open Core

open Typecheck

type t_unprocessed = Declaration.t list
                   * Module.Implementation.t
                   * Module.Specification.t
                   * UniversalFormula.t
                   * Type.t option
[@@deriving bin_io, eq, hash, ord, sexp]

type t = {
  module_type  : Type.t                 ;
  ec           : Context.Exprs.t        ;
  tc           : Context.Types.t        ;
  vc           : Context.Variants.t     ;
  mod_vals     : (Expr.t * Type.t) list ;
  post         : UniversalFormula.t     ;
  eval_context : (Id.t * Expr.t) list   ;
  unprocessed  : t_unprocessed          ;
  accumulator  : Type.t option          ;
}
[@@deriving bin_io, eq, hash, make, ord, sexp]

let extract_variants
    (t:Type.t)
    : (Context.Variants.key * Context.Variants.value) list =
  fst (Type.fold
         ~name_f:(fun i -> ([],Type.mk_named i))
         ~arr_f:(fun (vs1,t1) (vs2,t2) -> (vs1@vs2,Type.mk_arrow t1 t2))
         ~tuple_f:(fun vss_ts ->
                     let (vss,ts) = List.unzip vss_ts in
                     (List.concat vss, Type.mk_tuple ts))
        ~mu_f:(fun _ vs -> vs)
        ~variant_f:(fun ids_vss_ts ->
                      let (ids,vss_ts) = List.unzip ids_vss_ts in
                      let (vss,ts) = List.unzip vss_ts in
                      let ids_ts = List.zip_exn ids ts in
                      let ids_map = List.map ~f:(fun id -> (id,ids_ts)) ids in
                      (ids_map@(List.concat vss), Type.mk_variant ids_ts))
        t)

let process_decl_list
    (ec:Context.Exprs.t)
    (tc:Context.Types.t)
    (vc:Context.Variants.t)
    (ds:Declaration.t list)
  : (Context.Exprs.t * Context.Types.t * Context.Variants.t * (Id.t * Expr.t) list) =
  fst
    (List.fold_left
       ~f:(fun ((new_ec,new_tc,new_vc,i_e),(ec,tc,vc)) decl ->
           Declaration.fold
             ~type_f:(fun i t ->
                 let all_variants = extract_variants t in
                 ((new_ec
                  ,Context.set new_tc ~key:i ~data:t
                  ,List.fold_left
                      ~f:(fun vc (k,v) -> Context.set vc ~key:k ~data:v)
                      ~init:new_vc
                      all_variants
                  ,i_e)
                 ,(ec
                  ,Context.set tc ~key:i ~data:t
                  ,List.fold_left
                      ~f:(fun vc (k,v) -> Context.set vc ~key:k ~data:v)
                      ~init:vc
                      all_variants))
               )
             ~expr_f:(fun i e ->
                 let t = typecheck_exp ec tc vc e in
                 ((Context.set new_ec ~key:i ~data:t
                  ,new_tc
                  ,new_vc
                  ,(i,e)::i_e)
                 ,(Context.set ec ~key:i ~data:t
                  ,tc
                  ,vc))
               )
             decl)
       ~init:(((Context.empty,Context.empty,Context.empty,[])
              ,(ec,tc,vc)))
       ds)

let process_module_sig
    (ec:Context.Exprs.t)
    ((_,ets):Module.Specification.t)
  : Context.Exprs.t =
  List.fold_left
    ~f:(fun ec (i,t) -> Context.set ec ~key:i ~data:t)
    ~init:ec
    ets

let validate
    (full_tc:Context.Types.t)
    (ec:Context.Exprs.t)
    (tc:Context.Types.t)
    ((i,es):Module.Specification.t)
  : bool =
  List.fold_left
    ~f:(fun acc (i,t) ->
            if not acc then
              acc
            else
              begin match Context.find ec i with
                | None -> false
                | Some t' -> Typecheck.type_equiv full_tc t t'
              end)
    ~init:(Option.is_some (Context.find tc i))
    es

let process (unprocessed : t_unprocessed) : t =
  let (decs,modi,mods,uf,accumulator) = unprocessed in
  let (ec,tc,vc,i_e) =
    process_decl_list
      Context.empty
      Context.empty
      Context.empty
      decs
  in
  let m_ec,m_tc,m_vc,i_e' = process_decl_list ec tc vc modi in
  let i_e = i_e'@i_e in
  let full_tc =
    Map.merge_skewed tc m_tc ~combine:(fun ~key:_ v1 _ -> v1)
  in
  let satisfies = validate full_tc m_ec m_tc mods in
  if not satisfies then
    failwith "module doesn't satisfy spec"
  else
    let module_vals =
      List.map
        ~f:(fun (i,t) ->
            (List.Assoc.find_exn ~equal:Id.equal i_e i, t))
        (snd mods)
    in
    let ec_sig = process_module_sig ec mods in
    let _ = typecheck_formula ec_sig tc vc uf in
    let full_ec = Map.merge_skewed ec m_ec ~combine:(fun ~key:_ v1 _ -> v1) in
    let full_tc = Map.merge_skewed tc m_tc ~combine:(fun ~key:_ v1 _ -> v1) in
    let full_vc = Map.merge_skewed vc m_vc ~combine:(fun ~key:_ v1 _ -> v1) in
    let type_instantiation = Context.find_exn full_tc (fst mods) in
    let eval_context =
      (List.concat_map
         ~f:(fun cts ->
             List.map
               ~f:(fun (c,t) -> (c, Expr.mk_func ("i",t) (Expr.Ctor (c, Expr.mk_var "i"))))
               cts)
         (Context.data full_vc))
      @ i_e
    in
    let partial_problem = make ~module_type:type_instantiation
                               ~ec:full_ec
                               ~tc:full_tc
                               ~vc:full_vc
                               ~mod_vals:module_vals
                               ~post:uf
                               ~eval_context
                               ~unprocessed
     in match accumulator with
        | None -> partial_problem ()
        | Some acc -> partial_problem ~accumulator:acc ()
