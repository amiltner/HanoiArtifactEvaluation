open Core

module T = struct
  include Map.Make(Id)
  include Provide_bin_io(Id)
  include Provide_hash(Id)
end

include T

module Exprs = struct
  type key = T.Key.t
  type value = Type.t

  type t = Type.t T.t
  [@@deriving bin_io, eq, hash, ord, sexp]
end

module Types = struct
  type key = T.Key.t
  type value = Type.t

  type t = Type.t T.t
  [@@deriving bin_io, eq, hash, ord, sexp]
end

module Variants = struct
  type key = T.Key.t
  type value = (Id.t * Type.t) list

  type t = (Id.t * Type.t) list T.t
  [@@deriving bin_io, eq, hash, ord, sexp]
end

let get_foldable_t (tc:Types.t) (fold_completion:Type.t) : Type.t =
  let rec type_to_folded_type_internal
      (i:Id.t)
      (t:Type.t)
    : Type.t =
    begin match t with
      | Named i' ->
        if Id.equal i i' then
          fold_completion
        else
          t
      | Tuple ts ->
        Tuple (List.map ~f:(type_to_folded_type_internal i) ts)
      | Variant branches ->
        Variant
          (List.map
             ~f:(fun (b,t) ->
                 (Id.mk_prime b
                 ,type_to_folded_type_internal i t))
             branches)
      | Arrow _ | Mu _ -> t
    end
  in
  let t = find_exn tc "t" in
  let tv = Type.destruct_id_exn t in
  let t = find_exn tc tv in
  let ito = Type.destruct_mu t in
  begin match ito with
    | None -> t
    | Some (i,t) ->
      type_to_folded_type_internal i t
  end

let convert_foldable_to_full (tc : Types.t)
                             (fold_completion : Type.t)
                             : Expr.t =
    let convert_internal_id = "convert'" in
    let convert_internal_exp = Expr.mk_var convert_internal_id in
    let rec convert_foldable_internal
        (i:Id.t)
        (t:Type.t)
        (incoming_exp:Expr.t)
      : Expr.t =
      begin match t with
        | Named i' ->
          if Id.equal i i' then
            Expr.mk_app
              convert_internal_exp
              incoming_exp
          else
            incoming_exp
        | Tuple ts ->
          Expr.mk_tuple
            (List.mapi
               ~f:(fun num t ->
                   convert_foldable_internal
                     i
                     t
                     (Expr.mk_proj num incoming_exp))
               ts)
        | Variant branches ->
          Expr.mk_match
            incoming_exp
            "x"
            (List.map
               ~f:(fun (b,t) ->
                   (b,Expr.mk_ctor
                      (Id.mk_prime b)
                      (convert_foldable_internal
                         i
                         t
                         (Expr.mk_var "x"))))
               branches)
        | Mu _
        | Arrow _ ->
          incoming_exp
      end
    in
    let t = find_exn tc "t" in
    let tv = Type.destruct_id_exn t in
    let t = find_exn tc tv in
    let ito = Type.destruct_mu t in
    let t' = Type.mk_named (Id.mk_prime "t")
     in match ito with
        | None ->
          Expr.mk_func
            ("x",Type.mk_arrow t' t')
            (Expr.mk_var "x")
        | Some (i,t_internal) ->
          Expr.mk_func
            ("f",Type.mk_arrow
              t'
              fold_completion)
            (Expr.mk_fix
              convert_internal_id
              (Type.mk_arrow (Type._t) fold_completion)
              (Expr.mk_func
                  ("x" , Type._t)
                  (Expr.mk_app
                    (Expr.mk_var "f")
                    (convert_foldable_internal
                        i
                        t_internal
                        (Expr.mk_var "x")))))

open Myth_folds.Lang

let convert_foldable_and_res_to_folded_myth
    (tc:Types.t)
  : (exp -> (exp list)) * (exp -> (exp list) -> exp) =
  let rec foldable_and_res_to_folded
      (i:Id.t)
      (t:Type.t)
    : (exp -> (exp list)) * (exp -> (exp list) -> (exp * exp list)) =
    begin match t with
      | Named i' ->
        if Id.equal i i' then
          let exp_extract = (fun i -> [i]) in
          let exp_replace =
            (fun _ vs ->
               begin match vs with
                 | [] -> failwith "bad"
                 | h::t -> (h,t)
               end)
          in
          (exp_extract, exp_replace)
        else
          foldable_and_res_to_folded i (find_exn tc i')
      | Tuple ts ->
        if List.length ts = 0 then
          (* must special case for unit because of myth *)
          ((fun _ -> []), (fun _ vs -> (create_exp (EUnit), vs)))
        else
        let (sub_extracts,sub_replaces) =
          List.unzip
            (List.map ~f:(foldable_and_res_to_folded i) ts)
        in
        let exp_extract =
          fun (v:exp) ->
            begin match v.node with
              | ETuple vs ->
                let extracts_exps = List.zip_exn sub_extracts vs in
                List.concat_map
                  ~f:(fun (e,v) -> e v)
                  extracts_exps
              | _ ->
                failwith "bad exp"
            end
        in
        let exp_replace =
          fun (v:exp) ->
            begin match v.node with
              | ETuple vs ->
                let replacers =
                  List.map2_exn
                    ~f:(fun replacer v -> replacer v)
                    sub_replaces
                    vs
                in
                fun replaces ->
                  let (vs,replaces) =
                    List.fold
                      ~f:(fun (vs,replaces) replacer ->
                          let (v,replaces) = replacer replaces in
                          (v::vs,replaces))
                      ~init:([],replaces)
                      replacers
                  in
                  (create_exp (ETuple (List.rev vs)), replaces)
              | _ ->
                failwith "bad exp"
            end
        in
        (exp_extract, exp_replace)
      | Variant branches ->
        let (bs_sub_extracts,bs_sub_replaces) =
          List.unzip
            (List.map
               ~f:(fun (bn,bt) ->
                   let (sub_extract,sub_replace) = foldable_and_res_to_folded i bt in
                   ((bn, sub_extract), (bn, sub_replace)))
               branches)
        in
        let exp_extract =
          fun (v:exp) ->
            begin match v.node with
              | ECtor(i,v) ->
                let sub_extract = List.Assoc.find_exn ~equal:String.equal bs_sub_extracts i in
                sub_extract v
              | _ ->
                failwith "bad exp"
            end
        in
        let exp_replace =
          fun (v:exp) ->
            begin match v.node with
              | ECtor(i,v) ->
                let sub_replace = List.Assoc.find_exn ~equal:String.equal bs_sub_replaces i in
                fun replaces ->
                  let (e',replaces) = sub_replace v replaces in
                  (create_exp (ECtor(Id.mk_prime i,e')), replaces)
              | _ ->
                failwith "bad exp"
            end
        in
        (exp_extract, exp_replace)
      | Arrow _ | Mu _ -> ((fun _ -> []), fun v replaces -> (v,replaces))
    end
  in
  let t = find_exn tc "t" in
  let tv = Type.destruct_id_exn t in
  let t = find_exn tc tv in
  let ito = Type.destruct_mu t in
  begin match ito with
    | None -> ((fun _ -> []), (fun v _ -> v))
    | Some (i,t) ->
      let (exp_extract,exp_replace) = foldable_and_res_to_folded i t in
      let exp_replace =
        fun v ->
          let replacer = exp_replace v in
          fun rs ->
            fst (replacer rs)
      in
      (exp_extract, exp_replace)
  end
