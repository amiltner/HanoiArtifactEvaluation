(*******************************************************************************
 * eval.ml - environment-based evaluator
 ******************************************************************************)

open Core
open Consts
open Lang
open Printf

exception Eval_error of string
exception Extr_error of value
let raise_eval_error s = raise (Eval_error s)

(***** Helpers {{{ *****)

let rec find_first_branch (c:id) (bs:branch list) : branch =
  match bs with
  | [] -> raise_eval_error ("Constructor not found during matching: " ^ c)
  | ((c', x), e)::bs -> if c = c' then ((c', x), e) else find_first_branch c bs

let rec extract_values_from_pattern (v:value) (p:pattern) : (id * value) list =
  match (p, (node v)) with
  | (PWildcard, _) -> []
  | (PVar x,    _) -> [(x, v)]
  | (PTuple ps, VTuple vs) ->
    if List.length ps <> List.length vs then
      raise (Extr_error v)
    else
      List.concat_map ~f:(fun (v, p) -> extract_values_from_pattern v p) (List.zip_exn vs ps)
  | (PRcd ps, VRcd vs) ->
    begin try List.concat_map ~f:(fun (p, v) -> extract_values_from_pattern v p) (Util.zip_without_keys ps vs)
    with Invalid_argument _ ->
      raise (Extr_error v)
  end
  | (_, _) -> 
    raise (Extr_error v)

(***** }}} *****)

(***** Evaluation Cache {{{ *****)

module GTS : sig
  type t = { env : env; e : exp }
  val make_key : env -> exp -> t
  include Hashable.S with type t := t
end = struct
  module T = struct
    type t = { env : env; e : exp }
    let make_key (env:env) (e:exp) = { env = env; e = e }
    let hash k = hash_env k.env + 79 * hash_exp k.e + 73
    let hash_fold_t s k = Hash.fold_int s (hash k)
    let compare x y =
      let exp_compare = compare_exp x.e y.e in
      if exp_compare = 0 then
        let env_compare = compare_env x.env y.env in
        env_compare
      else
        exp_compare
    let sexp_of_t (_:t) : Sexp.t = failwith "GTS.sexp_of_t unimplemented"
    let t_of_sexp (_:Sexp.t) : t = failwith "GTS.t_of_sexp unimplemented"
  end
  include T
  include Hashable.Make(T)
end

module GTSCache = struct
  module GTS : sig
    type t = { env : env; e : exp }
    val make_key : env -> exp -> t
    include Hashable.S with type t := t
  end = struct
    module T = struct
      type t = { env : env; e : exp }
      let make_key (env:env) (e:exp) = { env = env; e = e }
      let hash k = hash_env k.env + 79 * hash_exp k.e + 73
      let hash_fold_t s k = Hash.fold_int s (hash k)
      let compare x y =
        let exp_compare = compare_exp x.e y.e in
        if exp_compare = 0 then
          let env_compare = compare_env x.env y.env in
          env_compare
        else
          exp_compare
      let sexp_of_t (_:t) : Sexp.t = failwith "GTS.sexp_of_t unimplemented"
      let t_of_sexp (_:Sexp.t) : t = failwith "GTS.t_of_sexp unimplemented"
    end
    include T
    include Hashable.Make(T)
  end

  include Lrucache.Make(GTS)
  let make_key (env:env) (e:exp) : GTS.t = { env = env; e = e }
end

let lookup_tables : bool ref = ref true ;;
let memo_eval_tbl : (GTS.t, value) Hashtbl.t =
  GTS.Table.create ()
let lrucache : value GTSCache.t =
  if !eval_lookup_tables then
    GTSCache.init ~size:8388608 (GTSCache.make_key ([]) (create_exp EUnit))
  else
    GTSCache.init ~size:1 (GTSCache.make_key ([]) (create_exp EUnit))

let find_in_table tbl key =
  Hashtbl.find tbl key

(***** }}} *****)

let insert_env
    (e:env)
    (i:id)
    (v:value)
  : env =
  (i,v)::e
  (*begin match e with
    | [] -> [(i,v)]
    | h::t ->
      let (i',_) = h in
      let c = String.compare i i' in
      if c > 0 then
        h::(insert_env t i v)
      else if c = 0 then
        (i,v)::t
      else
        (i,v)::e
    end*)

let insert_all
    (e:env)
    (ivs:(string * value) list)
  : env =
  ivs@e
  (*List.fold
    ~f:(fun env (i,v) -> insert_env env i v)
    ~init:e
    ivs*)

let lookup_env
    (e:env)
    (i:id)
  : value =
  (*let rec lookup_env_internal e i =
    if not (List.is_sorted ~compare:(fun (i1,_) (i2,_) -> String.compare i1 i2) e) then failwith (Pp.pp_env e);
    begin match e with
      | [] -> failwith i
      | (i',v)::t ->
        let c = String.compare i i' in
        if c < 0 then
          failwith (Pp.pp_env (e))
        else if c = 0 then
          v
        else
          lookup_env_internal t i
    end
  in
    lookup_env_internal e i*)
  List.Assoc.find_exn ~equal:(String.equal) e i

(* Evaluates e to a value under env *)
let rec eval (env:env) (e:exp) : value =
  let key = GTSCache.make_key env e in
  let calc = (fun (enve: GTSCache.key) ->
      let env = enve.env in
      let e = enve.e in
      (*match find_in_table memo_eval_tbl key with
        | Some ans -> ans
        | None ->*)
      let ans = begin match e.node with
        | EVar x -> lookup_env env x
        | EApp (e1, e2) ->
          let (v1, v2) = (eval env e1, eval env e2) in
          begin match (node v1) with
            | VFun (x, e, closure) ->
              let closure = insert_env closure x v2 in
              eval closure e
            | VFix (f, x, e, closure) ->
              eval
                (insert_env
                   (insert_env closure f v1)
                   x
                   v2)
                e
            | VPFun vps ->
              begin match Util.find_first (fun (v1, _) -> v1 = v2) vps with
                | Some (_, v) -> v
                | None ->
                  raise_eval_error @@ sprintf
                    "Non-matched value %s found with partial function:\n%s"
                    (Pp.pp_value v2) (Pp.pp_value v1)
              end
            | _ -> raise_eval_error ("Non-function value found in application" ^ (Pp.pp_value v1))
          end
        | EFun ((x, _), e) ->
          vfun x e env
        | ELet (f, is_rec, xs, t, e1, e2) ->
          let count = List.length xs in
          if count = 0 then
            (* Value binding *)
            let v1 = eval env e1 in
            eval (insert_env env f v1) e2
          else
            (* Function binding *)
            let rec binding_to_funs xs e =
              match xs with
              | []      -> e
              | x :: xs -> create_exp (EFun (x, binding_to_funs xs e))
            in
            let (x1, t1) = List.hd_exn xs in
            let fn = if is_rec then
                let e1 = binding_to_funs (List.tl_exn xs) e1 in
                create_exp (EFix ( f, (x1, t1)
                                 , (List.map ~f:snd (List.tl_exn xs)) @ [t] |> types_to_arr
                                 , e1 ))
              else
                binding_to_funs xs e1
            in
            eval (insert_env env f (eval env fn)) e2
        | ECtor (c, e)  -> vctor c (eval env e)
        | ETuple es     -> vtuple (List.map ~f:(eval env) es)
        | ERcd _       -> failwith "ah" (*(List.map ~f:(fun (l,e) -> (l,eval env e)) es)*)
        | EMatch (e, bs) ->
          let v = eval env e in
          begin match (node v) with
            | VCtor (c, v) ->
              let ((_, p_opt), e) = find_first_branch c bs in
              begin match p_opt with
                | None -> eval env e
                | Some p ->
                  eval
                    (List.fold_left
                       ~f:(fun env (label,value) ->
                           insert_env env label value)
                       ~init:env
                       (extract_values_from_pattern v p))
                    e
              end
            | _ ->
              raise_eval_error @@
              sprintf "Non-datatype value found in match: %s" (Pp.pp_exp e)
          end
        | EPFun _ ->
          (*VPFun (List.map ~f:(fun (e1, e2) -> (eval env e1, eval env e2)) ios)*) failwith "ah"
        | EFix (f, (x, _), _, e) ->
          let closure = env in
          let v = vfix f x e closure in
          v
        | EProj (n, e) ->
          begin match (node (eval env e)) with
            | VTuple vs -> List.nth_exn vs (n - 1)
            | _ -> raise_eval_error @@
              sprintf "Non-tuple value found in projection: %s" (Pp.pp_exp e)
          end
        | ERcdProj (l, e) ->
          let v = eval env e in
          begin match (node v) with
            | VRcd vs -> begin match Util.lookup l vs with
                | Some v' -> v'
                | None -> raise_eval_error @@
                  sprintf "Label '%s' not found in record: %s" l (Pp.pp_value v)
              end
            | _ -> raise_eval_error @@
              sprintf "Non-record value found in projection: %s" (Pp.pp_exp e)
          end
        | EUnit -> vunit
      end
      in
      (*Hashtbl.set memo_eval_tbl ~key ~data:ans; ans*)(ans))
  in
  if !eval_lookup_tables then
    GTSCache.get lrucache key calc
  else
    calc key

(* Generates the initial synthesis environment. *)
let gen_init_env (ds:decl list) : env =
  let process (env:env) = function
    | DData _ -> env
    | DLet (f, is_rec, xs, t, e) ->
        if List.length xs = 0 then
          (* Value binding *)
          let v = eval env e in
          insert_env env f v
        else
          (* Function binding *)
          let v = eval env (create_exp (ELet (f, is_rec, xs, t, e, create_exp (EVar f)))) in
          insert_env env f v
  in
  (List.fold_left ~f:process ~init:([]) ds)
