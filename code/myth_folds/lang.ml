open Core
open Printf
open My_hash_cons

(**** Language {{{ *****)

type id = string
[@@deriving eq, hash, ord, show]

type label = string
[@@deriving eq, hash, ord, show]

type 'a record = (label * 'a) list
[@@deriving eq, hash, ord, show]

type typ =
  | TBase of id
  | TArr  of typ * typ
  | TTuple of typ list (* Invariant: List must always have two members. *)
  | TRcd of typ record
  | TUnit
[@@deriving eq, hash, ord, show]

module MType =
struct
  type t = typ
  [@@deriving eq, hash, ord, show]
end

let get_base_exn (t:typ)
  : string =
  begin match t with
    | TBase i -> i
    | _ -> failwith "bad base"
  end

type ctor = id * typ
[@@deriving eq, hash, ord, show]

module Ctor = struct
  type t = ctor
  [@@deriving eq, hash, ord, show]
end

let hash_fold_ref =
  fun _ _ _ -> failwith "ah"

type pattern =
  | PWildcard
  | PVar of id
  | PTuple of pattern list
  | PRcd of pattern record
[@@deriving eq, hash, ord, show]

type pat = id * (pattern option)   (* (id of constructor, pattern). *)
[@@deriving eq, hash, ord, show]

type arg = id * typ
[@@deriving eq, hash, ord, show]

type exp = e_node hash_consed
and e_node =
  | EVar of id
  | EApp of exp * exp
  | EFun of arg * exp
  | ELet of id * bool * arg list * typ * exp * exp
  | ECtor of id * exp
  | EMatch of exp * branch list
  | EPFun of (exp * exp) list
  | EFix of id * arg * typ * exp
  | ETuple of exp list  (* Invariant: List must always have two members. *)
  | EProj of int * exp  (* int is the index of projection of the tuple (1-indexed). *)
  | ERcd of exp record
  | ERcdProj of (label * exp)
  | EUnit

and branch = pat * exp
[@@deriving hash, ord, show]

let exp_table = HashConsTable.create 1000000
let hashcons_exp = HashConsTable.hashcons hash_e_node compare_e_node exp_table
let create_exp enode = hashcons_exp enode

type decl =
  | DData of id * ctor list
  | DLet  of id * bool * arg list * typ * exp

type value =
  v_label hash_consed
and v_label =
  {
    node : v_node ;
    mutable exp_form : (exp option) [@hash.ignore] ;
  }
and v_node =
  | VCtor  of id * value
  | VFun   of id * exp * env
  | VFix   of id * id * exp * env
  | VPFun  of (value * value) list
  | VTuple of value list (* Invariant: List must always have two members. *)
  | VRcd of value record
  | VUnit

and env = (id * value) list
[@@deriving hash, show]

let rec compare_value
    (v1:value)
    (v2:value)
  : int =
  compare_hash_consed
    compare_v_label
    v1
    v2
and compare_v_label
    (l1:v_label)
    (l2:v_label)
  : int =
  compare_v_node
    l1.node
    l2.node
and compare_v_node
    (v1:v_node)
    (v2:v_node)
  : int =
  begin match (v1,v2) with
    | (VCtor (i1,v1), VCtor (i2,v2)) ->
      Util.pair_compare String.compare compare_value (i1,v1) (i2,v2)
    | (VCtor _, _) -> -1
    | (_, VCtor _) -> 1
    | (VFun (i1,e1,env1), VFun (i2,e2,env2)) ->
      Util.triple_compare
        String.compare
        compare_exp
        compare_env
        (i1,e1,env1)
        (i2,e2,env2)
    | (VFun _, _) -> -1
    | (_, VFun _) -> 1
    | (VFix (i11,i12,e1,env1), VFix (i21,i22,e2,env2)) ->
      Util.quad_compare
        String.compare
        String.compare
        compare_exp
        compare_env
        (i11,i12,e1,env1)
        (i21,i22,e2,env2)
    | (VFix _, _) -> -1
    | (_, VFix _) -> 1
    | (VTuple vs1, VTuple vs2) ->
      List.compare
        compare_value
        vs1
        vs2
    | (VTuple _, _) -> -1
    | (_, VTuple _) -> 1
    | (VUnit, VUnit) -> 0
    | _ -> failwith "shouldnt"
  end
and compare_env (env1:env) (env2:env) =
  List.compare
    (Util.pair_compare String.compare compare_value)
    env1
    env2

let node (v:value) = v.node.node

let rec value_to_exp (v:value) =
  begin match v.node.exp_form with
    | Some e -> e
    | None ->
      let ans =
        begin match (node v) with
          | VCtor(i,v) -> create_exp (ECtor (i,value_to_exp v))
          | VTuple vs -> create_exp (ETuple (List.map ~f:value_to_exp vs))
          | VUnit -> create_exp (EUnit)
          | VFun _
          | VFix _
          | VRcd _
          | VPFun _ -> failwith "shouldnt happen"
        end
      in
      v.node.exp_form <- Some ans;
      ans
  end

let rec compare_v_node
 (v1:v_node) (v2:v_node) : int =
  begin match (v1,v2) with
    | (VCtor (i1,v1), VCtor (i2,v2)) ->
      Util.pair_compare String.compare compare_val (i1,v1) (i2,v2)
    | (VCtor _, _) -> -1
    | (_, VCtor _) -> 1
    | (VFun (i1,e1,env1), VFun (i2,e2,env2)) ->
      Util.triple_compare String.compare compare_exp compare_env (i1,e1,env1) (i2,e2,env2)
    | (VFun _, _) -> -1
    | (_, VFun _) -> 1
    | (VFix (i11,i12,e1,env1), VFix (i21,i22,e2,env2)) ->
      Util.quad_compare String.compare String.compare compare_exp compare_env (i11,i12,e1,env1) (i21,i22,e2,env2)
    | (VFix _, _) -> -1
    | (_, VFix _) -> 1
    | (VPFun _, VPFun _) -> failwith "no happen"
    | (VPFun _, _) -> failwith "no happen"
    | (_, VPFun _) -> failwith "no happen"
    | (VTuple vs1, VTuple vs2) ->
      List.compare
        compare_val
        vs1
        vs2
    | (VTuple _, _) -> -1
    | (_, VTuple _) -> 1
    | (VRcd _, VRcd _) -> failwith "no happen"
    | (VRcd _, _) -> failwith "no happen"
    | (_, VRcd _) -> failwith "no happen"
    | (VUnit,VUnit) -> 0
  end
and compare_val (v1:value) (v2:value) : int =
  Int.compare v1.tag v2.tag
and compare_env (env1:env) (env2:env) : int =
  List.compare
    (Util.pair_compare String.compare compare_val)
    env1
    env2

(*let rec compare_val (v1:value) (v2:value) : int =
  begin match (v1,v2) with
    | (VCtor (i1,v1), VCtor (i2,v2)) ->
      Util.pair_compare String.compare compare_val (i1,v1) (i2,v2)
    | (VCtor _, _) -> -1
    | (_, VCtor _) -> 1
    | (VFun (i1,e1,envr1), VFun (i2,e2,envr2)) ->
      let env1 = !envr1 in
      let env2 = !envr2 in
      envr1 := [];
      envr2 := [];
      let ans = Util.triple_compare String.compare compare_exp compare_env (i1,e1,env1) (i2,e2,env2) in
      envr1 := env1;
      envr2 := env2;
      ans
    | (VFun _, _) -> -1
    | (_, VFun _) -> 1
    | (VPFun _, VPFun _) -> failwith "no happen"
    | (VPFun _, _) -> failwith "no happen"
    | (_, VPFun _) -> failwith "no happen"
    | (VTuple vs1, VTuple vs2) ->
      List.compare
        compare_val
        vs1
        vs2
    | (VTuple _, _) -> -1
    | (_, VTuple _) -> 1
    | (VRcd _, VRcd _) -> failwith "no happen"
    | (VRcd _, _) -> failwith "no happen"
    | (_, VRcd _) -> failwith "no happen"
    | (VUnit,VUnit) -> 0
  end
and compare_env
    (env1:env)
    (env2:env)
  : int =
  List.compare
    (Util.pair_compare String.compare compare_val)
    env1
    env2*)

(*let rec hash_v_node = function
  | VCtor (i,v)  -> abs ((String.hash i) + 79 * (hash_value v) + 73)
  | VFun (i,e,env) ->
    abs ((String.hash i) + 79 * (hash_exp e) + 79 * (hash_env env) + 73)
  | VFix (i1,i2,e,env) ->
    abs (79 * (String.hash i1) + 79 * (String.hash i2) + 79 * (hash_exp e) + 79 * (hash_env env) + 73)
  | VPFun _ -> failwith "cannot"
  | VTuple vs -> List.fold_left
                   ~f:(fun acc v ->
                       acc + 79 * (hash_value v) + 73 )
                   ~init:73
                   vs
  | VRcd _ -> failwith "cannot"
  | VUnit -> 1

and hash_env env =
  List.fold_left
    ~f:(fun acc (i,v) ->
        acc + 79 * (String.hash i) + 79 * (hash_value v) + 73 )
    ~init:73
    env

  and hash_value v = v.hkey*)

let value_table = HashConsTable.create 10000
let hashcons_value = HashConsTable.hashcons hash_v_label compare_v_label value_table
let create_value vnode = hashcons_value ({ node = vnode; exp_form = None })
let vctor i v = create_value (VCtor (i,v))
let vfun i e env = create_value (VFun (i,e,env))
let vfix f i e env = create_value (VFix (f,i,e,env))
let vtuple vs = create_value (VTuple vs)
let vunit = create_value VUnit

let compare_exp (e1:exp) (e2:exp) : int =
  compare_exp e1 e2

type synth_problem = id * typ * exp list

type prog = decl list * synth_problem

exception Internal_error of string
let internal_error f s = raise @@ Internal_error (sprintf "(%s) %s" f s)

let rec hash_typ = function
  | TUnit   -> 1
  | TBase x -> String.hash x
  | TArr (t1, t2) -> abs ((hash_typ t1) + 79 * (hash_typ t2) + 73)
  | TTuple ts -> List.fold_left
      ~f:(fun acc ty -> acc + 79 * (hash_typ ty) + 73)
      ~init:73
      ts
  | TRcd ts -> List.fold_left
      ~f:(fun acc (lbl,ty) ->
            acc + 79 * (String.hash lbl) + 79 * (hash_typ ty) + 73 )
      ~init:73
      ts

(*let rec hash_value = function
  | VCtor (i,v)  -> abs ((String.hash i) + 79 * (hash_value v) + 73)
  | VFun (i,e,envr) ->
    let env = !envr in
    envr := [];
    let ans = abs ((String.hash i) + 79 * (hash_exp e) + 79 * (hash_env env) + 73) in
    envr := env;
    ans
  | VPFun _ -> failwith "cannot"
  | VTuple vs -> List.fold_left
                   ~f:(fun acc v ->
                       acc + 79 * (hash_value v) + 73 )
                   ~init:73
                   vs
  | VRcd _ -> failwith "cannot"
  | VUnit -> 1

and hash_env env =
  List.fold_left
    ~f:(fun acc (i,v) ->
        acc + 79 * (String.hash i) + 79 * (hash_value v) + 73 )
    ~init:73
    env*)

(*let hash_fold_value s v = Hash.fold_int s (hash_value v)*)

let rec types_to_arr (ts:typ list) =
  match ts with
  | []  -> internal_error "types_to_arr" "empty type list provided"
  | [t] -> t
  | t :: ts -> TArr (t, types_to_arr ts)

let rec free_vars (e:exp) : id list =
  match e.node with
  | EVar x -> [x]
  | EApp (e1, e2) -> free_vars e1 @ free_vars e2
  | EFun (_, e) -> free_vars e
  | ELet (_, _, _, _, e1, e2) -> free_vars e1 @ free_vars e2
  | ECtor (_, e) -> free_vars e
  | ETuple es -> List.map ~f:free_vars es |> List.concat
  | EProj (_, e) -> free_vars e
  | ERcd es -> List.map ~f:(fun (_,e) -> free_vars e) es |> List.concat
  | ERcdProj (_, e) -> free_vars e
  | EMatch (e, bs) ->
    List.map ~f:(fun (_, e) -> free_vars e) bs
      |> List.concat
      |> (@) (free_vars e)
  | EPFun ios ->
    List.fold_left
      ~f:(fun acc (e1, e2) -> acc @ free_vars e1 @ free_vars e2)
      ~init:[] ios
  | EFix (_, _, _, e) -> free_vars e
  | EUnit -> []

let rec size (e:exp) : int =
  match e.node with
  | EVar _ -> 1
  | EApp (e1, e2) -> 1 + size e1 + size e2
  | EFun (_, e) -> 1 + size e
  | ELet (_, _, _, _, e1, e2) -> 1 + size e1 + size e2
  | ECtor (_, e) -> 1 + size e
  | ETuple es -> 1 + List.fold_left ~f:(fun n e -> n + size e) ~init:0 es
  | EProj (_, e) -> 1 + size e
  | ERcd es -> 1 + List.fold_left ~f:(fun n (_,e) -> n + size e) ~init:0 es
  | ERcdProj (_, e) -> 1 + size e
  | EMatch (e, bs) ->
      1 + size e + List.fold_left ~f:(fun n (_, e) -> n + size e) ~init:0 bs
  | EPFun ios -> 1 +
      List.fold_left ~f:(fun n (e1, e2) -> n + size e1 + size e2) ~init:0 ios
  | EFix (_, _, _, e) -> 1 + size e
  | EUnit -> 1

let rec examples_count (v:value) : int =
  match (node v) with
  | VPFun ios ->
      List.fold_left ~f:(fun n (_, v) -> n + examples_count v) ~init:0 ios
  | _ -> 1

let rec extract_ids_from_pattern = function
  | PWildcard -> []
  | PVar x    -> [x]
  | PTuple ps -> List.concat_map ~f:extract_ids_from_pattern ps
  | PRcd ps   -> List.concat_map ~f:(fun (_,p) -> extract_ids_from_pattern p) ps

let gen_var_base (t:typ) : id =
  match t with
  | TArr (_, _) -> "f"
  | TBase dt    -> dt.[0] |> Char.lowercase |> String.make 1
  | TTuple _    -> "t"
  | TRcd _      -> "r"
  | TUnit       -> "u"

let rec contains
    (e1:exp)
    (e2:exp)
  : bool =
  let contains_rec = fun e -> contains e e2 in
  if e1 = e2 then
    true
  else
    begin match e1.node with
      | EApp (e1,e2) -> contains_rec e1 || contains_rec e2
      | EFun (_,e) -> contains_rec e
      | ELet (_,_,_,_,e1,e2) -> contains_rec e1 || contains_rec e2
      | ECtor (_,e) -> contains_rec e
      | EMatch (e,bs) ->
        contains_rec e ||
        List.exists
          ~f:(fun (_,e) -> contains_rec e)
          bs
      | EPFun eps ->
        List.exists
          ~f:(fun (e1,e2) -> contains_rec e1 || contains_rec e2)
          eps
      | EFix (_,_,_,e) -> contains_rec e
      | ETuple es ->
        List.exists
          ~f:contains_rec
          es
      | EProj (_,e) -> contains_rec e
      | ERcd rs ->
        List.exists
          ~f:(fun (_,e) -> contains_rec e)
          rs
      | ERcdProj (_,e) -> contains_rec e
      | EUnit
      | EVar _ -> false
    end

let rec app_capital_to_ctor
    (e:exp)
  : exp =
  begin match e.node with
    | EVar _ -> e
    | EApp (e1,e2) ->
      begin match e1.node with
        | EVar x ->
          let e2 = app_capital_to_ctor e2 in
          if Char.is_uppercase (String.nget x 0) then
            create_exp (ECtor (x,e2))
          else
            e
        | _ ->
          create_exp (EApp (app_capital_to_ctor e1, app_capital_to_ctor e2))
      end
    | EFun (a,e) ->
      create_exp (EFun (a,app_capital_to_ctor e))
    | ELet (i,b,ags,t,e1,e2) ->
      create_exp (ELet (i,b,ags,t,app_capital_to_ctor e1, app_capital_to_ctor e2))
    | ECtor (i,e) -> create_exp (ECtor (i, app_capital_to_ctor e))
    | EMatch (e,bs) -> let e = app_capital_to_ctor e in
      create_exp (EMatch (e,
              List.map
                ~f:(fun (p,e) -> (p,app_capital_to_ctor e))
                bs))
    | EFix (i,a,t,e) -> create_exp (EFix (i,a,t,app_capital_to_ctor e))
    | ETuple es -> create_exp (ETuple (List.map ~f:app_capital_to_ctor es))
    | EProj (i,e) -> create_exp (EProj (i,app_capital_to_ctor e))
    | EUnit -> create_exp EUnit
    | _ -> failwith "shouldnt"
  end

(***** }}} *****)
