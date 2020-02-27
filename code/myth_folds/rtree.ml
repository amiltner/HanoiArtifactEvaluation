module MyRope = Rope
open Core
open Consts
open Printf
open Lang
open Sigma
open Gamma
module Rope = MyRope
open Util

(***** Type definitions {{{ *****)

(*module Output =
struct
  type t_node = ((value option) list option) list
  [@@deriving ord, show, hash]

  type t = t_node hash_consed

  let compare o1 o2 = Int.compare o1.tag o2.tag

  let table = HashConsTable.create 100000
  let hashcons = HashConsTable.hashcons hash_t_node compare_t_node table

  let create x = hashcons x
  end*)

(*type output = Output.t*)

(*type output = (value option option) list
  [@@deriving ord, show, hash]*)

(*type 'a test_output_retriever = exp * exp * ('a -> bool option) * ('a -> value option option)
type 'a test = 'a -> bool list

  type 'a tests_outputs = (('a test_output_retriever)) list*)

let desired_magic_num = 1000

type output = value option
[@@deriving ord, show, hash]

type test_output_result = bool * value option
[@@deriving ord, show, hash]

type test_output_result_lazy = test_output_result Lazy.t
[@@deriving ord, show, hash]

type test_output_result_list = test_output_result_lazy list
[@@deriving ord, show, hash]

type 'a test_output =
  (exp * exp * ('a -> value list -> test_output_result))

type 'a tests_outputs =
  'a test_output list

let tests_outputs_update
    (type a)
    (type b)
    (f:a -> b)
    (tests_outputs:b tests_outputs)
  : a tests_outputs =
  List.map
    ~f:(fun (e1,e2,otm) ->
        (e1,e2, otm % f))
    tests_outputs


let to_test_output_result_list
    (type a)
    (tests_outputs:a tests_outputs)
    (e:a)
    (priors:value list)
  : test_output_result_list =
  List.map
    ~f:(fun (_,_,v) -> lazy (v e priors))
    tests_outputs

let passing_test_output_result
    (res_lazy:test_output_result Lazy.t)
  : bool =
  fst (Lazy.force_val res_lazy)

(*let has_passing_capabilities
    (type a)
    (tests_outputs:a tests_outputs)
    (x:a)
    (priors:value list)
  : bool =
  List.for_all
    ~f:passing_test_output_result
    (to_test_output_result_list
       tests_outputs
       x
       priors)*)

(*let to_test_io_output_tree_list
    (type a)
    (tests_outputs:a tests_outputs)
    (e:a)
  : (exp * exp * test_output_result) list =
  List.map
    ~f:(fun (e1,e2,v) -> (e1,e2,v e))
    tests_outputs*)

let any_updated
    (test_output_trees:test_output_result_lazy list)
  : bool =
  let any_updated_tree
      (res:test_output_result Lazy.t)
    : bool =
    passing_test_output_result res
  in
  List.exists
    ~f:any_updated_tree
    test_output_trees

let core_deduper
    (type a)
    (compare:a -> a -> int)
    (to_size:a -> int)
    (xs:a list)
  : a list =
  let sized_xs =
    List.map
      ~f:(fun x -> (x,to_size x))
      xs
  in
  let sorted_parititioned_i =
    List.sort_and_partition_with_indices
      ~cmp:(fun (e1,_) (e2,_) -> compare e1 e2)
      sized_xs
  in
  List.map
    ~f:(fun esl ->
        let ordered_by_size =
          List.sort
            ~compare:(fun ((_,s1),_) ((_,s2),_) -> Int.compare s1 s2)
            esl
        in
        let ((a,_),_) = List.hd_exn ordered_by_size in
        a)
    sorted_parititioned_i

(*let minimize
    (type a)
    (to_size:a -> int)
    (es:a list)
    (tests_outputs:a tests_outputs)
  : a list =
  let es_exs_tests_outputs =
    List.map
      ~f:(fun e ->
          (e,to_test_output_result_list tests_outputs e))
      es
  in
  let productive_es_etc =
    List.filter
      ~f:(fun (_,o) -> any_updated o)
      es_exs_tests_outputs
  in
  let deduped_es =
    core_deduper
      (fun (_,o1) (_,o2) -> compare_test_output_result_list o1 o2)
      (fun (e,_) -> to_size e)
      productive_es_etc
  in
  List.map ~f:fst deduped_es*)

(*let tests_outputs_to_output_full_retriever
    (type a)
    (tests_outputs:a tests_outputs)
    (e:a)
  : output =
  List.map
    ~f:(fun (_,_,_,v) -> v e)
    tests_outputs

let tests_outputs_to_tests_full_retriever
    (type a)
    (tests_outputs:a tests_outputs)
    (e:a)
  : bool list =
  List.map
    ~f:(fun (_,_,t,_) ->
        begin match t e with
          | None -> false
          | Some b -> b
        end)
    tests_outputs*)

let output_comparer = List.compare (Option.compare Lang.compare_val)
let pp_output = List.to_string ~f:(Option.value_map ~f:Pp.pp_value ~default:"None")

type 'a tree = TNode of 'a * 'a tree list
[@@deriving ord, show, hash]

let node_paths_bfs
    (ts:'a tree list)
  : int list list =
  let rec node_paths_internal
      (to_process:('a tree * int list) list)
      (next_level:('a tree * int list) list)
    : int list list =
    begin match to_process with
      | [] ->
        if next_level = [] then
          []
        else
          node_paths_internal
            next_level
            []
      | h::t ->
        let (TNode(_,children),is) = h in
        let to_add = List.mapi ~f:(fun i c -> (c,i::is)) children in
        is::(node_paths_internal t (to_add@next_level))
    end
  in
  List.map
    ~f:List.rev
    (node_paths_internal
       (List.mapi
          ~f:(fun i t -> (t,[i]))
          ts)
       [])


type exptree = exp tree
[@@deriving ord, show, hash]

let rec tree_map
    (TNode(v,ts):'a tree)
    ~(f:'a -> 'b)
  : 'b tree =
  TNode(f v,tree_list_map ~f ts)

and tree_list_map
    (ts:'a tree list)
    ~(f:'a -> 'b)
  : 'b tree list =
  List.map
    ~f:(tree_map ~f)
    ts

let split_into_containing_tree
    ~(compare:'a -> 'a -> bool)
    (xs:'a list)
  : ('a tree) list =
  let rec merge_into_forest
      (current_clustering:'a tree list)
      (x:'a)
    : 'a tree list =
    let (children,current_clustering) =
      List.fold_left
        ~f:(fun (children,other_trees) other_tree ->
            let TNode(smallest,_) = other_tree in
            if compare smallest x then
              (other_tree::children,other_trees)
            else
              (children,other_tree::other_trees))
        ~init:([],[])
        current_clustering
    in
    if (List.is_empty children) then
      let (merged,trees) =
        List.fold
          ~f:(fun (merged,other_trees) tree ->
              if merged then
                (true,tree::other_trees)
              else
                let TNode(smallest,children) = tree in
                if compare x smallest then
                  let children = merge_into_forest children x in
                  let tree = TNode(smallest,children) in
                  (true,tree::other_trees)
                else
                  (false,tree::other_trees))
          ~init:(false,[])
          current_clustering
      in
      if merged then
        trees
      else
        TNode(x,[])::trees
    else
      (TNode(x,children))::current_clustering
  in
  List.fold
    ~f:merge_into_forest
    ~init:[]
    xs


let split_by_minimal
    (type a)
    ~(compare:a -> a -> bool)
    (xs:a list)
  : (a list) * (a list) =
  let rec split_by_minimal_internal
      (xs:a list)
      (smalls:a list)
      (others:a list)
    : (a list) * (a list) =
    begin match xs with
      | [] -> (smalls,others)
      | h::t ->
        let contains =
          List.exists
            ~f:(fun e -> compare h e)
            smalls
        in
        if contains then
          split_by_minimal_internal
            t
            smalls
            (h::others)
        else
          let (smalls,new_large) =
            List.partition_tf
              ~f:(fun s -> not (compare s h))
              smalls
          in
          split_by_minimal_internal
            t
            (h::smalls)
            (new_large@others)
    end
  in
  split_by_minimal_internal xs [] []

let split_into_minimal_partitions
    (type a)
    ~(compare:a -> a -> bool)
    ~(total_order:a -> a -> int)
    (xs:a list)
  : ((a list) * (a list)) list =
  let rec split_into_minimal_partitions_internal
      (remaining_bigs:a list)
      (most_recent_addition:a list)
      (partition_acc:((a list) * (a list)) list)
    : ((a list) * (a list)) list =
    if List.is_empty remaining_bigs then
      partition_acc
    else
      let (littles,bigs) = split_by_minimal ~compare remaining_bigs in
      let most_recent_addition = most_recent_addition @ littles in
      split_into_minimal_partitions_internal
        bigs
        most_recent_addition
        ((most_recent_addition,bigs)::partition_acc)
  in
  let partitions =
    split_into_minimal_partitions_internal
      xs
      []
      []
  in
  List.map
    ~f:(fun (p1,p2) -> (List.sort ~compare:total_order p1, p2))
    partitions

(*let deduper
    (type a)
    (tests_outputs:a tests_outputs)
    (to_size:a -> int)
    (xs:a list)
  : a list =
  let es_outputs =
    List.map
      ~f:(fun x -> (x, to_size x, (to_test_output_result_list tests_outputs x)))
      xs
  in
  let sorted_parititioned_i =
    List.sort_and_partition_with_indices
      ~cmp:(fun (_,_,e1) (_,_,e2) -> compare_test_output_result_list e1 e2)
      es_outputs
  in
  List.map
    ~f:(fun esl ->
        let ordered_by_size =
          List.sort
            ~compare:(fun ((_,s1,_),_) ((_,s2,_),_) -> Int.compare s1 s2)
            esl
        in
        let ((a,_,_),_) = List.hd_exn ordered_by_size in
        a)
    sorted_parititioned_i*)

let test_performance_to_ranking
    (tp:bool list)
  : Float.t =
  let success_count =
    List.length (List.filter ~f:ident tp)
  in
  let total_count = List.length tp in
  (Float.of_int success_count) /. (Float.of_int total_count)


(* output: partial program outputs *)

(* rtree: A single node of a refinement tree.                                             *)
type rtree =
  { t                 : typ               (* Goal type that we wish to generate.          *)
  ; mutable sz        : int               (* Size of the refinement tree.                 *)
  ; g                 : Gamma.t           (* Names that are in scope.                     *)
  ; mutable timed_out : bool              (* Whether the generation process has timed out.*)
  ; mutable es                : exp list          (* Expressions that have been generated so far. *)
  ; refinements       : rnode option        (* Generated using IRefine rules.               *)
  ; possible_match    : (rmatch option)  (* Generated using IRefine-match rule.      *)
  ; forced_match      : bool              (* Generated using IRefine-match rule.      *)
  ; matches_permitted : bool
  }

and rnode =
  | SAbs   of id * arg * typ * rtree      (* IRefine-Fix.                                 *)
  | SCtor  of id * rtree                  (* IRefine-Ctor.                                *)
  | STuple of rtree list                  (* IRefine-Tuple.                               *)
  | SRcd   of rtree record                (* IRefine-Record.                              *)
  | SUnit                                 (* IRefine-Unit.                                *)

and rmatch = exp *                        (* The match scrutinee.                         *)
            (pat * rtree) list            (* The branches of the match statement.         *)

(* rtree_size: Determines the size of an rtree, which is defined as the number of rtrees  *)
(*             contained in this and child trees.                                         *)

let rec duplicate_rtree
    (t:rtree)
  : rtree =
  {
    t = t.t;
    sz = t.sz;
    g = t.g;
    timed_out = t.timed_out;
    es = t.es;
    refinements = Option.map ~f:duplicate_rnode t.refinements;
    possible_match = Option.map ~f:duplicate_rmatch t.possible_match;
    forced_match = t.forced_match;
    matches_permitted = t.matches_permitted;
  }

and duplicate_rnode
    (n:rnode)
  : rnode =
  begin match n with
    | SAbs(i,a,t,rt) ->
      SAbs(i,a,t,duplicate_rtree rt)
    | SCtor(i,t) -> SCtor(i,duplicate_rtree t)
    | STuple ts -> STuple (List.map ~f:duplicate_rtree ts)
    | SRcd _ -> failwith "ignore"
    | SUnit -> SUnit
  end

and duplicate_rmatch
    ((e,bs):rmatch)
  : rmatch =
  (e, List.map ~f:(fun (p,t) -> (p,duplicate_rtree t)) bs)

let rec rtree_size (t:rtree) : int =
  let rnode_size n =
    match n with
    | SAbs (_, _, _, t) -> rtree_size t
    | SCtor (_, t)      -> rtree_size t
    | STuple ts -> List.fold_left ~f:(fun acc t -> rtree_size t + acc) ~init:0 ts
    | SRcd ts -> List.fold_left ~f:(fun acc (_,t) -> rtree_size t + acc) ~init:0 ts
    | SUnit -> 0
  in
  let match_size ((_, ls) : rmatch) =
      List.fold_left ~f:(fun acc t -> acc + rtree_size t) ~init:0 (List.map ~f:snd ls)
  in
  let matches_size = function
    | None    -> 0
    | Some ms -> match_size ms
  in
  let refinement_amount r =
    begin match r with
      | None -> 0
      | Some rnode -> rnode_size rnode
    end
  in
    matches_size t.possible_match + refinement_amount t.refinements

(***** }}} *****)

(***** Pretty printing {{{ *****)

type pretty_line = int * string

let print_whitespace (n:int) = (String.make (n + 1) '*') ^ "   "
let pretty_lines (lines:pretty_line list) : string list =
  List.map ~f:(fun (n, s) -> print_whitespace n ^ s) lines

let rec stringify (ss:string list) : string =
  match ss with
  | [] -> ""
  | [s] -> s
  | s :: ss -> s ^ "\n" ^ stringify ss

let stringify_rtree_matches (t:rtree) : string =
  match t.possible_match with
  | None    -> "growable"
  | Some _ -> sprintf "#/matches = %d" 1

let rec build_lines_rtree (k:int) (t:rtree) : pretty_line list =
  let childlines   =  match t.refinements with | None -> [] | Some r -> build_lines_rnode k t.t r in
  let matchlines   = build_lines_matches k t.t t.possible_match  in
  (k, sprintf "* :: %s [E-size = %d, timed_out = %b, exp_count = %d, %s]"
     (Pp.pp_typ t.t) t.sz t.timed_out
     (List.length t.es) (stringify_rtree_matches t)) :: (matchlines @ childlines)

and build_lines_match (k:int) (tt:typ) ((e, bs):rmatch) : pretty_line list =
    let s = Printf.sprintf "match %s :: %s" (Pp.pp_exp e) (Pp.pp_typ tt) in
    (k, s) :: List.concat_map ~f:(fun (p, t) ->
      let s = sprintf "| %s ->" (Pp.pp_pat p) in
      (k+1, s) :: build_lines_rtree (k+2) t) bs

and build_lines_matches k t ms = match ms with
  | None -> []
  | Some ms -> build_lines_match k t ms

and build_lines_rnode (k:int) (tt:typ) (n:rnode) : pretty_line list =
  match n with
  | SAbs (f, (x, t1), t2, t) ->
      let s = Printf.sprintf "fix %s (%s:%s) : %s :: %s" f x (Pp.pp_typ t1) (Pp.pp_typ t2) (Pp.pp_typ tt) in
      (k, s) :: build_lines_rtree (k+1) t
  | SCtor (c, t) ->
      let s = Printf.sprintf "ctor %s :: %s" c (Pp.pp_typ tt) in
      (k, s) :: (build_lines_rtree (k+1) t)
  | STuple ts ->
      let s = Printf.sprintf "tuple :: %s" (Pp.pp_typ tt) in
      (k, s) :: List.concat_map ~f:(build_lines_rtree (k+1)) ts
  | SRcd ts ->
      let s = Printf.sprintf "record :: %s" (Pp.pp_typ tt) in
      (k, s) :: List.concat_map ~f:(fun (_,t) -> build_lines_rtree (k+1) t) ts
  | SUnit ->
      let s = Printf.sprintf "unit :: %s" (Pp.pp_typ tt) in
      [(k, s)]

let pp_rtree t = build_lines_rtree 0 t |> pretty_lines |> stringify

(***** }}} *****)

(***** Refinement tree construction {{{ *****)

type synth_branch  = id * pat * Gamma.t
type eval_val      = {
    scrut_ctor  : id;            (* The constructor that the scrutinee evaluates to.    *)
    scrut_val   : value;         (* The value that the scrutinee evalutes to (no ctor). *)
    env:env;                     (* The environment for a particular world.             *)
    goal:value;                  (* The expected outcome of the larger match statement. *)
}

(* Creates a rtree for the given synthesis problem. *)
let rec create_rtree
    (s:Sigma.t)
    (g:Gamma.t)
    (env:env)
    (t:typ)
    (matches_count:int)
    (matches_permitted:bool)
  : rtree =
  begin match Gamma.peel_nonrecursive_variant g s with
    | None ->
      { t         = t
      ; sz        = 1
      ; g         = g
      ; es        = []
      ; timed_out = false
      ; possible_match = None
      (*else Some (create_matches s g env t matches_count 1 !scrutinee_size_lim)*)
      ; refinements  = create_non_matches s g env t matches_count
      ; forced_match = false
      ; matches_permitted = matches_permitted
      }
    | Some ((e,_),g) ->
      let m = Option.value_exn (create_match s g env t e matches_count) in
      { t         = t
      ; sz        = 1
      ; g         = g
      ; es        = []
      ; timed_out = false
      ; possible_match   = Some m
      ; refinements  = None
      ; forced_match = true
      ; matches_permitted = matches_permitted
      }
  end

(***** Create refinement tree match statements {{{ *****)

(* Distributes the examples according to the constructors that e evaluates to.
 * For each examles (env, v), if env(v) ~~> C (...), then (env, v) is filed
 * under the C bucket. *)
and distribute_constraints (s:Sigma.t) (g:Gamma.t) (e:exp) : synth_branch list =
  let dt = get_base_exn (Typecheck.Typecheck.check_exp s g e) in
  Sigma.ctors dt s |> List.map ~f:begin fun (c, (c_typ, _)) ->
    (* Generate a pattern.                                                                *)
    let (p_opt, g) = match c_typ with        (* Don't create a pattern at unit type.      *)
      | TUnit -> (None, g)
      | _ -> let (p, g) = Gamma.insert_pattern c_typ g in (Some p, g)
    in
    (* Mark pattern variables as decreasing if possible.                                  *)
    let (p_opt, g) = match (p_opt, Gamma.fun_of_arg e g) with
      | (None, _) | (_, None) -> (p_opt, g)
      | (Some p, Some f) ->
        let g  = List.fold_left
              ~f:(fun g x -> Gamma.mark_as_dec_arg_of_fun x f g)
              ~init:g
              (extract_ids_from_pattern p)
        in
        (p_opt, g)
    in
      (c, (c, p_opt), g)
    end

(* Creates a single match for the given synthesis problem and scrutinee expression. *)
(* If evaluation of the potential scrutinee results in no example generated         *)
(* (because all examples resulted in bad pattern matches), then reject this         *)
(* scrutinee immediately.                                                           *)
and create_match
    (s:Sigma.t)
    (g:Gamma.t)
    (env:env)
    (t:typ)
    (e:exp)
    (matches:int)
  : rmatch option =
  (* Returns true if the given synth_branches are an adequate distribution of the       *)
    (* examples as determined by {distribute_constraints}.                                *)
    (* Every branch must have one example.                                                *)
    let branches = distribute_constraints s g e in
    let trees = List.map ~f:(fun (_, p, g) ->
      (p, create_rtree s g env t (matches-1) true)) branches
    in
  Some (e, trees) 

(* Creates match nodes for the given synthesis problem.                                   *)
and create_matches (s:Sigma.t) (g:Gamma.t) (env:env) (t:typ)
                   (matches:int)
                   (scrutinee_min:int) (scrutinee_max:int) : rmatch list =
    match t with
    | TArr _ -> []
    | _      ->
      (* Evaluate a scrutinee candidate {e} to constructors in each example world,        *)
      (* creating a corresponding eval_val for each world.                                *)

      (* Generate scrutinees of size {size} of any type.                                  *)
      let gen_scrutinees size =
          (* Generate scrutinees of size {size} and type {t}.                             *)
        let gen_scrutinees_of_type t' =
          let met = Gen.gen_metric size 1 in
          let scrut_exps = Gen.gen_eexp Timeout.unlimited s g t' met in
          let valid_exps = Rope.filter ~f:(fun e -> Gamma.contains_variant e g) scrut_exps in
          let ms = Rope.map ~f:(fun e -> create_match s g env t e matches) valid_exps in
              Rope.filter_map ~f:Fn.id ms
          in
          Rope.concat_map ~f:gen_scrutinees_of_type (Rope.of_list (Sigma.types s))
      in
      Util.rangen scrutinee_min scrutinee_max |>
      Rope.of_list                            |>
      Rope.concat_map ~f:gen_scrutinees       |>
      Rope.to_list

(***** }}} *****)

(***** Create refinement tree non-match statements {{{ *****)

(* Creates (type-directed) rtree nodes for the given synthesis problem.                   *)
and create_non_matches (s:Sigma.t) (g:Gamma.t) (env:env) (t:typ)
                       (matches:int) : rnode option =
  match t with
  | TUnit -> Some SUnit

  (* Refine constructors *)
  | TBase _ -> None

  (* Refine functions *)
  | TArr (t1, t2) ->
    let f  = Gamma.fresh_id (gen_var_base t ) g in
    let x  = Gamma.fresh_id (gen_var_base t1) (Gamma.insert f t true g) in
    let g  = Gamma.insert x t1 true g in
    Some (SAbs (f, (x, t1), t2, create_rtree s g env t2 matches true))

  (* Refine tuples *)
  | TTuple ts ->
      let trees =
        List.map ~f:(fun t -> create_rtree s g env t matches false) ts
      in
      Some (STuple trees)

  (* Refine records *)
  | TRcd _ -> None

(***** }}} *****)

let rec generate_matches
    (tests_outputs:exp tests_outputs)
    (s:Sigma.t) (env:env) (t:rtree) : rtree list =
  let original_t = t in
  (if t.matches_permitted then
    begin match t.possible_match with
      | None ->
        let ms = create_matches s t.g env t.t 1 1 !scrutinee_size_lim in
        (*let ms =
          deduper
            (tests_outputs_update fst tests_outputs)
            (size % fst)
            ms
          in*)
        List.map
          ~f:(fun m ->
              { t with possible_match = Some m; forced_match = true })
          ms
      | Some (e,bs) ->
        let bs_splittings = List.all_splittings bs in
        List.concat_map
          ~f:(fun (pre,(p,t),post) ->
              (*print_endline (string_of_int (List.length pre));*)
              let make_match e' = create_exp (EMatch(e,[(p,e')])) in
              let tests_outputs =
                tests_outputs_update
                  make_match
                  tests_outputs
              in
              let ts = generate_matches tests_outputs s env t in
              List.map
                ~f:(fun t -> { original_t with possible_match = Some (e,pre@((p,t)::post))})
                ts)
          bs_splittings
    end
   else [])
  @
  (List.map
     ~f:(fun rn -> {t with refinements = Some rn})
     (Option.value
        ~default:[]
        (Option.map
           ~f:(generate_matches_rnode tests_outputs s env)
           t.refinements)))

and generate_matches_rnode
    (tests_outputs:exp tests_outputs)
    (s:Sigma.t) (env:env) (n:rnode) : rnode list =
  match n with
  | SAbs (f, x, ty, t) ->
    let e_transformer = fun e -> create_exp (EFix (f, x, ty, e)) in
    let tests_outputs = tests_outputs_update e_transformer tests_outputs in
    List.map
                           ~f:(fun t -> SAbs(f,x,ty,t))
                           (generate_matches tests_outputs s env t)
  | SCtor _ -> []
  | STuple _ -> []
  | SRcd _ -> []
  | SUnit -> []

(* Grows the given refinement tree by one level of matches. *)
(*let rec grow_matches (s:Sigma.t) (env:env) (t:rtree) =
  if t.matches_permitted then
    begin match t.matches with
      | None ->
        let ms = create_matches s t.g env t.t 1 1 !scrutinee_size_lim in
        t.matches <- Some (ms);
        t.scrutinee_size <- !scrutinee_size_lim
      | Some ms ->
        List.iter
          ~f:(fun (_, bs) -> List.iter ~f:(fun (_, t) -> grow_matches s env t) bs)
          ms
    end;
  List.iter ~f:(grow_matches_rnode s env) t.refinements

and grow_matches_rnode (s:Sigma.t) (env:env) (n:rnode) =
  match n with
  | SAbs (_, _, _, t) -> grow_matches s env t
  | SCtor (_, t) -> grow_matches s env t
  | STuple ts -> List.iter ~f:(grow_matches s env) ts
  | SRcd ts -> List.iter ~f:(fun (_,t) -> grow_matches s env t) ts
  | SUnit -> ()

(* Grows the given refinement tree by expanding the match scrutinees by
 * size k. *)
let rec grow_scrutinees (s:Sigma.t) (env:env) (k:int) (t:rtree) =
  begin match t.matches with
  | None -> ()
  | Some ms ->
    if not t.forced_match then
      begin let min = t.scrutinee_size+1 in
        let max = t.scrutinee_size+k in
        let ms' = create_matches s t.g env t.t 1 min max in
        t.matches <- Some (ms @ ms');
        t.scrutinee_size <- max;
      end;
    List.iter
      ~f:(fun (_, bs) ->
          List.iter ~f:(fun (_, t) -> grow_scrutinees s env k t) bs)
      ms
  end;
  List.iter ~f:(grow_scrutinees_rnode s env k) t.refinements

and grow_scrutinees_rnode (s:Sigma.t) (env:env) (k:int) (n:rnode) =
  match n with
  | SAbs (_, _, _, t) -> grow_scrutinees s env k t
  | SCtor (_, t) -> grow_scrutinees s env k t
  | STuple ts -> List.iter ~f:(grow_scrutinees s env k) ts
  | SRcd ts -> List.iter ~f:(fun (_,t) -> grow_scrutinees s env k t) ts
  | SUnit -> ()*)

(***** }}} *****)

(***** Refinement tree manipulation {{{ *****)
let check_exp (e:exp) (env_global:env) (env_local:env) (v:value) : bool =
  try v = (Timing.record
            ~label:"update_exps::eval"
            ~action:(fun _ -> Eval.eval (Eval.insert_all env_global env_local) e))
  with Eval.Eval_error msg ->
    if not !incomplete_constraints_flag then begin
      incomplete_constraints_flag := true;
      eprintf "Warning: incomplete constraint set given\n%s\n" msg;
    end; false

(***** update_exps: e-guesses at each node in the rtree {{{ *****)

let rec update_exps ?short_circuit:(sc = true) (timeout:float)
                    (s:Sigma.t) (env:env) (t:rtree) =
  let do_if_no_exp (f:unit -> unit) =
    if not sc || List.length t.es = 0 then f ()
  in
  (* Update this node's expressions... *)
  do_if_no_exp (fun _ ->
    (* NOTE: only generate expressions at this node if it is at base type... *)
    begin match t.t with
    | TArr _ | TUnit | TTuple _ | TRcd _ -> ()
    | TBase _ ->
      (* ...and we have not exceeded the max eguess size nor timed out yet. *)
      if (not t.timed_out) && t.sz <= !max_eguess_size then try
        Timing.record
          ~label:"update_exps::gen"
          ~action:begin fun _ ->
            Gen.gen_iexp
              (Timeout.create timeout) s t.g t.t (Gen.gen_metric t.sz 1)
          end
        |> Rope.iter ~f:begin fun e ->
            (* TODO: probably want to short-circuit walking through gen_eexp
             * results as well... *)
            if sc then
              match t.es with
              | [] -> t.es <- e::t.es
              | _ :: _ -> ()
            else
              t.es <- e :: t.es
            end;
        t.sz <- t.sz + 1
      with
        Timeout.Timeout_exception -> begin
          do_if_verbose (fun _ ->
            Printf.printf
              "Timeout occurred while guessing, size = %d\n%!" t.sz);
          t.timed_out <- true
        end
    end);
  (* ...if we didn't update this tree's exp then recursively update it's
   * children. *)
  do_if_no_exp (fun _ -> begin
        update_exps_matches ~short_circuit:sc timeout s env t.possible_match;
        Option.iter ~f:(update_exps_node ~short_circuit:sc timeout s env)
          t.refinements;
      end)

and update_exps_matches ?short_circuit:(sc = true) (timeout:float) (s:Sigma.t)
                        (env:env) (mopt:rmatch option) =
  match mopt with
  | None -> ()
  | Some ms ->
      update_exps_rmatch ~short_circuit:sc timeout s env ms

and update_exps_rmatch ?short_circuit:(sc = true) (timeout:float)
                       (s:Sigma.t) (env:env) (m:rmatch) =
  let (_, bs) = m in
  List.iter ~f:(fun (_, t) -> update_exps ~short_circuit:sc timeout s env t) bs

and update_exps_node ?short_circuit:(sc = true) (timeout:float)
                     (s:Sigma.t) (env:env) (n:rnode) =
  begin match n with
  | SAbs (_, _, _, t) -> update_exps ~short_circuit:sc timeout s env t
  | SCtor (_, t) -> update_exps ~short_circuit:sc timeout s env t
  | STuple ts -> List.iter ~f:(update_exps ~short_circuit:sc timeout s env) ts
  | SRcd ts -> List.iter ~f:(fun (_,t) -> update_exps ~short_circuit:sc timeout s env t) ts
  | SUnit -> ()
  end

(***** }}} *****)

(***** reset_timeouts: resets the timeout flag in the rtree {{{ *****)

let rec reset_timeouts (t:rtree) = begin
  t.timed_out <- false;
  match t.possible_match with
  | None -> ()
  | Some (_,bs) -> begin
          List.iter ~f:(fun (_, t) -> reset_timeouts t) bs
    end;
    Option.iter ~f:reset_timeouts_refinements t.refinements
end

and reset_timeouts_refinements (n:rnode) =
  match n with
  | SAbs (_, _, _, t) -> reset_timeouts t
  | SCtor (_, t) -> reset_timeouts t
  | STuple ts -> List.iter ~f:reset_timeouts ts
  | SRcd ts -> List.iter ~f:(fun (_,t) -> reset_timeouts t) ts
  | SUnit -> ()

(***** }}} *****)

(***** propogate_exps: tries to construct exps from rtree sub-children {{{ *****)

let select_tops
    (es:'a list)
    (ranking:'a -> Float.t)
    (to_size:'a -> Int.t)
  : ('a list * Float.t) option =
  let e_rank_size = List.map ~f:(fun e -> (e,(ranking e,-1 * to_size e))) es in
  let sorted_e_rank = List.sort ~compare:(fun (_,f1) (_,f2) -> (Tuple.T2.compare ~cmp1:Float.compare ~cmp2:Int.compare) f2 f1) e_rank_size in
  begin match sorted_e_rank with
    | [] -> None
    | (e,(r,_))::t ->
      if r = 1. then
        Some ([e],1.)
      else
        Some (e :: (List.map
                      ~f:fst
                      (List.take_while ~f:(fun (_,(r',_)) -> r = r') t)),r)
  end

let select_any_improve
    (es:'a list)
    (runs:('a -> bool list))
  : 'a list =
  List.filter
    ~f:(fun e ->
        List.exists
          ~f:(ident)
          (runs e))
    es


let retrieve_maxes_and_indices
    (l:'a list)
    (cmp:'a -> 'a -> int)
  : ('a * int) list =
  match l with
    | [] -> failwith "cannot"
    | h::t -> [List.foldi t ~init:(h,0)
                          ~f:(fun i (accv,acci) x ->
                              if cmp accv x < 0 then
                                (x,i+1)
                              else
                                (accv,acci))]

type pnode =
  | Node of exp * (pat * pnode) list
  | Leaf of exp
[@@deriving ord, show, hash]

type test_output_result_tree = (pnode test_output * test_output_result_lazy) tree

type deps = int list
type pnt_sub = (pnode test_output * deps * test_output_result_lazy) Array.t
type pnt = pnode * pnt_sub
type pnt_backtrack_node = (int * pnt list)

type output_tree = value option tree list
[@@deriving ord, show, hash]

let rec force_output_tree
    (ts:test_output_result_tree list)
  : value option tree list =
  List.map
    ~f:(fun (TNode((_,res),children)) ->
        let (_,vo) = Lazy.force res in
        begin match vo with
          | None ->
            TNode(None
                 ,[])
          | Some v ->
            TNode(Some v
                 ,force_output_tree children)
        end)
    ts

let force_output_array
    (ts:pnt_sub)
  : value option Array.t =
  Array.map
    ~f:(fun (_,_,res) -> snd (Lazy.force res))
    ts

type ppath = (exp * pat) list
[@@deriving ord, show, hash]

let rec pnode_to_exp
    (p:pnode)
  : exp =
  begin match p with
    | Node (e,ppns) ->
      create_exp (EMatch (e, List.map ~f:(fun (p,pn) -> (p,pnode_to_exp pn)) ppns))
    | Leaf e -> e
  end

let ppath_to_pnode
    (pp:ppath)
    (e:exp)
  : pnode =
  List.fold_right
    ~f:(fun (e,p) pn ->
        Node (e,[(p,pn)]))
    ~init:(Leaf e)
    pp

let retrieve_match_exp_exn
    (t:rtree)
  : exp =
  fst (Option.value_exn t.possible_match)


let rec retrieve_force_match_ppaths
    (t:rtree)
  (*(exp_finder:(exp -> output) -> (exp -> Float.t) -> rtree -> exp list)*)
  : (ppath * rtree) list =
  if t.forced_match then
    let (e,prts) = (Option.value_exn t.possible_match) in
    List.concat_map
      ~f:(fun (p,rt) ->
          let ppess =
            retrieve_force_match_ppaths
              rt
          in
          List.map ~f:(fun (pp,t) -> ((e,p)::pp),t) ppess)
      prts
  else
    [[],t]
(*[([],exp_finder exp_to_output condition t)]*)

let rec contains_path
    (pn:pnode)
    (pp:ppath)
  : bool =
  begin match (pn,pp) with
    | (_, []) -> true
    | (Leaf _, _) -> false
    | (Node (e,ppns), (e',p')::t) ->
      if e = e' then
        List.exists
          ~f:(fun (p,pn) ->
              p = p' &&
              contains_path pn t)
          ppns
      else
        false
  end


let integrate_path_exn
    (pp:ppath)
    (pn:pnode)
    (e_base:exp)
  : pnode =
  let rec integrate_path_internal
      (pp:ppath)
      (pn:pnode)
    : pnode =
    begin match (pn,pp) with
      | (Node (e,ppns), (_,p)::t) ->
        let p_update =
          fun (p',pn') ->
            if p = p' then
              Some (p',integrate_path_internal t pn')
            else
              None
        in
        begin match update_first ~f:p_update ppns with
          | None -> Node (e,(p,ppath_to_pnode t e_base)::ppns)
          | Some ppns -> Node (e,ppns)
        end
      | _ -> failwith "shouldn't happen"
    end
  in
  (integrate_path_internal pp pn)

let integrate_path
    (pp:ppath)
    (pn:pnode)
    (e_base:exp)
  : pnode option =
  let rec integrate_path_internal
      (pp:ppath)
      (pn:pnode)
    : pnode =
    begin match (pn,pp) with
      | (Node (e,ppns), (_,p)::t) ->
        let p_update =
          fun (p',pn') ->
            if p = p' then
              Some (p',integrate_path_internal t pn')
            else
              None
        in
        begin match update_first ~f:p_update ppns with
          | None -> Node (e,(p,ppath_to_pnode t e_base)::ppns)
          | Some ppns -> Node (e,ppns)
        end
      | _ -> failwith "shouldn't happen"
    end
  in
  if contains_path pn pp then
    None
  else
    Some (integrate_path_internal pp pn)

let valid_pnt
    ((_,tests_outputs_results):pnt)
  : bool =
  (*if !magic_num = desired_magic_num then print_endline "pnt start";
    if !magic_num = desired_magic_num then print_endline ("PNT" ^ (Pp.pp_exp (pnode_to_exp pn)));*)
  let valid_test_output_result_lazy
      (res:test_output_result_lazy)
    : bool =
    let (b,vo) = Lazy.force_val res in
    begin match vo with
      | None -> true
      | Some _ -> (*if b && !magic_num = desired_magic_num then print_endline "OMG WHAT"; if not b && !magic_num = desired_magic_num then print_endline ("didnt work, here's pnt" ^ (Pp.pp_exp (pnode_to_exp pn)));*) b
    end
  in
  let b = Array.for_all
    ~f:(valid_test_output_result_lazy % trd3)
    tests_outputs_results
  in
  (*if !magic_num = desired_magic_num && b then print_endline "THIS WAS VALID WHAT";*)
  b
  (*let rec valid_test_output_result_trees
      (tests_outputs_results:test_output_result_tree list)
    : bool =
    List.for_all
      ~f:(fun (TNode((_,res),children)) ->
          let (b,vo) = Lazy.force_val res in
          begin match vo with
            | None -> true
            | Some _ ->
              b && valid_test_output_result_trees children
          end)
      tests_outputs_results
    in
    valid_test_output_result_trees tests_outputs_results*)

let completed_pnt
    ((_,tests_outputs_results):pnt)
  : bool =
  let completed_test_output_result_lazy
      (res:test_output_result_lazy)
    : bool =
    fst (Lazy.force_val res)
  in
  (*let rec completed_test_output_result_trees
      (tests_outputs_results:test_output_result_tree list)
    : bool =
    List.for_all
      ~f:(fun (TNode((_,res),children)) ->
          let (b,_) = Lazy.force_val res in
          b && completed_test_output_result_trees children)
      tests_outputs_results
  in
    completed_test_output_result_trees tests_outputs_results*)
  Array.for_all
    ~f:(completed_test_output_result_lazy % trd3)
    tests_outputs_results

let rec extract_path_element
    (path:int list)
    (trees:'a tree list)
  : 'a =
  begin match path with
    | [] -> failwith "shouldnt happen"
    | [n] ->
      let TNode(v,_) = List.nth_exn trees n in
      v
    | n::rest ->
      let TNode(_,children) = List.nth_exn trees n in
      extract_path_element rest children
  end

(*let passes_path
    (path:int list)
    ((_,tests_outputs_results):pnt)
  : bool =
  let (_,res) = extract_path_element path tests_outputs_results in
  fst (Lazy.force_val res)*)

let passes_index
    (i:int)
    ((_,tests_outputs_results):pnt)
  : bool =
  let (_,_,res) = tests_outputs_results.(i) in
  (*if !magic_num = desired_magic_num then (let fres = (Lazy.force_val res) in if Option.is_some (snd fres) then print_endline "GETS HERE BABY"; if Option.is_some (snd fres) then print_endline (Pp.pp_value (Option.value_exn (snd fres))));*)
  fst (Lazy.force_val res)

(*let updated_tests_pnt
    ((_,tests_outputs_results1):pnt)
    ((_,tests_outputs_results2):pnt)
  : bool =
  let rec updated_test_output_result_trees
      (tors:(test_output_result_tree * test_output_result_tree) list)
    : bool =
    List.exists
      ~f:(fun ((TNode((_,res1),children1)),(TNode((_,res2),children2))) ->
          let (b1,vo1) = Lazy.force_val res1 in
          let (b2,vo2) = Lazy.force_val res2 in
          if b1 <> b2 then
            true
          else
            begin match (vo1,vo2) with
              | (None,None) -> false
              | (Some _,Some _) ->
                updated_test_output_result_trees
                  (List.zip_exn children1 children2)
              | _ -> failwith "shouldnt happen"
            end)
      tors
  in
  updated_test_output_result_trees
    (List.zip_exn tests_outputs_results1 tests_outputs_results2)*)

let update_pnt
    (old_pnt:pnt)
    (new_pn:pnode)
    (condition:pnt -> bool)
  : pnt option =
  let (_,tests_outputs_results) = old_pnt in
  let completed_test_output_results
      (tests_outputs_results:pnt_sub)
    : pnt_sub =
    let new_tor = Array.copy tests_outputs_results in
    Array.iteri
      ~f:(fun i (test_output,deps,res) ->
          let runner = trd3 test_output in
          let lazy_result =
            lazy
              (let (b,vo) = Lazy.force_val res in
               begin match vo with
                 | None ->
                   let subos =
                     List.map
                       ~f:(fun i ->
                           let res = trd3 new_tor.(i) in
                           snd (Lazy.force_val res))
                       deps
                   in
                   let subs_o = List.distribute_option subos in
                   begin match subs_o with
                     | None -> (false,None)
                     | Some vs ->
                       runner new_pn vs
                   end
                 | Some _ -> (b,vo)
               end)
          in
          new_tor.(i) <- (test_output,deps,lazy_result))
      new_tor;
    new_tor
    (*Array.map
      ~f:(fun (test_output,deps,res) ->
          let lazy_result =
            lazy
              (let (b,vo) = Lazy.force_val res in
               begin match vo with
                 | None ->
                   let subs_o =
                     List.map
                       ~f:(fun i -> )

                   runner new_pn
                 | Some _ -> (b,vo)
               end)
          in
          (test_output,deps,lazy_result))
      tests_outputs_results*)
  in
  let new_pnt =
    (new_pn
    ,completed_test_output_results tests_outputs_results)
  in
  if (condition new_pnt) && (valid_pnt new_pnt) then
    ((*if !magic_num = desired_magic_num then print_endline "SHOULD CONTINUE";*) Some new_pnt)
  else
    ((*if !magic_num = desired_magic_num then print_endline "WHY NOT";*) None)

type empty_solution_cache_key = rtree * (exp * exp) list
(*type partition_solution_cache_value_component = pnode
[@@deriving ord, show, hash]
type partition_solution_cache_value = partition_solution_cache_value_component list
type partition_solution_cache =
  (partition_solution_cache_key * partition_solution_cache_value) list*)

(*let rec any_nonforced_matches r : bool =
  let contains_itself =
    begin match r.possible_match with
      | None -> false
      | _ -> true
    end
  in
  (not r.forced_match && contains_itself)
  || List.exists ~f:any_nonforced_matches_rnode r.refinements
  || (begin match r.possible_match with
      | None -> false
      | Some ms -> any_nonforced_matches_rmatch ms
    end)

and any_nonforced_matches_rnode r : bool =
  begin match r with
    | SAbs(_,_,_,r) -> any_nonforced_matches r
    | SCtor(_,r) -> any_nonforced_matches r
    | STuple rs -> List.exists ~f:any_nonforced_matches rs
    | SRcd _ -> failwith "too lazy"
    | SUnit -> false
  end

and any_nonforced_matches_rmatch (_,bs) : bool =
  List.exists
    ~f:(fun (_,r) -> any_nonforced_matches r)
    bs*)

let rec rtree_equal r1 r2 : bool =
  r1.t = r2.t
  && r1.sz = r2.sz
  && Gamma.hash r1.g = Gamma.hash r2.g
  && r1.es = r2.es
  && Option.equal rnode_equal r1.refinements r2.refinements
  && Option.equal rmatch_equal r1.possible_match r2.possible_match
  && r1.forced_match = r2.forced_match
  && r1.matches_permitted = r2.matches_permitted

and rnode_equal r1 r2 : bool =
  begin match (r1,r2) with
    | (SAbs (i1,a1,t1,rt1), SAbs (i2,a2,t2,rt2)) ->
      (compare_id i1 i2 = 0) &&
      (compare_arg a1 a2 = 0) &&
      (compare_typ t1 t2 = 0) &&
      rtree_equal rt1 rt2
    | (SCtor (i1,rt1), SCtor (i2,rt2)) ->
      (compare_id i1 i2 = 0) &&
      rtree_equal rt1 rt2
    | (STuple rts1, STuple rts2) ->
      List.equal ~equal:rtree_equal rts1 rts2
    | (SRcd _, SRcd _) -> failwith "todo"
    | (SUnit, SUnit) -> true
    | _ -> false
  end

and rmatch_equal (e1,branches1) (e2,branches2) : bool =
  (compare_exp e1 e2 = 0) &&
  List.equal ~equal:((fun (pat1,rt1) (pat2,rt2)
                     -> (compare_pat pat1 pat2 = 0) &&
                        rtree_equal rt1 rt2))
             branches1
             branches2

let solution_cache : empty_solution_cache_key list ref = ref []

let update_solution_cache
    (t:rtree)
    (ios:(exp * exp) list)
  : unit =
  solution_cache := (t,ios)::!solution_cache
    (*((duplicate_rtree t,List.map ~f:(fun (_,i,o,_) -> (i,o)) tests_outputs), pnodes)
      ::!solution_cache*)


let has_no_solution_via_cache
    (_:rtree)
    (_:(exp * exp) list)
  : bool =
  false
  (*List.exists
    ~f:(fun (t',ios') ->
        rtree_equal t t' &&
        List.contains_as_multiset
          ~compare:(pair_compare compare_exp compare_exp)
          ios
          ios')
    !solution_cache*)
  (*let minimal_partitions_tests_outputs =
    split_into_minimal_partitions
      ~compare:(fun (e1,_,_) (e2,_,_) -> contains e1 e2)
      ~total_order:(fun (e1,_,_) (e2,_,_) -> compare_exp e1 e2)
      tests_outputs
  in
  List.fold_left
    ~f:(fun acc_o ((t',e12s),v) ->
        begin match acc_o with
          | Some _ -> acc_o
          | None ->
            if rtree_equal t' t then
              let fst_sat_o =
                List.find
                  ~f:(fun (tests_outputs,_) ->
                        0 = (List.compare_as_multisets
                           ~cmp:(pair_compare compare_exp compare_exp)
                           (List.map ~f:(fun (e1,e2,_) -> (e1,e2)) tests_outputs)
                           e12s))
                  minimal_partitions_tests_outputs
              in
              Option.map ~f:(fun (prior,remaining) -> (v,remaining,prior)) fst_sat_o
            else
              None
        end)
    ~init:None
    (!solution_cache)*)
(*
              let fst_sat_o =
                List.find
                  ~f:(fun (tests_outputs,_) ->
                        (List.compare_as_multisets
                           ~cmp:(Tuple.T2.compare ~cmp1:compare_exp ~cmp2:compare_exp)
                           (List.map ~f:(fun (e1,e2,_) -> (e1,e2)) tests_outputs)
                           e12s) = 0)
                  minimal_partitions_tests_outputs
              in
              Option.map ~f:(fun (prior,remaining) -> (v,remaining,prior)) fst_sat_o
            else
              None
        end)
    ~init:None
    (!solution_cache)*)

let rec propogate_exps ?short_circuit:(sc = true)
    (enforced_completed:bool)
    (tests_outputs:exp tests_outputs)
    (extractor:exp -> exp list)
    (replacer:exp -> exp list -> exp)
    (t:rtree)
    ~(search_matches:bool)
  : exp list =
  if sc && List.length t.es > 0 then
    t.es
  else
    (* NOTE: Prioritize lambdas, matches, and then constructors, in that order. *)
    let es = t.es
             @ propogate_exps_matches ~short_circuit:sc enforced_completed tests_outputs t ~search_matches extractor replacer
             @ Option.value_map
               ~f:(propogate_exps_node ~short_circuit:sc enforced_completed tests_outputs ~search_matches extractor replacer)
               ~default:[]
               t.refinements
    in
    (*t.es <- es;*)
    es

and propogate_exps_matches ?short_circuit:(sc = true)
    (enforced_completed:bool)
    (tests_outputs:exp tests_outputs)
    (t:rtree)
    ~(search_matches:bool)
    (extractor:exp -> exp list)
    (replacer:exp -> exp list -> exp)
  : exp list =
  if t.forced_match && not enforced_completed then
    propagate_enforced_matches ~short_circuit:sc tests_outputs t extractor replacer
  else
    match t.possible_match with
    | None -> []
    | Some _ ->
      if search_matches then
        (*begin
          let ms =
            deduper
              (tests_outputs_update fst tests_outputs)
              (size % fst)
              ms
          in
          List.concat_map
            ~f:(propogate_exps_rmatch
                 enforced_completed
                  ~short_circuit:sc
                  tests_outputs)
            ms
          end*)
        []
      else
        []

and propogate_exps_rmatch
    ?short_circuit:(_ = true)
    (_:bool)
    (_:exp tests_outputs)
    (_:rmatch)
    (_:exp -> exp list)
    (_:exp -> exp list -> exp)
  (*?short_circuit:(sc = true)
    (enforced_completed:bool)
    (tests_outputs:exp tests_outputs)
    (m:rmatch)
    (extractor:exp -> exp list)
                            (replacer:exp -> exp list -> exp)*)
  : exp list =
  failwith "shouldn't hit";
  (*let (e, bs)  = m in
  (*let is_desired = e = EApp ((EApp (EVar "compare", EVar "n1")), EVar "n3") in*)
  (*if is_desired then print_endline "ITS HAPPENING";*)
  (*let (ps, ts) = List.unzip bs in*)
  (*print_endline (Pp.pp_exp e);
    print_endline (List.to_string ~f:(fun (p,r) -> "(" ^ Pp.pp_pat p ^ "," ^ pp_rtree r ^ ")") bs);*)
  (*print_endline "startb";
    print_endline (string_of_int (List.length bs));*)
  let nonprod_bs =
    List.map
      ~f:(fun (p,t) ->
          (*print_endline "this is slow why?";*)
          let make_match e' = create_exp (EMatch(e,[(p,e')])) in
          let tests_outputs = tests_outputs_update make_match tests_outputs in
          let initial_es = propogate_exps ~short_circuit:sc enforced_completed tests_outputs ~search_matches:true extractor replacer t in
          (*print_endline "1";*)
          (*print_endline @$ string_of_int (List.length es);*)
          (*let es =
            minimize
              size
              initial_es
              tests_outputs
            in*)
          let nonproductive = List.length es = 0 in
          let es =
            if nonproductive then
              begin match initial_es with
                | [] -> []
                | h::_ -> [h]
              end
            else
              es
          in
          (*print_endline "abs";
          print_endline @$ string_of_int (List.length es);
            print_endline "3";*)
          (nonproductive,List.map ~f:(fun e -> (p,e)) es))
      bs
  in
  let (nonprod,bs) = List.unzip nonprod_bs in
  if List.for_all ~f:ident nonprod then
    []
  else
    let brancheses = combinations bs in
    let ans = List.map ~f:(fun bs -> create_exp (EMatch(e,bs))) brancheses in

  (*let ans =
    ([[]],bs)
    List.fold_until_completion
    ~f:(fun (established_branches,bs) ->
         let make_match bs = EMatch(e,bs) in
        if bs = [] then
          Right (List.map ~f:make_match established_branches)
        else
          let integrations_rank_bos =
            List.map
              ~f:(fun pes ->
                  let full_bes =
                    cartesian_map
                      ~f:(fun pe eb -> pe::eb)
                      pes
                      established_branches
                  in
                  Option.map
                    ~f:(fun (b,v) -> (pes,b,v))
                    (select_tops
                       full_bes
                       (fun bs ->
                          test_performance_to_ranking
                            (List.map
                               ~f:(fun (_,run) -> run (make_match bs))
                               tests))
                       (size % make_match)))
              bs
          in
          let integrations_rank_bs_o = distribute_option integrations_rank_bos in
          begin match integrations_rank_bs_o with
            | None -> Right []
            | Some integrations_ranks ->
              let maxes_indices =
                retrieve_maxes_and_indices
                  integrations_ranks
                  (fun (_,_,f1) (_,_,f2) -> Float.compare f1 f2)
              in
              if List.length maxes_indices = 0 then
                failwith "unexpected"
              else if List.length maxes_indices = 1 then
                let ((_,established_branches,_),i) = List.hd_exn maxes_indices in
                (*let ((established_branches,_),i) =*)
                print_endline "BEGINIT";
                print_endline @$ string_of_int (List.length established_branches);
                let pns =
                  deduper
                    (exp_to_output % make_match)
                    (size % make_match)
                    established_branches
                in
                let (_,bs) = remove_at_index_exn bs i in
                Left (pns,bs)
              else
                failwith "TODO"
          end)
    ([[]],bs)
    in*)
  (*if is_desired then print_endline "it happened";*)
  ans
  (*let branches_o =
    List.fold_left
      ~f:(fun bss_o (p,t) ->
          begin match bss_o with
            | None -> None
            | Some bss ->
              let above_adder =
                fun e' ->
                  above_adder (EMatch (e,[(p,e')]))
              in
              let make_match e' bs = EMatch (e,(p,e')::bs) in
              let new_condition =
                fun e ->
                  Option.value_exn
                    (List.max_elt
                       ~compare:Float.compare
                       (List.map
                          ~f:(fun bs -> condition (make_match e bs))
                          bss))
              in
              print_endline "hi there";
              print_endline (pp_rtree t);
              let t_es = propogate_exps ~short_circuit:sc above_adder new_condition deduper t in
              let pe = List.map ~f:(fun e -> (p,e)) t_es in
              print_endline (string_of_int (List.length pe));
              print_endline (string_of_int (List.length bss));
              let non_projected = Util.cartesian_map ~f:List.cons pe bss in
              print_endline "why?";
              let ans = select_tops
                  non_projected
                  (fun bs -> condition (EMatch (e,bs))) in
              Option.map ~f:fst ans
          end)
      ~init:(Some [[]])
      bs
  in
    print_endline "endb";
  begin match branches_o with
    | None -> []
    | Some branches ->
      List.map ~f:(fun bs -> EMatch (e, bs)) branches
    end*)*)

and propogate_exps_node
    ?short_circuit:(sc = true)
    (enforced_completed:bool)
    (tests_outputs:exp tests_outputs)
    ~(search_matches:bool)
    (extractor:exp -> exp list)
    (replacer:exp -> exp list -> exp)
    (n:rnode)
  : exp list =
  match n with
  | SUnit -> [create_exp EUnit]

  | SAbs (f, x, ty, t) ->
    let e_transformer = fun e -> create_exp (EFix (f, x, ty, e)) in
    let tests_outputs = tests_outputs_update e_transformer tests_outputs in
    List.map
      ~f:e_transformer
      (propogate_exps
         ~short_circuit:sc
         enforced_completed
         tests_outputs
         ~search_matches
         extractor
         replacer
         t)

  | SCtor (c, t) ->
    propogate_exps ~short_circuit:sc enforced_completed tests_outputs ~search_matches extractor replacer t |> List.map ~f:(fun e -> create_exp (ECtor (c, e)))

  | STuple ts ->
    List.map ~f:(propogate_exps ~short_circuit:sc enforced_completed tests_outputs ~search_matches extractor replacer) ts
    |> Util.combinations
    |> List.map ~f:(fun es -> create_exp (ETuple es))

  | SRcd ts ->
    List.map ~f:(fun (l,t) ->
        List.map ~f:(fun e -> (l,e)) (propogate_exps ~short_circuit:sc enforced_completed tests_outputs ~search_matches extractor replacer t)) ts
    |> Util.combinations
    |> List.map ~f:(fun es -> create_exp (ERcd es))

and propagate_enforced_matches
    ?short_circuit:(sc = true)
    (tests_outputs:exp tests_outputs)
    (t:rtree)
    (extractor:exp -> exp list)
    (replacer:exp -> exp list -> exp)
  : exp list =
  let tests_outputs =
    List.sort
      ~compare:(fun (e1,_,_) (e2,_,_) -> compare_exp e1 e2)
      tests_outputs
  in
  let ios = List.map ~f:(fun (i,o,_) -> (i,o)) tests_outputs in
  if has_no_solution_via_cache t ios then
    ([])
  else
    let inputs = List.map ~f:fst ios in
    let ppaths =
      retrieve_force_match_ppaths
        t
        (*(fun above_adder condition ->
           propogate_exps
             ~short_circuit:sc
             above_adder
             condition)*)
    in
    (*if !magic_num = desired_magic_num  then List.iter
      ~f:(fun (pp,_) -> print_endline (show_ppath pp))
      ppaths;*)
    (*print_endline (List.to_string ~f:(fun (e,_,_) -> Pp.pp_exp e) tests_outputs);*)
    (*List.iter
      ~f:(fun pp -> print_endline (show_ppath (fst pp)))
      ppaths;*)
    (*List.iter
      ~f:(fun (pp,_) -> print_endline (show_ppath pp))
      ppaths;*)
    let possible_branches =
      List.map
        ~f:(fun (p,t) ->
            let es =
              propogate_exps
                ~short_circuit:sc
                true
                ~search_matches:true
                []
                extractor
                replacer
                t
            in
            let es = List.dedup_and_sort ~compare:compare_exp es in
            (p,es)
            (*List.map
              ~f:(fun e -> (p,e))
              es*))
        ppaths
    in
    let tests_outputs = tests_outputs_update pnode_to_exp tests_outputs in
    (*let test_output_tree =
      split_into_containing_tree
        ~compare:(fun (e1,_,_) (e2,_,_) -> contains e1 e2)
        tests_outputs
      in
      let node_paths = node_paths_bfs test_output_tree in*)
    let initial_tests_results =
      Array.of_list
        (List.map
           ~f:(fun tout ->
               let e = fst3 tout in
               let subcomponents = extractor e in
               let deps =
                 List.map
                   ~f:(fun subc ->
                       fst (Option.value_exn (List.findi ~f:(fun _ e -> 0 = compare_exp subc e) inputs)))
                   subcomponents
               in
               (tout,deps,Lazy.from_val (false,None)))
           tests_outputs)
    in
    let test_size = Array.length initial_tests_results in
    let initial_pnt : pnt =
      (Node (retrieve_match_exp_exn t,[])
      ,initial_tests_results)
    in
    let initial_pnt_node : pnt_backtrack_node =
      (0,[initial_pnt])
    in
    if !generate_and_test then
      List.fold_until_completion
        ~f:(fun pns ->
            let new_pns =
              List.concat
                (List.cartesian_filter_map
                   ~f:(fun (p,es) pn ->
                       if contains_path pn p then
                         None
                       else
                         Some
                           (List.map
                              ~f:(integrate_path_exn p pn)
                              es))
                   possible_branches
                   pns)
            in
            if List.is_empty new_pns then
              Right
                (List.map
                   ~f:(pnode_to_exp % fst)
                   (List.filter_map
                      ~f:(fun pn ->
                          let pnt = (pn,initial_tests_results) in
                          update_pnt
                            pnt
                            pn
                            (fun pnt ->
                               List.for_all
                                 ~f:(fun i ->
                                     passes_index
                                       i
                                       pnt)
                                 (range (List.length tests_outputs))))
                      pns))
            else
              Left (List.dedup_and_sort ~compare:compare_pnode new_pns))
        [Node (retrieve_match_exp_exn t,[])]
    else
      (*print_endline (string_of_int !magic_num);
      print_endline (string_of_int desired_magic_num);*)
    let pns =
      List.fold_until_completion
        ~f:(fun (pnt_backtrack_nodes : pnt_backtrack_node list)(*(remaining_indices,pnts,completed_pnts)*) ->
            begin match pnt_backtrack_nodes with
              | [] -> Right []
              | (i,pnts)::pnt_backtrack_nodes ->
                if !magic_num = desired_magic_num then print_endline "START";
                if !magic_num = desired_magic_num then print_endline (string_of_int i);
                if !magic_num = desired_magic_num then print_endline (string_of_int (List.length pnts));
                if !magic_num = desired_magic_num && List.length pnts < 50 then List.iter ~f:(fun (pn,_) -> print_endline (Pp.pp_exp (pnode_to_exp pn))) pnts;
                if i = test_size && (not (List.is_empty pnts)) then
                  Right (List.map ~f:fst pnts)
                else
                  let passes_path = passes_index i in
                  (*if !magic_num = desired_magic_num then print_endline (Pp.pp_exp (fst3 (List.nth_exn tests_outputs i)));*)
                  let (passing_pnts,nonpassing_pnts) =
                    List.partition_tf
                      ~f:passes_path
                      pnts
                  in
                  if (not (List.is_empty passing_pnts)) then
                    Left ((i+1,passing_pnts)::(i,nonpassing_pnts)::pnt_backtrack_nodes)
                  else
                  (*if not (List.is_empty passing_pnts) then
                    let pnt_backtrack_nodes =
                      if List.is_empty nonpassing_pnts then
                        pnt_backtrack_nodes
                      else
                        (i,nonpassing_pnts)::pnt_backtrack_nodes
                    in
                    let pnt_backtrack_nodes = (i+1,passing_pnts)::pnt_backtrack_nodes in
                    Left (pnt_backtrack_nodes)
                    else*)
                    let (first_grouping,second_grouping) =
                      List.split_n
                        nonpassing_pnts
                        1
                  in
                  let pnt_backtrack_nodes =
                    if List.is_empty second_grouping then
                      pnt_backtrack_nodes
                    else
                      (i,second_grouping)::pnt_backtrack_nodes
                  in
                    (*if not (List.is_empty second_grouping) then
                      let pnt_backtrack_nodes =
                        (i,first_grouping)::(i,second_grouping)::pnt_backtrack_nodes
                      in
                      Left pnt_backtrack_nodes
                      else*)
                  let updated_pnts =
                    List.concat
                        (List.cartesian_filter_map
                           ~f:(fun (p,es) old_pnt ->
                              let old_pn = fst old_pnt in
                              if contains_path old_pn p then
                                None
                              else
                                Some (
                                  List.filter_map
                                    ~f:(fun e ->
                                        let pn =
                                          integrate_path_exn
                                            p
                                            old_pn
                                            e
                                        in
                                        update_pnt old_pnt pn passes_path)
                                    es))
                           possible_branches
                           first_grouping)
                  in
                  let updated_pnts =
                    if !no_dedup then
                      updated_pnts
                    else
                      let updated_pnts_with_outputs =
                        List.map
                          ~f:(fun npt -> (npt,force_output_array (snd npt)))
                          updated_pnts
                      in
                      let updated_pnts_with_outputs =
                        core_deduper
                          (fun (_,output_tree1) (_,output_tree2) ->
                             Array.compare compare_output output_tree1 output_tree2)
                          (size % pnode_to_exp % fst % fst)
                          updated_pnts_with_outputs
                      in
                      List.map ~f:fst updated_pnts_with_outputs
                  in
                  let pnts = passing_pnts@updated_pnts in
                  let pnt_backtrack_nodes =
                    if (List.is_empty pnts) then
                      pnt_backtrack_nodes
                        else
                          (i+1,pnts)::pnt_backtrack_nodes
                      in
                      Left pnt_backtrack_nodes

              (*List.iter
                ~f:(fun p -> print_endline (List.to_string ~f:Int.to_string p))
                remaining_paths;
                List.iter
                ~f:(fun pnt -> print_endline (Pp.pp_exp (pnode_to_exp (fst pnt))))
                pnts;*)
              (*let (newly_completed_pnts,incompleted_pnts) =
                List.partition_tf
                  ~f:completed_pnt
                  pnts
                in
                let completed_pnts = newly_completed_pnts@completed_pnts in*)
              (*if List.is_empty incompleted_pnts then
                Right (List.map ~f:fst completed_pnts)
                else
                begin match remaining_indices with
                  | [] -> Right (List.map ~f:fst pnts)
                  | current_index::remaining_indices ->
                    let passes_path = passes_index current_index in
                    (*let path_element = fst3 (fst (extract_path_element current_path (snd (List.hd_exn pnts)))) in
                      print_endline (Pp.pp_exp path_element);*)
                    let (passing_pnts,nonpassing_pnts) =
                    List.partition_tf
                      ~f:passes_path
                      pnts
                  in
                  let updated_pnts_with_outputs =
                    List.cartesian_filter_map_dedup
                      ~f:(fun (p,e) old_pnt ->
                          let new_pnt_o =
                            Option.bind
                              ~f:(fun pn -> update_pnt old_pnt pn passes_path)
                              (integrate_path p (fst old_pnt) e)
                          in
                          Option.map
                            ~f:(fun npt -> (npt,force_output_array (snd npt)))
                            new_pnt_o)
                      ~compare:(fun (_,output_tree1) (_,output_tree2) ->
                          Array.compare compare_output output_tree1 output_tree2)
                      ~to_size:(size % pnode_to_exp % fst % fst)
                      possible_branches
                      nonpassing_pnts
                  in
                  let updated_pnts =
                    List.map
                      ~f:fst
                      updated_pnts_with_outputs
                  in
                  Left (remaining_indices,passing_pnts@updated_pnts,completed_pnts)
              end*)
            end)
        [initial_pnt_node](*(List.range 0 (Array.length initial_tests_results),[initial_pnt],[])*)
    in
    if List.is_empty pns then update_solution_cache t ios;
    let ppeos =
      List.map
        ~f:(fun (pp,rt) ->
            let es =
              propogate_exps
                ~short_circuit:false
                true
                []
                extractor
                replacer
                rt
                ~search_matches:false
            in
            let es_sized =
              List.map
                ~f:(fun e -> (e,size e))
                es
            in
            let sorted_sized_es =
              List.sort
                ~compare:(fun (_,s1) (_,s2) -> Int.compare s1 s2)
                es_sized
            in
            begin match sorted_sized_es with
              | [] -> None
              | _ ->
                let sorted_sized_es =
                  List.take
                    sorted_sized_es
                    (Float.to_int (100000. ** (1. /. (Float.of_int (List.length ppaths)))))
                in
                let es =
                  List.map
                    ~f:fst
                    sorted_sized_es
                in
                Some (pp,es)
            end)
        ppaths
    in
    let ppes_o = Some (List.filter_map ppeos ~f:Fn.id) in
    begin match ppes_o with
      | None -> []
      | Some ppes ->
        (List.concat_map
           ~f:(fun pn ->
               List.map
                 ~f:pnode_to_exp
                 (List.fold_left
                    ~f:(fun pns (pp,es) ->
                        let ans =
                          List.cartesian_filter_map
                            ~f:(integrate_path pp)
                            pns
                            es
                        in
                        if ans = [] then
                          pns
                        else
                          ans)
                    ~init:[pn]
                    ppes))
           pns)
        (*let pns =
          List.fold_until_completion
          ~f:(fun (pns,tests_outputs,prior_tests) ->
              print_endline (string_of_int (List.length pns));
              (*if (!magic_num = 33 && List.length pns = 50) then
                List.iter
                  ~f:(print_endline % Pp.pp_exp % pnode_to_exp)
                  pns;
              if (!magic_num = 33 && List.length pns = 50) then
                List.iter
                  ~f:(print_endline % Pp.pp_exp % fst3)
                  tests_outputs;*)
              (*print_endline (string_of_int (List.length pns));
                print_endline (List.to_string ~f:(fun (e,_,_) -> Pp.pp_exp e) tests_outputs);*)
              if List.length tests_outputs = 0 then
                Right pns
              else
                (*let passing =
                    List.filter
                      ~f:(fun pn ->
                          has_passing_capabilities
                            (tests_outputs_update pnode_to_exp tests_outputs)
                            pn)
                      pns
                  in*)
                let standard_calc () =
                  let (relevant_tests_outputs,next_tests_outputs) =
                    split_by_minimal
                      ~compare:(fun (_,e1,_,_) (_,e2,_,_) -> contains e1 e2)
                      tests_outputs
                  in
                  let tests_outputs =
                    relevant_tests_outputs
                    (*@
                      (List.map ~f:(fun (_,e1,e2,r) -> (false,e1,e2,r)) next_tests_outputs)*)
                  in
                  if (!magic_num = 33 && List.length pns = 50) then
                      print_endline "AND THEN";
                    if (!magic_num = 33 && List.length pns = 50) then
                      List.iter
                        ~f:(print_endline % Pp.pp_exp % (fun (_,e1,_,_) -> e1))
                        tests_outputs;
                    if (!magic_num = 33 && List.length pns = 50) then
                      List.iter
                        ~f:(print_endline % Pp.pp_exp % (fun (_,_,e2,_) -> e2))
                        tests_outputs;
                    (*let all_tests_outputs =
                      relevant_tests_outputs
                      @
                      (List.map
                         ~f:(fun (_,e,r,t) -> (false,e,r,t))
                         next_tests_outputs)
                      in*)

                          (*do_if_verbose (fun _ ->
                            print_endline "cache miss");*)
                          let possible_branches =
                            List.concat_map
                              ~f:(fun (p,t) ->
                                  (*let make_match pn e =
                                    Option.map
                                      ~f:(fun pn -> pnode_to_exp pn)
                                      (integrate_path
                                         p
                                         pn
                                         e)
                                    in*)
                                  (*let lower_tests_outputs =
                                    (List.map
                                       ~f:(fun (b,e1,e2,otm) ->
                                           (b,e1,e2,fun e ->
                                               InternalNode
                                                 (List.map
                                                    ~f:(fun pn ->
                                                        begin match make_match pn e with
                                                          | None -> NonexistantLeaf
                                                          | Some e -> otm e
                                                        end)
                                                    pns)))
                                       relevant_tests_outputs)
                                    in*)
                                  let es =
                                    propogate_exps
                                      ~short_circuit:sc
                                      true
                                      ~search_matches:true
                                      (*(fun e ->
                                         Output.create
                                           (List.concat_map
                                           ~f:(fun pn ->
                                               begin match make_match pn e with
                                                 | None -> [None]
                                                 | Some e -> (exp_to_output e).node
                                               end)
                                           pns))*)
                                      (*lower_*)tests_outputs
                                      (*(fun e ->
                                         snd @$
                                         Option.value_exn
                                           (List.max_elt
                                              ~compare:(pair_compare Float.compare (fun _ _ -> 0))
                                              (List.map
                                                 ~f:(fun pn ->
                                                     let ts = tests (make_match pn e) in
                                                     (test_performance_to_ranking ts,ts))
                                                 pns)))*)
                                      t
                                  in
                                  (*let es =
                                    minimize
                                      size
                                      es
                                      lower_tests_outputs
                                    in*)
                                  List.map
                                    ~f:(fun e -> (p,e))
                                    es
                                    (*let pppns =
                                      cartesian_map
                                        ~f:(fun pn e -> (p,pn,e))
                                        pns
                                        es
                                      in
                                      let pppns =
                                      select_any_improve
                                        pppns
                                        (List.map
                                           ~f:(fun (_,run) ->
                                               fun (p,e,pn) ->
                                                 begin match (integrate_path p e pn) with
                                                   | None -> false
                                                   | Some e -> run (pnode_to_exp e)
                                                 end)
                                           relevant_tests)
                                      in
                                      let pppns =
                                      deduper
                                        (fun (p,pn,e) ->
                                           begin match integrate_path p pn e with
                                             | None -> List.map ~f:(fun _ -> None) (exp_to_output e)
                                             | Some pn -> exp_to_output (pnode_to_exp pn)
                                           end)
                                        (fun (p,pn,e) ->
                                           begin match integrate_path p pn e with
                                             | None -> Int.max_value
                                             | Some pn ->
                                               size (pnode_to_exp pn)
                                           end)
                                        pppns
                                      in
                                      ((p,t),pppns)*))
                              (*(fun (p,e,pn) ->
                                       List.map
                                         ~f:(fun (_,run) -> run (pnode_to_exp (integrate_path p e pn))))*)
                              (*Option.map
                                ~f:(fun (pn,f) -> (es,pn,f))
                                (select_tops
                                   pns
                                   (fun e ->
                                      test_performance_to_ranking
                                        (List.map ~f:(fun (_,run) -> run (pnode_to_exp e)) tests))
                                   (*(test_performance_to_ranking % tests % pnode_to_exp)*)
                                   (size % pnode_to_exp)))*)
                              ppaths
                    in
                    let did_update_tests
                        ((_,tests_outputs_results1):pnode * (pnode test_output * test_output_result_lazy) list)
                        ((_,tests_outputs_results2):pnode * (pnode test_output * test_output_result_lazy) list)
                      : bool =
                      List.exists
                        ~f:(fun ((_,res1),(_,res2)) ->
                            let (_,b1) = Lazy.force_val res1 in
                            let (_,b2) = Lazy.force_val res2 in
                            b1 <> b2)
                        (List.zip_exn tests_outputs_results1 tests_outputs_results2)
                    in
                    let update_pnt
                        (old_pnt:pnode * (pnode test_output * test_output_result_lazy) list)
                        (new_pn:pnode)
                      : (pnode * (pnode test_output * test_output_result_lazy) list) option =
                      let (_,tests_outputs_results) = old_pnt in
                      let new_pnt =
                        (new_pn
                        ,List.map
                            ~f:(fun ((b,e1,e2,runner),res) ->
                                let lazy_result =
                                  lazy
                                    (let (b,vo) = Lazy.force_val res in
                                     begin match vo with
                                       | None -> runner new_pn
                                       | Some _ -> (b,vo)
                                     end)
                                in
                                ((b,e1,e2,runner),lazy_result))
                            tests_outputs_results)
                      in
                      if (valid_pnt new_pnt) && (did_update_tests old_pnt new_pnt) then
                        Some new_pnt
                      else
                        None
                    in
                    (*List.iter
                      ~f:(fun pn -> print_endline (Pp.pp_exp (pnode_to_exp pn)))
                      pns;*)
                    let pnode_tests_outputs =
                      tests_outputs_update pnode_to_exp tests_outputs
                    in
                    let initial_pnts =
                      List.filter_map
                        ~f:(fun pn ->
                            let initial_ts =
                              List.map
                                ~f:(fun (b,e1,e2,runner) ->
                                    let res = lazy (runner pn) in
                                    ((b,e1,e2,runner),res))
                                pnode_tests_outputs
                            in
                            let pnt = (pn,initial_ts) in
                            if valid_pnt pnt then
                              Some pnt
                            else
                              None)
                        pns
                    in
                    let pns =
                      List.fold_until_completion
                        ~f:(fun (incompleted_pnts,completed_pns) ->
                            (*print_endline "here doing";*)
                            let (newly_completed_pnts,incompleted_pnts) =
                              List.partition_tf
                                ~f:(fun (_,ts) -> List.for_all ~f:(fun (_,res) -> fst (Lazy.force_val res)) ts)
                                incompleted_pnts
                            in
                            let newly_completed_pns =
                              List.map
                                ~f:fst
                                newly_completed_pnts
                            in
                            let completed_pns = newly_completed_pns@completed_pns in
                            if List.length incompleted_pnts = 0 then
                              Right completed_pns
                            else
                              let incompleted_pnts =
                                (*print_endline (string_of_int (List.length incompleted_pnts));*)
                                List.cartesian_filter_map
                                  ~f:(fun (p,e) old_pnt ->
                                      Option.bind
                                        ~f:(fun pn -> update_pnt old_pnt pn)
                                        (integrate_path p (fst old_pnt) e))
                                  possible_branches
                                  incompleted_pnts
                              in
                              (*print_endline (string_of_int (List.length incompleted_pnts));*)
                              let incompleted_pnts =
                                core_deduper
                                  (fun (_,tores1) (_,tores2) ->
                                     let bos1 = List.map ~f:(Lazy.force_val % snd) tores1 in
                                     let bos2 = List.map ~f:(Lazy.force_val % snd) tores2 in
                                     List.compare compare_test_output_result bos1 bos2)
                                  (size % pnode_to_exp % fst)
                                  incompleted_pnts
                                  (*(tests_outputs_update (pnode_to_exp % fst) relevant_tests_outputs)*)
                                in
                                let incompleted_pnts' =
                                  minimize
                                    (size % pnode_to_exp % fst)
                                    incompleted_pnts
                                    (tests_outputs_update (pnode_to_exp % fst) tests_outputs)
                                  in
                                assert (List.length incompleted_pnts' = List.length incompleted_pnts);
                              Left (incompleted_pnts,completed_pns)
                          )
                        (initial_pnts,[])
                    in
                    let pns =
                      deduper
                        (tests_outputs_update pnode_to_exp tests_outputs)
                        (size % pnode_to_exp)
                        pns
                    in
                    (*let (progressed_branches,remaining_branches) =
                      split_by_condition
                        ~f:(fun (_,xs) -> not (List.is_empty xs))
                        integrations_rank_os
                      in
                      let progressed_branches_nodes =
                        List.map
                          ~f:snd
                          progressed_branches
                      in
                      let remaining_branches =
                        List.map
                          ~f:fst
                          remaining_branches
                      in
                      print_endline (string_of_int (List.length progressed_branches_nodes));
                      (*let integrations_ranks_o = distribute_option integrations_rank_os in*)
                      print_endline "NOOO";
                      let all_combos = combinations progressed_branches_nodes in
                      print_endline (List.to_string ~f:(fun (e,_) -> Pp.pp_exp e) relevant_tests);
                      print_endline "ooon";
                      let filtered_combos =
                        List.filter_map
                          ~f:(fun combo ->
                              begin match combo with
                                | (p,pn,e)::t ->
                                  snd @$
                                  List.fold_left
                                    ~f:(fun (pn,pno) (p,pn',e) ->
                                        begin match pno with
                                          | None -> (pn,None)
                                          | Some pn'' ->
                                            if pn = pn' then
                                              (pn,integrate_path p pn'' e)
                                            else
                                              (pn,None)
                                        end)
                                    ~init:(pn,integrate_path p pn e)
                                    t
                                | _ -> failwith "pleaseno"
                              end)
                          all_combos
                      in
                      print_endline (string_of_int (List.length filtered_combos));
                      print_endline "hi";
                      let final_pns =
                        List.filter
                          ~f:(fun pn ->
                              List.for_all
                                ~f:(fun (_,run) -> run (pnode_to_exp pn))
                                relevant_tests)
                          filtered_combos
                      in*)
                    let prior_tests_outputs = prior_tests@relevant_tests_outputs in
                    update_solution_cache t prior_tests_outputs pns;
                    if List.is_empty pns then
                      ((*print_endline "was empty";*) Right [])
                    else
                      Left (pns,next_tests_outputs,prior_tests_outputs)
                in

                (*if not (List.is_empty passing) then
                  Right passing
                  else*)
                  standard_calc ()
                      (*begin match integrations_ranks_o with
                        | None -> Right []
                        | Some integrations_ranks ->
                          let maxes_indices =
                            retrieve_maxes_and_indices
                              integrations_ranks
                              (fun (_,_,f1) (_,_,f2) -> Float.compare f1 f2)
                          in
                          if List.length maxes_indices = 0 then
                            failwith "cannot happen no"
                          else if List.length maxes_indices = 1 then
                            let ((_,pns,f),i) = List.hd_exn maxes_indices in
                            print_endline (Float.to_string f);
                            let pns =
                              deduper
                                (exp_to_output % pnode_to_exp)
                                (size % pnode_to_exp)
                                pns
                            in
                            List.iter
                              ~f:(fun pn -> print_endline (Pp.pp_exp (pnode_to_exp pn)))
                              pns;
                            List.iter
                              ~f:(fun pn -> print_endline (List.to_string ~f:(string_of_pair Pp.pp_exp Bool.to_string) (List.map ~f:(fun (v,run) -> (v,run (pnode_to_exp pn))) tests)))
                              pns;
                            print_endline (string_of_int (List.length pns));
                            let (_,bs) = remove_at_index_exn bs i in
                            let tests =
                              List.filter
                                ~f:(fun (_,run) ->
                                    List.exists
                                      ~f:(fun pn -> not (run (pnode_to_exp pn)))
                                      pns)
                                tests
                            in
                            List.iter
                              ~f:(fun pn -> print_endline (List.to_string ~f:(string_of_pair Pp.pp_exp Bool.to_string) (List.map ~f:(fun (v,run) -> (v,run (pnode_to_exp pn))) tests)))
                              pns;
                            print_endline "next";
                            Left (pns,bs,tests)
                          else
                            failwith "TODO"
                        end*)
                  )
          (initial_pns_tests)
          in*)
        (*let ppeos =
          List.map
            ~f:(fun (pp,rt) ->
                let es =
                  propogate_exps
                    ~short_circuit:false
                    true
                    []
                    rt
                    ~search_matches:false
                in
                let es_sized =
                  List.map
                    ~f:(fun e -> (e,size e))
                    es
                in
                let sorted_sized_es =
                  List.sort
                    ~compare:(fun (_,s1) (_,s2) -> Int.compare s1 s2)
                    es_sized
                in
                begin match sorted_sized_es with
                  | [] -> None
                  | _ ->
                    let sorted_sized_es =
                      List.take
                        sorted_sized_es
                        (Float.to_int (10000. ** (1. /. (Float.of_int (List.length ppaths)))))
                    in
                    let es =
                      List.map
                        ~f:fst
                        sorted_sized_es
                    in
                    Some (pp,es)
                end)
            ppaths
          in
          let ppes_o = Some (List.filter_map ppeos ~f:Fn.id) in
          begin match ppes_o with
          | None -> []
          | Some ppes ->
          (List.concat_map
           ~f:(fun pn ->
               List.map
                 ~f:pnode_to_exp
                 (List.fold_left
                    ~f:(fun pns (pp,es) ->
                        let ans =
                          List.cartesian_filter_map
                            ~f:(integrate_path pp)
                            pns
                            es
                        in
                        if ans = [] then
                          pns
                        else
                          ans)
                    ~init:[pn]
                    ppes))
           pns)*)
    end

(***** }}} *****)

(***** }}} *****)
