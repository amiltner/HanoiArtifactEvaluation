open Core
open Utils

module T : Verifier.t = struct
  let _MAX_SIZE_T_ = 30
  let _MAX_SIZE_NON_T = 10
  let _MAX_COUNT_INPUT_ = 300
  let _MAX_COUNT_INPUT_TOTAL_ = 2000
  let _MAX_TOTAL_SIZE_ = 45

  (*module TypeToGeneratorDict =
  struct
    module Generators =
    struct
      type t = Expr.t Sequence.t
      [@@deriving ord]

      let hash _ = failwith "dont"
      let hash_fold_t _ = failwith "don't"
      let pp _ = failwith "don't"
      let show _ = failwith "don't"
    end
    module D = DictOf(Type)(Generators)

    type t = D.t * (Type.t -> Expr.t Sequence.t)

    (*let get_val
        ((d,fs):t)
        (t:Type.t)
      : t * Expr.t =
      begin match D.lookup d t with
        | None ->
          let g = fs t in
          let (v,g) = Option.value_exn (Sequence.next g) in
          let d = D.insert d t g in
          ((d,fs),v)
        | Some g ->
          let (v,g) = Option.value_exn (Sequence.next g) in
          let d = D.insert d t g in
          ((d,fs),v)
      end*)

    let create
        (fs:(Type.t -> Expr.t Sequence.t))
      : t =
      (D.empty,fs)
    end*)

  let rec elements_of_type_and_size
      (tc:Context.Types.t)
      (t:Type.t)
      (s:int)
    : Expr.t list =
    if s <= 0 then
      []
    else
      let elements_simple = elements_of_type_and_size tc in
      begin match t with
        | Named i ->
          elements_simple (Context.find_exn tc i) s
        | Arrow _ ->
          failwith "Will do if necessary..."
        | Tuple ts ->
          let parts = List.partitions (s-1) (List.length ts) in
          let components =
            List.concat_map
              ~f:(fun part ->
                  let components =
                    List.map2_exn
                      ~f:(fun t p -> elements_simple t p)
                      ts
                      part
                  in
                  List.combinations components)
              parts
          in
          List.map ~f:Expr.mk_tuple components
        | Mu (v,t) ->
          let tc = Context.set tc ~key:v ~data:t in
          elements_of_type_and_size tc t s
        | Variant options ->
          List.concat_map
            ~f:(fun (i,t) ->
                List.map
                  ~f:(Expr.mk_ctor i)
                  (elements_simple t (s-1)))
            options
      end

  let elements_of_type_and_size_unit
      (tc:Context.Types.t)
      (t:Type.t)
      (s:int)
    : (unit * Expr.t) list =
    List.map
      ~f:(fun e -> ((),e))
      (elements_of_type_and_size tc t s)


  let elements_of_type_to_size
      (tc:Context.Types.t)
      (t:Type.t)
      (max_size:int)
    : Expr.t list =
    List.concat_map
      ~f:(fun s -> elements_of_type_and_size tc t s)
      (List.range 1 (max_size+1))


  (*let elements_of_type_to_size_unit
      (tc:Context.Types.t)
      (t:Type.t)
      (max_size:int)
    : (unit * Expr.t) list =
    List.map
      ~f:(fun r -> ((),r))
      (elements_of_type_to_size tc t max_size)*)

  module TypeSet = Set.Make(Type)

  let contains_any
      (tc:Context.Types.t)
      (desired_t:Type.t)
      (t:Type.t)
    : bool =
    let rec contains_any
        (tc:Context.Types.t)
        (desired_t:Type.t)
        (checked:TypeSet.t)
        (t:Type.t)
      : bool =
      if TypeSet.mem checked t then
        false
      else if Type.equal t desired_t then
        true
      else
        let checked = TypeSet.add checked t in
        let contains_any_simple = contains_any tc desired_t checked in
        begin match t with
          | Named v ->
            begin match Context.find tc v with
              | Some t -> contains_any_simple t
              | None -> false
            end
          | Arrow (t1,t2) ->
            contains_any_simple t1 || contains_any_simple t2
          | Tuple ts ->
            List.exists ~f:contains_any_simple ts
          | Mu (i,t) ->
            let tc = Context.set tc ~key:i ~data:t in
            contains_any tc desired_t checked t
          | Variant branches ->
            List.exists ~f:contains_any_simple (List.map ~f:snd branches)
        end
    in
    contains_any tc desired_t TypeSet.empty t

  let rec extract_typed_subcomponents
      (tc:Context.Types.t)
      (desired_t:Type.t)
      (t:Type.t)
      (v:Value.t)
    : Value.t list =
    let extract_typed_subcomponents_simple = extract_typed_subcomponents tc desired_t in
    if Type.equal t desired_t then
      [v]
    else
      begin match (t,v) with
        | (Tuple ts, Tuple vs) ->
          List.concat_map
            ~f:(fun (t,v) -> extract_typed_subcomponents_simple t v)
            (List.zip_exn ts vs)
        | (Variant branches, Ctor (c,v)) ->
          let t =
            List.Assoc.find_exn ~equal:String.equal branches c
          in
          extract_typed_subcomponents_simple t v
        | (Named i, _) ->
          begin match Context.find tc i with
            | None -> []
            | Some t -> extract_typed_subcomponents_simple t v
          end
        | (Mu (i,t), _) ->
          let tc = Context.set tc ~key:i ~data:t in
          extract_typed_subcomponents tc desired_t t v
        | (Arrow _, _) -> failwith "arrows not currently supported"
        | _ -> failwith "Something went wrong"
      end

  let rec extract_args
      (t:Type.t)
    : Type.t list * Type.t =
    begin match t with
      | Arrow (t1,t2) ->
        let (ts,tres) = extract_args t2 in
        (t1::ts,tres)
      | _ -> ([],t)
    end

  let make_evaluators_to_size
      (type a)
      ~(generator:Type.t -> int -> (a * Expr.t) list)
      ~(problem:Problem.t)
      ~(eval:Expr.t)
      ~(args:Type.t list)
      ~(size:int)
    : ((a * Expr.t * Type.t) list * Value.t) Sequence.t =
    (* Eagerly returning all expressions till size "size" ... *)
    let args_sizes =
      List.map
        ~f:(fun a ->
            let size = if Type.equal a Type._t then size else _MAX_SIZE_NON_T in
            List.map
              ~f:(fun s -> (a,s))
              (List.range 1 size))
        args
    in
    let sizes_combinations =
      List.sort
        ~compare:(fun cs1 cs2 ->
            let len1 = List.fold ~f:(+) ~init:0 (List.map ~f:snd cs1) in
            let len2 = List.fold ~f:(+) ~init:0 (List.map ~f:snd cs2) in
            Int.compare len1 len2)
        (List.combinations args_sizes)
    in
    let sizes_combinations_sequences =
      Sequence.of_list
        sizes_combinations
    in
    let all_args =
      Sequence.take
        (Sequence.concat_map
           ~f:(fun tss ->
               let total_size =
                 List.fold_left
                   ~f:(fun acc (_,x) -> acc + x)
                   ~init:0
                   tss
               in
               if total_size > _MAX_TOTAL_SIZE_ then
                 Sequence.empty
               else
                 let tss_a =
                   List.map
                     ~f:(fun (t,s) ->
                         List.map
                           ~f:(fun (d,e) -> (d,e,t))
                           (List.take
                              (generator t s)
                              _MAX_COUNT_INPUT_))
                     tss
                 in
                 Sequence.of_list (List.combinations tss_a))
           sizes_combinations_sequences)
        _MAX_COUNT_INPUT_TOTAL_
    in
    (*let args_possibilities =
      List.map
        ~f:(fun t ->
            List.map
              ~f:(fun (d,e) -> (d,e,t))
              (generator t size))
        args
    in
      let all_args = List.combinations args_possibilities in*)
    (*let args_sized =
      List.map
        ~f:(fun args -> (args,(List.fold_left ~f:(+) ~init:0 (List.map ~f:(Expr.size % snd3) args))))
        all_args
    in
    let all_args_sized_ordered =
      List.sort
        ~compare:(fun (_,s1) (_,s2) -> Int.compare s1 s2)
        args_sized
    in
      let all_args = List.map ~f:fst all_args_sized_ordered in*)
    Sequence.map
      ~f:(fun args ->
          (args,
           Eval.evaluate_with_holes_basic
                  ~tc:problem.tc
             ~eval_context:problem.eval_context
             (List.fold_left
                ~f:(fun acc (_,e,_) -> Expr.mk_app acc e)
                ~init:eval
                args
             )))
      all_args


  let fully_eval_exp_to_size
      (type a)
      ~(generator:Type.t -> int -> (a * Expr.t) list)
      ~(problem:Problem.t)
      ~(eval:Expr.t)
      ~(eval_t:Type.t)
      ~(size:int)
    : ((a * Expr.t * Type.t) list * Value.t) Sequence.t =
    (* Eagerly returning all expressions till size "size" ... *)
    let (args,_) = extract_args eval_t in
    make_evaluators_to_size
      ~generator
      ~problem
      ~eval
      ~args
      ~size

  let equiv_false
      ~(problem:Problem.t)
      ~cond:(cond:Expr.t)
    : bool =
    let cond_t = Type.mk_arrow (Type._t) (Type._bool) in
    (*let generators
        (t:Type.t)
      : Expr.t Sequence.t =
       let g = generator_of_type problem.tc t in
       QC.g_to_seq g
      in*)
    (*let gen = TypeToGeneratorDict.create generators*)
     try Sequence.fold
           (fully_eval_exp_to_size
              ~generator:(elements_of_type_and_size_unit problem.tc)
              ~problem
              ~eval:cond
              ~eval_t:cond_t
              ~size:_MAX_SIZE_T_)
           ~init:true
           ~f:(fun _ (_,res) -> if Value.equal res Value.mk_true
                then true else raise Caml.Exit)
     with Caml.Exit -> false
  (* fold_until_completion
       ~f:(fun (i,gen) ->
           if i > num_checks then
             Right true
           else
             let (_,res,gen) =
               make_random_evaluator
                 ~problem
                 ~eval:cond
                 ~eval_t:cond_t
                 ~gen
             in
             if is_equal @$ Value.compare res Value.mk_true then
               Right false
             else
               Left (i+1,gen))
       (0,gen) *)

  let ensure_uf_to_size
      (type a)
      ~(generator:Type.t -> int -> (a * Expr.t) list)
      ~(problem:Problem.t)
      ~post:((post_quants,post_expr):UniversalFormula.t)
      ~(size:int)
    : (a * Expr.t * Type.t) list option =
    let args = List.map ~f:snd post_quants in
    let eval =
      List.fold_right
        ~f:(fun a acc -> Expr.mk_func a acc)
        ~init:post_expr
        post_quants
    in
    let evaled =
      make_evaluators_to_size
        ~generator
        ~problem
        ~eval
        ~args
        ~size
    in
    Sequence.find_map
      ~f:(fun (e,v) ->
          if Value.equal v Value.mk_true then
            None
          else if Value.equal v Value.mk_false then
            Some e
          else
            failwith (Value.show v))
      evaled

  let true_on_examples_full
      ~(problem:Problem.t)
      ~(examples:Value.t list)
      ~(eval:Expr.t)
      ~(eval_t:Type.t)
      ~(post:UniversalFormula.t)
      ~(size:int)
    : ((Expr.t * Type.t) list * Value.t) list option =
    let desired_t = Type._t in
    let (args_t,result_t) = extract_args eval_t in
    if (List.length examples = 0
        && List.mem ~equal:Type.equal args_t desired_t)
    || not (contains_any problem.tc desired_t result_t) then
      None
    else
      let sized_exs =
        List.map
          ~f:(fun v ->
              let e = Value.to_exp v in
              (e, Expr.size e))
          examples
      in
      let generator
          (t:Type.t)
          (size:int)
        : (unit * Expr.t) list =
        if Type.equal t desired_t then
          List.filter_map
            ~f:(fun (x,s) -> if s = size then Some ((),x) else None)
            sized_exs
        else
          List.map ~f:(fun x -> ((),x)) (elements_of_type_and_size problem.tc t size)
      in
      let results =
        fully_eval_exp_to_size
          ~generator
          ~problem
          ~eval
          ~eval_t
          ~size
      in
      let split_sized_results =
        Sequence.concat_map
          ~f:(fun (uets,res) ->
              let et = List.map ~f:(fun (_,e,t) -> (e,t)) uets in
              Sequence.of_list
                (List.map
                   ~f:(fun v ->
                       let e = Value.to_exp v in
                       let s = Expr.size e in
                       ((et,v),e,s))
                   (extract_typed_subcomponents
                      problem.tc
                      desired_t
                      result_t
                      res)))
          results
      in
      let res = Sequence.to_list split_sized_results in
      let res = List.dedup_and_sort ~compare:(fun (_,e1,_) (_,e2,_) -> Expr.compare e1 e2) res in
      let generator
          (t:Type.t)
          (size:int)
        : (((Expr.t * Type.t) list * Value.t) option * Expr.t) list =
        if Type.equal t desired_t then
          List.filter_map
            ~f:(fun (etv,e,s) -> if s = size then Some (Some etv,e) else None)
            res
        else
          List.map ~f:(fun x -> (None,x)) (elements_of_type_and_size problem.tc t size)
      in
      let negative_example_o =
        ensure_uf_to_size
          ~generator
          ~problem
          ~post
          ~size
      in
      Option.map
        ~f:(fun negative_example ->
            List.filter_map
              ~f:(fun (et_o,_,t) ->
                  if Type.equal t desired_t then
                    Some (Option.value_exn et_o)
                  else
                    None)
              negative_example)
        negative_example_o
  (*let arged_split_res =
        List.map
          ~f:(fun r -> (args,Value.to_exp r))
          split_res
      in
      let i = i + List.length split_res in
      let uf_types_seqs
        : (Expr.t * string * Type.t) Sequence.t list =
        List.map
          ~f:(fun (i,t) ->
              let gen =
                if is_equal (Type.compare (Type.mk_var "t") t) then
                  result_gen
                else
                  generator_of_type problem.tc t
              in
              let seq = QC.g_to_seq gen in
              Sequence.map
                ~f:(fun e -> (e,i,t))
                seq)
          post_quants
      in
      let ce_option =
        fold_until_completion
          ~f:(fun (uf_types_seqs,i) ->
              if i = 100 then
                Right None
              else
                let (exps_names_types,uf_types_seqs) =
                  List.fold_right
                    ~f:(fun seq (exps_names,uf_types_seqs) ->
                        let (exp_name,seq) = Option.value_exn (Sequence.next seq) in
                        (exp_name::exps_names,seq::uf_types_seqs))
                    ~init:([],[])
                    uf_types_seqs
                in
                let (names_exps,exps_types) =
                  List.unzip @$
                  List.map
                    ~f:(fun (exp,name,typ) -> ((name,exp),(exp,typ)))
                    exps_names_types
                in
                let post_held =
                  is_equal @$
                  Value.compare
                    Value.mk_true
                    (Eval.evaluate_with_holes ~eval_context:(problem.eval_context@names_exps) post_expr)
                in
                if post_held then
                  Left (uf_types_seqs,i+1)
                else
                  let relevant =
                    List.filter_map
                      ~f:(fun (e,t) ->
                          if Type.equal desired_t t then
                            Some e
                          else
                            None)
                      exps_types
                  in
                  Right (Some relevant))
          (uf_types_seqs,0)
      in
      Option.map ~f:List.hd_exn @$
      Option.map
        ~f:(List.map ~f:Value.from_exp_exn)
        ce_option*)

  let true_on_examples
      ~(problem:Problem.t)
      ~(examples:Value.t list)
      ~(eval:Expr.t)
      ~(eval_t:Type.t)
      ~(post:UniversalFormula.t)
    : Value.t list =
    Option.value
      ~default:[]
      (Option.map
         ~f:(List.map ~f:snd)
         (true_on_examples_full
            ~problem
            ~examples
            ~eval
            ~eval_t
            ~post
            ~size:_MAX_SIZE_T_))

  let implication_counter_example
      ~problem:(problem:Problem.t)
      ~pre:(pre:Expr.t)
      ~eval:(eval:Expr.t)
      ~(eval_t:Type.t)
      ~(post:UniversalFormula.t)
    : Value.t list =
    let desired_t = Type._t in
    let (args_t,result_t) = extract_args eval_t in
    if not (contains_any problem.tc desired_t result_t) then
      []
    else
      Option.value
        ~default:[]
        (List.fold
           ~f:(fun ans_o s ->
               begin match ans_o with
                 | Some ans -> Some ans
                 | None ->
                   let examples =
                     if List.mem ~equal:Type.equal args_t desired_t then
                       List.filter_map
                         ~f:(fun e ->
                             let pre_e_app =
                               Expr.mk_app
                                 pre
                                 e
                             in
                             let v = Eval.evaluate_with_holes_basic ~tc:problem.tc ~eval_context:problem.eval_context pre_e_app in
                             if Value.equal v Value.mk_true then
                               Some (Value.from_exp_exn e)
                             else if Value.equal v Value.mk_false then
                               None
                             else
                               failwith "incorrect evaluation")
                         (elements_of_type_to_size problem.tc desired_t s)
                     else
                       []
                   in
                   let results =
                     true_on_examples_full
                       ~problem
                       ~examples
                       ~eval
                       ~eval_t
                       ~post
                       ~size:s
                   in
                   Option.map
                     ~f:(List.concat_map
                           ~f:(fun (ets,_) ->
                               List.filter_map
                                 ~f:(fun (e,t) ->
                                     if Type.equal t desired_t then
                                       Some (Value.from_exp_exn e)
                                     else
                                       None)
                                 ets))
                     results
               end)
           ~init:None
           [_MAX_SIZE_T_ / 2; Float.to_int (Float.of_int (_MAX_SIZE_T_) /. 1.25) ; _MAX_SIZE_T_])
end
