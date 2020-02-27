module OurLog = Log

open Async
open Core

module Log = OurLog

open Utils

module T : Synthesizer.t = struct
  let synth_core ~(problem:Problem.t)
                 ~(testbed:TestBed.t)
                 ~(accumulator:Type.t)
    : Expr.t list =
    if Type.equal accumulator Type._unit then
      snd (MythSynthesizer.T.synth
        ~problem
        ~testbed)
    else
    let end_type = Type.mk_tuple [Type._bool ; accumulator] in
    let pos_examples = List.map ~f:(fun v -> (Value.to_exp v, Expr.mk_true_exp)) testbed.pos_tests in
    let neg_examples = List.map ~f:(fun v -> (Value.to_exp v, Expr.mk_false_exp)) testbed.neg_tests in
    let examples = pos_examples @ neg_examples in
    let (decls,_,_,_) =
      DSToMyth.convert_problem_examples_type_to_myth
        problem
        examples
        None
    in
    let (_,gamma) =
      Myth_folds.Typecheck.Typecheck.check_decls
        Myth_folds.Sigma.Sigma.empty
        Myth_folds.Gamma.Gamma.empty
        decls
    in
    let foldable_t = Context.get_foldable_t problem.tc end_type in
    let fold_creater =
      Context.convert_foldable_to_full
        problem.tc
        end_type
    in
    let (ds,mi,ms,uf,acc) = problem.unprocessed in
    let unprocessed =
      (ds
      ,mi @ [ Declaration.type_dec (Id.mk_prime "t") foldable_t
            ; Declaration.expr_dec "convert" fold_creater ]
      ,ms
      ,uf
      ,acc)
    in
    let problem = Problem.process unprocessed in
    if (List.length examples = 0) then
      [Expr.mk_constant_false_func (Type._t)]
    else
      let (decls,myth_examples,t,end_type_myth) =
        DSToMyth.convert_problem_examples_type_to_myth
          problem
          examples
          (Some end_type)
      in
      let (sigma,_) =
        Myth_folds.Typecheck.Typecheck.check_decls
          Myth_folds.Sigma.Sigma.empty
          Myth_folds.Gamma.Gamma.empty
          decls
      in
      let env = Myth_folds.Eval.gen_init_env decls in
      (*let env = Myth_folds.Sigma.Sigma.add_ctors_env env sigma in
        let gamma = Myth_folds.Gamma.Gamma.add_ctors gamma sigma in*)
      let desired_t = Type.mk_arrow (Type._t) (Type._bool) in
      let (extractor,replacer) = Context.convert_foldable_and_res_to_folded_myth problem.tc in
      let tests_outputs : Myth_folds.Lang.exp Myth_folds.Rtree.tests_outputs =
        List.map
          ~f:(fun (input,expected_output) ->
              let replacer = replacer input in
              let expected_output_value = Myth_folds.Eval.eval env expected_output in
              (input
              ,expected_output
              ,(fun e vs ->
                 let es = List.map ~f:Myth_folds.Lang.value_to_exp vs in
                 let input = replacer es in
                 (*let evaler = Myth_folds.Lang.create_exp (Myth_folds.Lang.EApp (Myth_folds.Lang.create_exp (EVar "convert"), e)) in*)
                 let (output,is_real) =
                   try
                     let ans =
                       Myth_folds.Eval.eval
                         env
                         ((Myth_folds.Lang.create_exp (Myth_folds.Lang.EApp(e,input))))
                     in
                     (Some ans,true)
                   with
                   | Myth_folds.Eval.Eval_error _ -> (None,true)
                   | Myth_folds.Eval.Extr_error v -> (Some v,false)
                 in
                 let correct =
                   is_real &&
                   begin match output with
                     | None -> false
                     | Some v ->
                       begin match (Myth_folds.Lang.node v) with
                         | (Myth_folds.Lang.VTuple vs) ->
                           0 = Myth_folds.Lang.compare_value expected_output_value (List.hd_exn vs)
                         | _ -> false
                       end
                   end
                 in
                 (correct, output))))
          myth_examples
      in
      (*Some [(
                     let evaler = Myth_folds.Lang.EApp (EVar "convert", e) in
                     let (real_output,output) =
                       try
                         (true
                         ,Some (Myth_folds.Eval.eval
                                  env
                                  (Myth_folds.Lang.EApp(evaler,input))))
                       with
                         Myth_folds.Eval.Eval_error _ -> (true,None)
                       | Myth_folds.Eval.Extr_error v -> (false, Some v)
                     in
                     let correct =
                       real_output &&
                       begin match output with
                         | Some (Myth_folds.Lang.VTuple vs) ->
                           print_endline (Myth_folds.Pp.pp_value (Myth_folds.Lang.VTuple vs));
                           let expected_value = Myth_folds.Eval.eval env expected_output in
                           print_endline (Myth_folds.Pp.pp_value expected_value);
                           List.hd_exn vs = Myth_folds.Eval.eval env expected_output
                         | None -> false
                         | _ -> failwith "unexpected"
                       end
                     in
                     (output,correct)
                  )])
            )
          myth_examples
                  in*)
      (*let correct_check =
        List.map
          ~f:(fun (e1,e2) ->
              (e1,fun e ->
                let evaler = Myth_folds.Lang.EApp (EVar "convert", e) in
                try
                   let ans =
                     Myth_folds.Eval.eval
                       env
                       (Myth_folds.Lang.EProj
                          (1
                          ,Myth_folds.Lang.EApp(evaler,e1)))
                   in
                   ans = Myth_folds.Eval.eval env e2
                 with
                 | Myth_folds.Eval.Eval_error _ -> false
                ))
          myth_examples
          (*let total_correct = List.fold_left ~f:(+) ~init:0 corrects in
              let total = List.length corrects in
              (*print_endline (Float.to_string ((Float.of_int total_correct) /. (Float.of_int total)));*)
                (Float.of_int total_correct) /. (Float.of_int total)*)
        in*)
      (*let to_outputs =
        fun e ->
          let evaler = Myth_folds.Lang.EApp (EVar "convert", e) in
          Myth_folds.Rtree.Output.create
            [Some (List.map
                     ~f:(fun (input,_) ->
                         try
                           Some
                             (Myth_folds.Eval.eval
                                env
                                (Myth_folds.Lang.EApp(evaler,input)))
                         with
                           Myth_folds.Eval.Eval_error _ -> None
                         | Myth_folds.Eval.Extr_error v -> Some v)
                     myth_examples)]
        in*)
      List.map
        ~f:(fun me ->
            let e = MythToDS.convert_expr me in
            let e = Typecheck.align_types desired_t e in
            let full_e = Expr.mk_app fold_creater e in
            Expr.mk_func
              ("x",Type._t)
              (Expr.mk_proj 0
                 (Expr.mk_app full_e (Expr.mk_var "x"))))
        (Myth_folds.Synth.synthesize
           sigma
           env
           (Myth_folds.Rtree.create_rtree
              sigma
              gamma
              env
              (TArr (t,end_type_myth))
              0
              true)
           tests_outputs
           extractor
           replacer)

  module Worker = struct
    module T = struct
      module Input = struct
        type t_acc = ExistingType of Type.t
                   | DerivedVariant of (Id.t * Type.t)
        [@@deriving bin_io, show]

        type t = {
          problem : Problem.t ;
          testbed : TestBed.t ;
          accumulator : t_acc ;
        }
        [@@deriving bin_io]
      end

      module Output = struct
        type t =
          Type.t option * Expr.t list
        [@@deriving bin_io]
      end

      type 'worker functions = {
        synth : ('worker, Input.t, Output.t) Rpc_parallel.Function.t
      }

      module Worker_state = struct
        type init_arg = unit [@@deriving bin_io]
        type t = unit
      end

      module Connection_state = struct
        type init_arg = unit [@@deriving bin_io]
        type t = unit
      end

      module Functions (C : Rpc_parallel.Creator
                            with type worker_state := Worker_state.t
                             and type connection_state := Connection_state.t) =
      struct
        let synth_impl ~worker_state:() ~conn_state:() (input : Input.t) : Output.t Deferred.t =
          return (match input.accumulator with
                  | ExistingType accumulator
                    -> (Some accumulator
                       ,synth_core ~problem:input.problem
                                  ~testbed:input.testbed
                                  ~accumulator)
                  | DerivedVariant (acc_name, acc_type)
                    -> let d = Declaration.type_dec acc_name acc_type in
                       let (ds,mi,ms,uf,acc) = input.problem.unprocessed in
                       let unprocessed = (ds @ [d], mi, ms, uf, acc) in
                       let problem = Problem.process unprocessed
                        in (Some acc_type
                           ,synth_core ~problem
                                      ~testbed:input.testbed
                                      ~accumulator:(Type.mk_named acc_name)))

        let synth = C.create_rpc ~f:synth_impl
                                 ~bin_input:Input.bin_t
                                 ~bin_output:Output.bin_t
                                 ()

        let functions = { synth }
        let init_worker_state () = Deferred.unit
        let init_connection_state ~connection:_ ~worker_state:_ = return
      end
    end

    include Rpc_parallel.Make (T)
  end

  let synth ~(problem : Problem.t)
            ~(testbed : TestBed.t)
            : Type.t option * Expr.t list =
    match problem.accumulator with
    | Some accumulator -> (Some accumulator, synth_core ~problem ~testbed ~accumulator)
    | None -> begin
        let extract_result conns_procs_def_results =
          match%bind conns_procs_def_results with
          | [] -> return (None, [])
          | conns_procs_def_results
            -> if conns_procs_def_results = [] then return (None, [])
               else begin
                 let conns_procs, def_results = List.unzip conns_procs_def_results in
                 let rec helper (def_results : Worker.T.Output.t Or_error.t Deferred.t list)
                                : (Type.t option * Expr.t list) Deferred.t =
                   if List.for_all def_results ~f:(fun dr -> Deferred.is_determined dr
                                                          && Or_error.is_error (Deferred.value_exn dr))
                   then begin
                     List.iter def_results ~f:(fun [@warning "-8"] dr -> match Deferred.value_exn dr with Error e -> Log.error (lazy (Error.to_string_hum e))) ;
                     return (None, [])
                   end
                   else begin
                     let determined, undetermined = List.partition_tf def_results ~f:Deferred.is_determined
                      in match List.filter_map determined ~f:(Or_error.ok % Deferred.value_exn) with
                         | [] -> let%bind _ = Deferred.any undetermined in helper undetermined
                         | res :: _
                           -> List.iter conns_procs
                                        ~f:(fun (c,p) -> ignore (Worker.Connection.close c)
                                                       ; ignore (Signal.(send kill (`Pid (Process.pid p))))
                                                       ; ignore (Process.wait p))
                            ; return res
                   end
                 in let%bind _ = Deferred.any def_results in helper def_results
               end
        in
        let _, _, (mod_type, mod_vals), _, _ = problem.unprocessed in
        let type_names =
          List.fold_left mod_vals ~init:[]
                         ~f:(fun acc (_, t) -> Type.(fold t ~arr_f:List.append
                                                            ~tuple_f:List.concat
                                                            ~mu_f:(fun _ _ -> [])
                                                            ~variant_f:(List.concat % (List.map ~f:snd))
                                                            ~name_f:(function "bool" -> []
                                                                            | n -> if n = mod_type || String.is_suffix ~suffix:"option" n
                                                                                   then []
                                                                                   else [n]))
                                             @ acc)
        in
        let type_names =
          match Context.find_exn problem.tc mod_type with
          | Named n -> n :: type_names
          | _ -> failwith "Module type `t` must be a single Named type."
        in
        let type_names =
          let open Worker.T.Input
           in (ExistingType Type._unit)
           :: (List.fold_left
                 ~init:[]
                 (List.dedup_and_sort ~compare:String.compare type_names)
                 ~f:(fun acc n -> ExistingType (Type.mk_named n) 
                               :: DerivedVariant (
                                    "__" ^ n ^ "_option__",
                                    Variant [
                                      ("D__None_" ^ n, Type._unit) ;
                                      ("D__Some_" ^ n, Type.mk_named n)
                                    ])
                               :: DerivedVariant (
                                    "__" ^ n ^ "_pair_option__",
                                    Variant [
                                      ("D__P_None_" ^ n, Type._unit) ;
                                      ("D__P_Some_" ^ n, Type.(mk_tuple [mk_named n ; mk_named n]))
                                    ])
                               :: acc))
        in
        Log.info (lazy ("Spinning " ^ (Int.to_string (List.length type_names))
                       ^ " workers for accumulator types:")) ;
        List.iter type_names ~f:(fun t -> Log.info (lazy ("  > "
                                                         ^ (Worker.T.Input.show_t_acc t)))) ;
        let conns_procs_def_results =
              List.map type_names
                ~f:(fun t -> let%map conn, proc =
                               Worker.spawn_in_foreground_exn
                                 ~shutdown_on:Disconnect
                                 ~connection_state_init_arg:()
                                 ~on_failure:Error.raise
                                 () in
                             let def_res = Worker.Connection.run
                                             ~f:Worker.functions.synth
                                             ~arg:{ problem
                                                  ; testbed
                                                  ; accumulator = t
                                                  }
                                             conn
                              in ((conn, proc), def_res))
         in match Thread_safe.block_on_async
                    (fun () -> extract_result (Deferred.all conns_procs_def_results))
            with Ok res    -> res
               | Error exn -> Log.error (lazy (Exn.to_string exn))
                            ; Log.error (lazy (Printexc.get_backtrace ()))
                            ; (None, [])
    end
end
