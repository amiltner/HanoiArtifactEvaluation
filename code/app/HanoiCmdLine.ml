open Core

open Hanoi

(*let _ = let full_spec = ProcessFile.process_full_problem problem in
  let ans =
    Verifiers.QuickCheckVerifier.implication_counter_example
      ~problem:full_spec
      ~pre:(Expr.mk_func ("x",Type.Var "t")
              (Expr.mk_app
                 (Expr.mk_app
                    (Expr.mk_var "and")
                    ((Value.to_exp (Verifiers.QuickCheckVerifier.true_val))))
                 (Value.to_exp (Verifiers.QuickCheckVerifier.true_val))
              )
              )
      ~eval:(Expr.mk_func ("x",Type.Var "t") (Expr.mk_var "x"))
      ~post:full_spec.post
  in
  begin match ans with
    | None -> failwith "Nonegrr"
    | Some anses -> print_endline (string_of_list Value.show anses)
  end*)

module EMIG = MIG.Make (EnumerativeVerifier.T) (ParSynthesizer.T) (EnumerativeLR.T)
module QCMIG = MIG.Make (QuickCheckVerifier.T) (ParSynthesizer.T) (EnumerativeLR.T)
module MythMIG = MIG.Make (EnumerativeVerifier.T) (MythSynthesizer.T) (EnumerativeLR.T)
module AltMIG = MIG_Alternative.Make (EnumerativeVerifier.T) (MythSynthesizer.T) (EnumerativeLR.T)

let read_accum = function
  | None -> "", ""
  | Some filename
    -> let file_chan = Utils.get_in_channel filename in
       let file_data = Stdio.In_channel.input_all file_chan
        in match String.split file_data ~on:'#' with
           | [ accum_types ; accum_annot ] -> (accum_types , accum_annot)
           | _ -> raise (Hanoi.Exceptions.Parse_Exn "bad accumulating annotation")

let main (* nworkers *) accum_file use_fold srp clp smallest50 prelude_context gat ndd conjstr linarb print_data filename () =
  Consts.use_myth := not use_fold;
  Consts.synth_result_persistance := not srp;
  Consts.counterexample_list_persistance := not clp;
  Consts.prelude_context := prelude_context;
  Myth_folds.Consts.generate_and_test := gat;
  Myth_folds.Consts.no_dedup := ndd;
  Log.enable ~msg:"DSInfer" (Some "_log") ;
  let file_chan = Utils.get_in_channel filename in
  let accum_types, accum_annot = read_accum accum_file in
  let problem_string = Prelude.prelude_string ^ accum_types
                     ^ (Stdio.In_channel.input_all file_chan)
                     ^ accum_annot
   in Stdio.In_channel.close file_chan
    ; let unprocessed_problem = Parser.unprocessed_problem
                                  Lexer.token
                                  (Lexing.from_string problem_string)
      in
      let inv =
        if smallest50 then
          (AltMIG.learnInvariant_internal_smallest50 ~unprocessed_problem)
        else if use_fold then
          (EMIG.learnInvariant ~unprocessed_problem)
        else if conjstr then
          (AltMIG.learnInvariant ~unprocessed_problem)
        else if linarb then
          (AltMIG.learnInvariantLinearArbitrary ~unprocessed_problem)
        else
          (MythMIG.learnInvariant ~unprocessed_problem)
      in
      print_endline inv;
      if print_data then
        (print_endline ";";
         print_endline (string_of_int !Consts.synthesis_calls);
         print_endline ";";
         print_endline (string_of_int !Consts.verification_calls);
         print_endline ";";
         print_endline (Float.to_string !Consts.max_synthesis_time);
         print_endline ";";
         print_endline (Float.to_string !Consts.max_verification_time);
         print_endline ";";
         print_endline (Float.to_string !Consts.synthesis_times);
         print_endline ";";
         print_endline (Float.to_string !Consts.verification_times);
         print_endline ";";
         print_endline (string_of_int !Consts.invariant_size);
        )

let spec =
  Command.Spec.(
    empty
    (* +> flag "nworkers" (optional_with_default 4 int) ~doc:" Number of workers" *)
    +> flag "-a" (optional string)
            ~doc:"FILENAME accumulating annotation file"
    +> flag "-use-fold" no_arg
      ~doc:"Use fold as the underlying synthesizer"
    +> flag "-srp" no_arg
      ~doc:"Do not use synth result persistance"
    +> flag "-clp" no_arg
      ~doc:"Do not use counterexample list persistance"
    +> flag "-smallestthirty" no_arg
      ~doc:"run post on smallest 30 elements"
    +> flag "-prelude-context" no_arg
      ~doc:"Use only Prelude as the underlying context"
    +> flag "-gat" no_arg
      ~doc:"Generate and test the synthesized programs"
    +> flag "-no-dedup" no_arg
      ~doc:"Do not perform observational equivalence deduplication"
    +> flag "-conj-str" no_arg
      ~doc:"Synth via conjunctive strengthening"
    +> flag "-linear-arbitrary" no_arg
      ~doc:"Synth via linear arbitrary"
    +> flag "-print-data" no_arg
      ~doc:"print data"
    +> anon ("filename" %: file)
  )

let () =
  Rpc_parallel.start_app
     ~rpc_heartbeat_config:(
       Async.Rpc.Connection.Heartbeat_config.create
         ~timeout:(Time_ns.Span.of_min 30.0)
         ~send_every:(Time_ns.Span.of_sec 15.0)
    )
    (Command.basic_spec spec main
      ~summary: "Infer a representation invariant that is sufficient for proving the correctness of a module implementation.")
