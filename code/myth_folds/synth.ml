open Core
open Consts
open Lang
open Rtree
open Sigma

type synth_step =
  | SynthSaturate of float      (* Try to saturate e-guesses *)
  | SynthGrowMatches            (* Increase the depth of matches *)
  | SynthGrowScrutinees  (* Grow the scrutinees of all matches *)

type synth_plan = synth_step list

let standard_synth_plan : synth_plan =
  [
    SynthGrowMatches
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthGrowScrutinees
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthGrowScrutinees
  ; SynthSaturate 0.24
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees
  ; SynthSaturate 0.25
  ; SynthGrowMatches
  ; SynthSaturate 0.25
  ; SynthGrowScrutinees
  ; SynthSaturate 0.25
  ]

let saturate_guesses (timeout:float) ?short_circuit:(sc = true) (s:Sigma.t) (env:env) (t:rtree) =
  let rec update n =
    if n <= !max_eguess_size then begin
      Timing.record
        ~label:"saturate_guesses::update_exps"
        ~action:(fun _ -> update_exps ~short_circuit:sc timeout s env t);
      (*Timing.record
        ~label:"saturate_guesses::propogate_exps"
        ~action:(fun _ -> propogate_exps ~short_circuit:sc condition t |> ignore);*)
      update (n+1)
    end
  in
    update 1

let execute_synth_step
    (s:Sigma.t)
    (env:env)
    (ts:rtree list)
    (ss:synth_step)
    (tests_outputs:exp tests_outputs)
    (extractor:exp -> exp list)
    (replacer:exp -> exp list -> exp)
  : exp list * rtree list =
  (*reset_timeouts t;
  begin match st with
  | SynthSaturate timeout -> begin
      do_if_verbose (fun _ ->
        printf "Saturating E-guesses (timeout = %.2f)...\n%!" timeout);
      Timing.record
        ~label:"synth::saturate_guesses"
        ~action:(fun _ -> saturate_guesses ~short_circuit:false timeout s env t)
    end
  | SynthGrowMatches -> begin
      do_if_verbose (fun _ -> printf "Growing matches...\n%!");
      Timing.record
        ~label:"synth::grow_matches"
        ~action:(fun _ -> grow_matches s env t)
    end
  | SynthGrowScrutinees k -> begin
      do_if_verbose (fun _ -> printf "Growing scrutinees by %d...\n%!" k);
      Timing.record
        ~label:"synth::grow_scrutinees"
        ~action:(fun _ -> grow_scrutinees s env k t)
    end
    end;*)
  (*do_if_verbose (fun _ -> printf "%s\n%!" (Rtree.pp_rtree t));*)
  do_if_verbose (fun _ ->
      printf "Saturating E-guesses and propogating...\n%!");
  (*Timing.record
    ~label:"synth::saturate_guesses"
    ~action:(fun _ -> List.iter ~f:(fun t -> saturate_guesses 0.25 ~short_circuit:false s env t) ts);*)
  let es =
    Timing.record
      ~label:"synth::propogate_exps"
      ~action:(fun _ ->
          List.foldi
            ~f:(fun i es t ->
                begin match es with
                  | [] ->
                    magic_num := i;
                    do_if_verbose (fun _ -> print_endline ("number " ^ string_of_int i));
                    saturate_guesses 0.5 ~short_circuit:false s env t;
                    propogate_exps ~short_circuit:false false tests_outputs ~search_matches:true extractor replacer t
                  | _ -> es
                end)
            ~init:[]
            ts)
  in
  (*assert (List.for_all ~f:(has_passing_capabilities tests_outputs) es);*)
  (*let es =
    List.filter
      ~f:(has_passing_capabilities tests_outputs)
      es
    in*)
  (*let es =
    List.map ~f:app_capital_to_ctor es
    in*)
  if List.is_empty es then
    begin match ss with
      | SynthGrowMatches ->
        (es, (do_if_verbose (fun _ -> printf "Growing matches...\n%!");
              ts@(List.concat_map ~f:(fun t -> generate_matches tests_outputs s env t) ts)))
      | SynthSaturate _ ->
        do_if_verbose (fun _ -> printf "Increasing EGuess Size...\n%!");
        max_eguess_size := !max_eguess_size+2;
        (es,  ts)
      | SynthGrowScrutinees ->
        do_if_verbose (fun _ -> printf "Increasing Scrutinee Size...\n%!");
        scrutinee_size_lim := !scrutinee_size_lim+2;
        (es, ts)
    end
  else
    (do_if_verbose (fun _ -> printf "found...\n%!");
     (es,[]))
(*let es_s =
  List.map
    ~f:(fun e -> (e,size e))
    es
  in
  let es_s =
  List.sort
    ~compare:(fun (_,s1) (_,s2) -> Int.compare s1 s2)
    es_s
  in
  begin match es_s with
  | [] -> None
  | (e,_) :: _ -> Some e
  end*)

let rec execute_synth_plan
    (s:Sigma.t)
    (env:env)
    (ts:rtree list)
    (plan:synth_plan)
    (tests_outputs:exp tests_outputs)
    (extractor:exp -> exp list)
    (replacer:exp -> exp list -> exp)
  : exp list =
  match plan with
  | [] -> []
  | st :: plan ->
    begin match execute_synth_step s env ts st tests_outputs extractor replacer with
      | ([],ts) -> execute_synth_plan s env ts plan tests_outputs extractor replacer
      | (es,_) -> es
    end

let synthesize
    (s:Sigma.t)
    (env:env)
    (t:rtree)
    (tests_outputs:exp tests_outputs)
    (extractor:exp -> exp list)
    (replacer:exp -> exp list -> exp)
  : exp list =
  verbose_mode := true;
  eval_lookup_tables := false;
  execute_synth_plan s env [t] standard_synth_plan tests_outputs extractor replacer
