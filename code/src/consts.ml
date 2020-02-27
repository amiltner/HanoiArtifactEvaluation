let use_myth = ref false
let prelude_context = ref false

let synth_result_persistance = ref true
let counterexample_list_persistance = ref true

let synthesis_calls = ref 0
let verification_calls = ref 0
let synthesis_times = ref 0.0
let max_synthesis_time = ref 0.0
let verification_times = ref 0.0
let max_verification_time = ref 0.0
let invariant_size = ref 0

let increment
    (xr : int ref)
  : unit =
  xr := !xr + 1


let time
    (timer : Float.t ref)
    (max_time : Float.t ref)
    (func : unit -> 'a)
  : 'a =
  let initial_time = Core.Time.now () in
  let result = func () in
  let end_time = Core.Time.now () in
  let time_diff = Core.Time.Span.to_ms (Core.Time.diff end_time initial_time) /. 1000. in
  max_time := Core.Float.max time_diff !max_time;
  timer := !timer +. time_diff;
  result

let full_time
    (timer : Float.t ref)
    (max_time : Float.t ref)
    (xr : int ref)
    (func : unit -> 'a)
  : 'a =
  increment xr;
  time timer max_time func

