open Core
open Utils

let rec generator
    (tc:Context.Types.t)
    (t:Type.t)
    (size:int)
  : Value.t list =
  if size <= 0 then
    []
  else
    let generator_simple t size = generator tc t size in
    begin match t with
      | Named i ->
        generator_simple
          (Context.find_exn tc i)
          size
      | Arrow _ ->
        failwith "cannot do"
      | Tuple ts ->
        let parts = List.partitions (size-1) (List.length ts) in
        let components =
          List.concat_map
            ~f:(fun part ->
                let components =
                  List.map2_exn
                    ~f:(fun t p -> generator_simple t p)
                    ts
                    part
                in
                List.combinations components)
            parts
        in
        List.map ~f:Value.mk_tuple components
      | Mu (v,t) ->
        let tc = Context.set tc ~key:v ~data:t in
        generator tc t size
      | Variant options ->
        List.concat_map
          ~f:(fun (i,t) ->
              List.map
                ~f:(Value.mk_ctor i)
                (generator_simple t (size-1)))
          options
end
