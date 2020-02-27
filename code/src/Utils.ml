open Core

let (%) (f : 'b -> 'c) (g : 'a -> 'b) : 'a -> 'c =
  Fn.compose f g

let get_in_channel = function
  | "-"      -> Stdio.In_channel.stdin
  | filename -> Stdio.In_channel.create filename

module List = struct
  include List

  let cartesian_filter_map ~(f : 'a -> 'b -> 'c option)
                           (l1 : 'a list)
                           (l2 : 'b list)
                           : 'c list =
    rev (fold l1 ~init:[]
              ~f:(fun acc a -> fold l2 ~init:acc
                                    ~f:(fun acc b -> match f a b with
                                                     | None -> acc
                                                     | Some c -> c :: acc)))

  let combinations (type a) (l : a list list) : a list list =
    let rec combinations_internal
        (l : a list list)
        (continuation : a list list -> a list list)
        : a list list =
      match l with
        | [] -> continuation [[]]
        | [x] -> continuation (rev_map ~f:(fun n -> [n]) x)
        | x :: l ->
          combinations_internal
            l
            (fun c ->
                continuation
                  (fold_left x ~init:[]
                             ~f:(fun res n -> rev_append (rev_map ~f:(fun l -> n::l) c) res)))
    in combinations_internal l (fun x -> x)

  let rec partitions (n : int) (k : int) : int list list =
    if n = 0 && k = 0 then
      [[]]
    else if n <= 0 || k <= 0 then
      []
    else if k = 1 then
      [[n]]
    else
      fold_left ~f:(fun res i -> res @ map ~f:(cons i) (partitions (n-i) (k-1)))
                ~init:[]
                (map ~f:((+) 1) (range 0 (n-k+1)))

  let rec fold_until_completion ~f:(f: 'a -> ('a,'b) Either.t) (acc:'a) : 'b =
    match f acc with
      | First acc' -> fold_until_completion ~f acc'
      | Second answer -> answer

  let remove_at_exn (l : 'a list) (i : int) : 'a list =
    if i < 0 || i >= (length l) then l
    else let (first_i_1, i_onwards) = split_n l i
      in first_i_1 @ (drop i_onwards 1)

  let rec zip3
      (l1:'a list)
      (l2:'b list)
      (l3:'c list)
    : ('a*'b*'c) list option =
    begin match (l1,l2,l3) with
      | (h1::t1,h2::t2,h3::t3) ->
        Option.map
          ~f:(fun tl ->
              (h1,h2,h3)::tl)
          (zip3 t1 t2 t3)
      | _ ->
        None
    end

  let zip3_exn
      (l1:'a list)
      (l2:'b list)
      (l3:'c list)
    : ('a * 'b * 'c) list =
    Option.value_exn (zip3 l1 l2 l3)
end

let pair_compare
    (fst_compare:'a -> 'a -> int)
    (snd_compare:'b -> 'b -> int)
    ((x1,x2):('a * 'b))
    ((y1,y2):('a * 'b))
  : int =
  let cmp = fst_compare x1 y1 in
  if (0 = cmp) then
    snd_compare x2 y2
  else
    cmp
