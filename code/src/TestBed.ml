open Core

open Exceptions

type t = {
  neg_tests : Value.t list ;
  pos_tests : Value.t list ;
} [@@deriving bin_io, show]

let create_positive pos_tests : t =
  { pos_tests = List.dedup_and_sort ~compare:Value.compare pos_tests
  ; neg_tests = [] }

let contains_test ~(testbed : t) (test : Value.t) : bool =
  List.exists testbed.pos_tests ~f:(Value.equal test) ||
  List.exists testbed.neg_tests ~f:(Value.equal test)

let contains_neg_test
    ~(testbed : t)
  : Value.t -> bool =
  List.mem ~equal:Value.equal testbed.neg_tests

let add_pos_test ~(testbed : t) (test : Value.t) : t =
  if List.exists testbed.pos_tests ~f:(Value.equal test) then
    testbed
  else if List.exists testbed.neg_tests ~f:(Value.equal test) then
    raise (Ambiguous_Test ("New POS test ("
                          ^ Value.show test ^ ") already already exists in NEG set!"))
  else { testbed with
         pos_tests = test :: testbed.pos_tests }

let add_neg_test ~(testbed : t) (test : Value.t) : t =
  if List.exists testbed.neg_tests ~f:(Value.equal test) then
    testbed
  else if List.exists testbed.pos_tests ~f:(Value.equal test) then
    raise (Ambiguous_Test ("New NEG test ("
                          ^ Value.show test ^ ") already already exists in POS set!"))
  else { testbed with
         neg_tests = test :: testbed.neg_tests }

let add_neg_tests ~(testbed : t) (tests : Value.t list) : t =
  List.fold
    ~f:(fun testbed test -> add_neg_test ~testbed test)
    ~init:testbed
    tests

let add_pos_tests ~(testbed : t) (tests : Value.t list) : t =
  List.fold
    ~f:(fun testbed test -> add_pos_test ~testbed test)
    ~init:testbed
    tests

let add_pos_tests_safe ~(testbed : t) (tests : Value.t list) : t option =
  List.fold
    ~f:(fun tbo p ->
        begin match tbo with
          | None -> None
          | Some testbed ->
            if contains_neg_test ~testbed p then
              None
            else
              Some (add_pos_test ~testbed p)
        end)
    ~init:(Some testbed)
    tests

let merge (tb1 : t) (tb2 : t) : t =
  let new_pos = List.dedup_and_sort ~compare:Value.compare (tb1.pos_tests@tb2.pos_tests) in
  let new_neg = List.dedup_and_sort ~compare:Value.compare (tb1.neg_tests@tb2.neg_tests) in
  {
    pos_tests = new_pos ;
    neg_tests = new_neg ;
  }

let positives ~(testbed : t) : Value.t list = testbed.pos_tests

let remove_all_negatives ~(testbed : t) : t =
  {
    pos_tests = testbed.pos_tests ;
    neg_tests = []                ;
  }

let remove_all_positives ~(testbed : t) : t =
  {
    pos_tests = []                ;
    neg_tests = testbed.neg_tests ;
  }
