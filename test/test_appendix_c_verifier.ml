open Appendix_c_verifier.Ast
open Appendix_c_verifier.Interpreter
open Appendix_c_verifier.Parse
open Appendix_c_verifier.Common

let env: environment = StringMap.empty
let sdef: struct_definitions = StringMap.empty
let h: heap = IntMap.empty

let%test "Let shadowing test" =
  let prog = Let(0, "x", Num(1, 5), Let(2, "x", Num(3, 3), Id(4, "x"))) in
    let (res, _) = interp prog env sdef Unit h in
      match res with
      | Num(3) -> true
      | _ -> false

let%test "Conditional test" =
  let prog = Let(0, "x", Bool(1, false), Cond(2, Id(3, "x"), Num(4, 42), Num(5, 1337))) in
    let (res, _) = interp prog env sdef Unit h in
      match res with
      | Num(1337) -> true
      | _ -> false

let%test "Simple heap access test" =
  let prog = Struct(0, "nums", [("a", Num); ("b", Num)], Let(1, "x", Malloc(2, "nums", [Num(3, -6); Num(4, 5)]), BinOp(5, Add, Mget(6, Id(7, "x"), "a"), Mget(8, Id(9, "x"), "b")))) in
    let (res, _) = interp prog env sdef Unit h in
      match res with
      | Num(-1) -> true
      | _ -> false

let%test "Invalid heap access test" =
  let prog = Struct(0, "num", [("n", Num)], Let(1, "x", Malloc(2, "num", [Num(3, 3)]), Mget(4, Id(5, "x"), "m"))) in
    try
      ignore (interp prog env sdef Unit h);
      false
    with
      | InterpreterException _ -> true
      | _ -> false

let%test "While loop" =
  let prog = Struct(0, "num", [("n", Num)], Let(1, "c", Malloc(2, "num", [Num(3, 0)]), While(4, BinOp(5, Lt, Mget(6, Id(7, "c"), "n"), Num(8, 5)), Mset(9, Id(10, "c"), "n", BinOp(11, Add, Mget(12, Id(13, "c"), "n"), Num(14, 1)))))) in
    let (_, h) = interp prog env sdef Unit h in
      match IntMap.find_first (fun _ -> true) h with
      | (_, [Num(5)]) -> true
      | _ -> false

let%test "For loop" =
  let prog = Struct(0, "num", [("n", Num)], Let(1, "sum", Malloc(2, "num", [Num(3, 0)]), For(4, "i", Num(5, 1), Num(6, 5), Mset(7, Id(8, "sum"), "n", BinOp(9, Add, Mget(10, Id(11, "sum"), "n"), Id(12, "i")))))) in
    let (_, h) = interp prog env sdef Unit h in
      match IntMap.find_first (fun _ -> true) h with
      | (_, [Num(15)]) -> true
      | _ -> false

let%test "Parse simple arithmetics" =
  (let (v, _) = (interp (parse "1 + 5") env sdef Unit h) in v) === Num(6) &&
  (let (v, _) = (interp (parse "1 - 5") env sdef Unit h) in v) === Num(-4) &&
  (let (v, _) = (interp (parse "2 * 5") env sdef Unit h) in v) === Num(10) &&
  (let (v, _) = (interp (parse "9 / 3") env sdef Unit h) in v) === Num(3) &&
  (let (v, _) = (interp (parse "-1 + 5") env sdef Unit h) in v) === Num(4) &&
  (let (v, _) = (interp (parse "-1 - 5") env sdef Unit h) in v) === Num(-6) &&
  (let (v, _) = (interp (parse "-1 * 5") env sdef Unit h) in v) === Num(-5) &&
  (let (v, _) = (interp (parse "(5 + 1) * 3") env sdef Unit h) in v) === Num(18) &&
  (let (v, _) = (interp (parse "3 * (-5 + 1)") env sdef Unit h) in v) === Num(-12) &&
  (let (v, _) = (interp (parse "(-1) - 1 - 1 - 1") env sdef Unit h) in v) === Num(-4) &&
  (let (v, _) = (interp (parse "1 - 1 - 1") env sdef Unit h) in v) === Num(-1) &&
  (let (v, _) = (interp (parse "3 + 5 * 7 + 2 / 1 * 3") env sdef Unit h) in v) === Num(44)

let%test "Parse hard arithmetics" =
  (let (v, _) = (interp (parse "-1 - 1 - 1 - 1") env sdef Unit h) in v) === Num(-4) &&
  (let (v, _) = (interp (parse "20 / 4 / 2") env sdef Unit h) in v) === Num(2) &&
  (let (v, _) = (interp (parse "20 / 2 - 2") env sdef Unit h) in v) === Num(8) &&
  (let (v, _) = (interp (parse "let x := 5 in -x - x * 3") env sdef Unit h) in v) === Num(-20)

let%test "Parse simple comparators" =
  (let (v, _) = (interp (parse "-5 < 5") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "5 < 5") env sdef Unit h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "5 <= 5") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "-5 > 5") env sdef Unit h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "5 > 5") env sdef Unit h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "5 >= 5") env sdef Unit h) in v) === Bool(true)

let%test "Parse hard comparators" =
  (let (v, _) = (interp (parse "true == false") env sdef Unit h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "false == false") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "5 <= 5 == (5 == 5)") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "5 < 5 == (5 == 5)") env sdef Unit h) in v) === Bool(false)

let%test "Parse simple bool operations" =
  (let (v, _) = (interp (parse "true && true") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "true && false") env sdef Unit h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "false && true") env sdef Unit h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "false && false") env sdef Unit h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "true || true") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "true || false") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "false || true") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "false || false") env sdef Unit h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "not true") env sdef Unit h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "not false") env sdef Unit h) in v) === Bool(true)

let%test "Parse hard bool operations" =
  (let (v, _) = (interp (parse "false && true || false") env sdef Unit h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "true || false && true") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "true && true && false || false || false || true") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "true && true && false || false || false") env sdef Unit h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "5 <= 5 == (5 == 5) && 5 < 5 == (5 == 5)") env sdef Unit h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "5 <= 5 == (5 == 5) || 5 < 5 == (5 == 5)") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "not false || true") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "not true || true") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "not false && true") env sdef Unit h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "not (5 <= 5 == (5 == 5))") env sdef Unit h) in v) === Bool(false)

let%test "Parse let" =
  (let (v, _) = (interp (parse "let x := 5 in let y := 3 in let x := 10 in x + y") env sdef Unit h) in v) === Num(13)

let%test "Parse let and cond" =
  (let (v, _) = (interp (parse "let x := 5 in if x * 5 < 30 != true then 42 else 1337") env sdef Unit h) in v) === Num(1337)

let%test "Parse short cond" =
  (let (v, _) = (interp (parse "struct num { n: int } in let x := malloc(num, 5) in (if true then !x.n := !x.n + 7); (if false then !x.n := !x.n + 3); !x.n") env sdef Unit h) in v) === Num(12)

let%test "Parse heap commands" =
  (let (v, _) = (interp (parse "struct nums { a: int, b: int } in let x := malloc(nums, 5, 7) in !x.a := 42; !x.a") env sdef Unit h) in v) === Num(42) &&
  (let (v, _) = (interp (parse "struct nums { a: int, b: int } in let x := malloc(nums, 5, 7) in !x.a := 42; mfree(x)") env sdef Unit h) in v) === Unit &&
  (let (v, _) = (interp (parse "struct nums { a: int, b: int } in let x := malloc(nums, 5, 7) in let a := !x.a in !x.b := a*2; !x.b") env sdef Unit h) in v) === Num(10)

let%test "Parse for loop" =
  (let (v, _) = (interp (parse "struct num { n: int } in let sum := malloc(num, 0) in (for i in [1 to 5] do !sum.n := !sum.n + i); !sum.n") env sdef Unit h) in v) === Num(15)

let%test "Parse while loop" =
  (let (v, _) = (interp (parse "struct num { n: int } in let sum := malloc(num, 1) in (while !sum.n < 20 do !sum.n := !sum.n + !sum.n); !sum.n") env sdef Unit h) in v) === Num(32)

let%test "Parse assert 1" =
  (let (v, _) = (interp (parse "@ true @") env sdef Unit h) in v) === Unit

let%test "Parse assert 2" =
  (let (v, _) = (interp (parse "@ true ** false @") env sdef Unit h) in v) === Unit

let%test "Parse invariant" =
  (let (v, _) = (interp (parse "@ invariant true @ while false do 5") env sdef Unit h) in v) === Unit
