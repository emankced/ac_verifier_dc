open Appendix_c_verifier.Ast
open Appendix_c_verifier.Interpreter
open Appendix_c_verifier.Parse

let env: environment = EnvironmentMap.empty
let sdef: struct_definitions = EnvironmentMap.empty
let h: heap = HeapMap.empty

let%test "Let shadowing test" =
  let prog = Let("x", Num(5), Let("x", Num(3), Id("x"))) in
    let (res, _) = interp prog env sdef h in
      match res with
      | Num(3) -> true
      | _ -> false

let%test "Conditional test" =
  let prog = Let("x", Bool(false), Cond(Id("x"), Num(42), Num(1337))) in
    let (res, _) = interp prog env sdef h in
      match res with
      | Num(1337) -> true
      | _ -> false

let%test "Simple heap access test" =
  let prog = Let("x", Malloc([Num(-6); Num(5)]), BinOp(Add, Mget(Id("x")), Mget(BinOp(Add, Id("x"), Num(1))))) in
    let (res, _) = interp prog env sdef h in
      match res with
      | Num(-1) -> true
      | _ -> false

let%test "Invalid heap access test" =
  let prog = Let("x", Malloc([Num(3)]), Mget(BinOp(Add, Id("x"), Num(1)))) in
    try
      ignore (interp prog env sdef h);
      false
    with
      | InterpreterException _ -> true
      | _ -> false

let%test "While loop" =
  let prog = Let("c", Malloc([Num(0)]), While(BinOp(Lt, Mget(Id("c")), Num(5)), Mset(Id("c"), BinOp(Add, Mget(Id("c")), Num(1))))) in
    let (_, h) = interp prog env sdef h in
      match HeapMap.find_first (fun _ -> true) h with
      | (_, [Num(5)]) -> true
      | _ -> false

let%test "For loop" =
  let prog = Let("sum", Malloc([Num(0)]), For("i", Num(1), Num(5), Mset(Id("sum"), BinOp(Add, Mget(Id("sum")), Id("i"))))) in
    let (_, h) = interp prog env sdef h in
      match HeapMap.find_first (fun _ -> true) h with
      | (_, [Num(15)]) -> true
      | _ -> false

let%test "Parse simple arithmetics" =
  (let (v, _) = (interp (parse "1 + 5") env sdef h) in v) === Num(6) &&
  (let (v, _) = (interp (parse "1 - 5") env sdef h) in v) === Num(-4) &&
  (let (v, _) = (interp (parse "2 * 5") env sdef h) in v) === Num(10) &&
  (let (v, _) = (interp (parse "9 / 3") env sdef h) in v) === Num(3) &&
  (let (v, _) = (interp (parse "-1 + 5") env sdef h) in v) === Num(4) &&
  (let (v, _) = (interp (parse "-1 - 5") env sdef h) in v) === Num(-6) &&
  (let (v, _) = (interp (parse "-1 * 5") env sdef h) in v) === Num(-5) &&
  (let (v, _) = (interp (parse "(5 + 1) * 3") env sdef h) in v) === Num(18) &&
  (let (v, _) = (interp (parse "3 * (-5 + 1)") env sdef h) in v) === Num(-12) &&
  (let (v, _) = (interp (parse "(-1) - 1 - 1 - 1") env sdef h) in v) === Num(-4) &&
  (let (v, _) = (interp (parse "1 - 1 - 1") env sdef h) in v) === Num(-1) &&
  (let (v, _) = (interp (parse "3 + 5 * 7 + 2 / 1 * 3") env sdef h) in v) === Num(44)

let%test "Parse hard arithmetics" =
  (let (v, _) = (interp (parse "-1 - 1 - 1 - 1") env sdef h) in v) === Num(-4) &&
  (let (v, _) = (interp (parse "20 / 4 / 2") env sdef h) in v) === Num(2) &&
  (let (v, _) = (interp (parse "20 / 2 - 2") env sdef h) in v) === Num(8) &&
  (let (v, _) = (interp (parse "let x := 5 in -x - x * 3") env sdef h) in v) === Num(-20)

let%test "Parse simple comparators" =
  (let (v, _) = (interp (parse "-5 < 5") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "5 < 5") env sdef h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "5 <= 5") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "-5 > 5") env sdef h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "5 > 5") env sdef h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "5 >= 5") env sdef h) in v) === Bool(true)

let%test "Parse hard comparators" =
  (let (v, _) = (interp (parse "true == false") env sdef h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "false == false") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "5 <= 5 == (5 == 5)") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "5 < 5 == (5 == 5)") env sdef h) in v) === Bool(false)

let%test "Parse simple bool operations" =
  (let (v, _) = (interp (parse "true && true") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "true && false") env sdef h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "false && true") env sdef h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "false && false") env sdef h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "true || true") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "true || false") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "false || true") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "false || false") env sdef h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "not true") env sdef h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "not false") env sdef h) in v) === Bool(true)

let%test "Parse hard bool operations" =
  (let (v, _) = (interp (parse "false && true || false") env sdef h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "true || false && true") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "true && true && false || false || false || true") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "true && true && false || false || false") env sdef h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "5 <= 5 == (5 == 5) && 5 < 5 == (5 == 5)") env sdef h) in v) === Bool(false) &&
  (let (v, _) = (interp (parse "5 <= 5 == (5 == 5) || 5 < 5 == (5 == 5)") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "not false || true") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "not true || true") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "not false && true") env sdef h) in v) === Bool(true) &&
  (let (v, _) = (interp (parse "not (5 <= 5 == (5 == 5))") env sdef h) in v) === Bool(false)

let%test "Parse let" =
  (let (v, _) = (interp (parse "let x := 5 in let y := 3 in let x := 10 in x + y") env sdef h) in v) === Num(13)

let%test "Parse let and cond" =
  (let (v, _) = (interp (parse "let x := 5 in if x * 5 < 30 != true then 42 else 1337") env sdef h) in v) === Num(1337)

let%test "Parse short cond" =
  (let (v, _) = (interp (parse "let x := malloc(5) in (if true then !x := !x + 7); (if false then !x := !x + 3); !x") env sdef h) in v) === Num(12)

let%test "Parse heap commands" =
  (let (v, _) = (interp (parse "let x := malloc(5, 7) in !x := 42; !x") env sdef h) in v) === Num(42) &&
  (let (v, _) = (interp (parse "let x := malloc(5, 7) in !x := 42; mfree(x)") env sdef h) in v) === Unit &&
  (let (v, _) = (interp (parse "let x := malloc(5, 7) in let a := !x in !(x+1) := a*2; !(x+1)") env sdef h) in v) === Num(10)

let%test "Parse for loop" =
  (let (v, _) = (interp (parse "let sum := malloc(0) in (for i in [1 to 5] do !sum := !sum + i); !sum") env sdef h) in v) === Num(15)

let%test "Parse while loop" =
  (let (v, _) = (interp (parse "let sum := malloc(1) in (while !sum < 20 do !sum := !sum + !sum); !sum") env sdef h) in v) === Num(32)
