open Appendix_c_verifier.Interpreter

let env: environment = EnvironmentMap.empty
let h: heap = HeapMap.empty

let%test "Let shadowing test" =
  let prog = Let("x", Num(5), Let("x", Num(3), Id("x"))) in
    let (res, _) = interp prog env h in
      match res with
      | Num(3) -> true
      | _ -> false

let%test "Conditional test" =
  let prog = Let("x", Bool(false), Cond(Id("x"), Num(42), Num(1337))) in
    let (res, _) = interp prog env h in
      match res with
      | Num(1337) -> true
      | _ -> false

let%test "Simple heap access test" =
  let prog = Let("x", Malloc([Num(-6); Num(5)]), BinOp(Add, Mget(Id("x")), Mget(BinOp(Add, Id("x"), Loc(1))))) in
    let (res, _) = interp prog env h in
      match res with
      | Num(-1) -> true
      | _ -> false

let%test "Invalid heap access test" =
  let prog = Let("x", Malloc([Num(3)]), Mget(BinOp(Add, Id("x"), Loc(1)))) in
    try
      ignore (interp prog env h);
      false
    with
      | InterpreterException _ -> true
      | _ -> false
