open Appendix_c_verifier.Interpreter

let env: environment = EnvironmentMap.empty
let h: heap = HeapMap.empty

let () =
  let prog = Let("x", Num(5), Let("x", Num(3), Id("x"))) in
    let (res, _) = interp prog env h in
      print_string "Let shadowing: ";
      match res with
      | Num(3) -> print_endline "success"
      | _ -> print_endline "failure"; exit 1

let () =
  let prog = Let("x", Bool(false), Cond(Id("x"), Num(42), Num(1337))) in
    let (res, _) = interp prog env h in
      print_string "Conditional: ";
      match res with
      | Num(1337) -> print_endline "success"
      | _ -> print_endline "failure"; exit 1

let () =
  let prog = Let("x", Malloc([Num(-6); Num(5)]), BinOp(Add, Mget(Id("x")), Mget(BinOp(Add, Id("x"), Loc(1))))) in
    let (res, _) = interp prog env h in
      print_string "Simple heap access: ";
      match res with
      | Num(-1) -> print_endline "success"
      | _ -> print_endline "failure"; exit 1

let () =
  let prog = Let("x", Malloc([Num(3)]), Mget(BinOp(Add, Id("x"), Loc(1)))) in
    print_string "Invalid heap access: ";
    let _ =
      try interp prog env h with _ -> print_endline "success"; exit 0
      in
      print_endline "failure"; exit 1
