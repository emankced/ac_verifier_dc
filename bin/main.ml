let prog: Appendix_c_verifier.Interpreter.expression = Let("x", Bool(false), Cond(Id("x"), Num(42), Num(1337)))
let env: Appendix_c_verifier.Interpreter.environment = Appendix_c_verifier.Interpreter.EnvironmentMap.empty
let h: Appendix_c_verifier.Interpreter.heap = Appendix_c_verifier.Interpreter.HeapMap.empty

let () = print_endline "Appendix C Verifier"
let () =
  let (res, _) = Appendix_c_verifier.Interpreter.interp prog env h in
    match res with
    | Loc(l) -> print_string "Loc("; print_int l; print_endline ")"
    | Num(n) -> print_string "Num("; print_int n; print_endline ")"
    | Bool(b) -> print_endline ("Bool(" ^ (if b then "true" else "false") ^ ")")
    | Unit -> print_endline "Unit"
