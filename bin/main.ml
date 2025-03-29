open Appendix_c_verifier.Interpreter

(** let prog: expression = Let("x", Bool(false), Cond(Id("x"), Num(42), Num(1337))) *)
let prog: expression = Let("x", Malloc([Num(-6); Num(5)]), BinOp(Add, Mget(Id("x")), Mget(BinOp(Add, Id("x"), Loc(1)))))
let env: environment = EnvironmentMap.empty
let h: heap = HeapMap.empty

let () = print_endline "Appendix C Verifier"
let () =
  let (res, _) = interp prog env h in
    match res with
    | Loc(l) -> print_string "Loc("; print_int l; print_endline ")"
    | Num(n) -> print_string "Num("; print_int n; print_endline ")"
    | Bool(b) -> print_endline ("Bool(" ^ (if b then "true" else "false") ^ ")")
    | Unit -> print_endline "Unit"
