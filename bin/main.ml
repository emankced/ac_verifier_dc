open Appendix_c_verifier.Interpreter
open Appendix_c_verifier.Parse

let env: environment = EnvironmentMap.empty
let h: heap = HeapMap.empty

let () = print_endline "Appendix C Verifier"

let src = "let x := malloc(5, 7) in !x := 42; !x"

let () =
  let prog = parse src in
    print_endline (string_of_expression prog)

let () =
  let prog = parse src in
    let (res, _) = interp prog env h in
      match res with
      | Loc(l) -> print_string "Loc("; print_int l; print_endline ")"
      | Num(n) -> print_string "Num("; print_int n; print_endline ")"
      | Bool(b) -> print_endline ("Bool(" ^ (if b then "true" else "false") ^ ")")
      | Unit -> print_endline "Unit"
