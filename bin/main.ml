open Appendix_c_verifier.Ast
open Appendix_c_verifier.Interpreter
open Appendix_c_verifier.Parse

let env: environment = EnvironmentMap.empty
let h: heap = HeapMap.empty

let () = print_endline "Appendix C Verifier"; print_newline ()

let () = if (Array.length Sys.argv) != 2 then
  print_endline ("Usage: " ^ Array.get Sys.argv 0 ^ " <file>")
else
  let src =
    let lines = ref "" in
    let ic = open_in (Array.get Sys.argv 1) in
    try
      while true do
        lines := !lines ^ "\n" ^ input_line ic
      done; !lines
    with End_of_file ->
      close_in ic;
      !lines
  in
    let prog = parse src in
      print_endline "AST:";
      print_endline (string_of_expression prog);
      print_newline ();
      print_endline "Result:";
      let (res, _) = interp prog env h in
        match res with
        | Loc(l, o) -> print_string "Loc("; print_int l; print_string ", "; print_int o; print_endline ")"
        | Num(n) -> print_string "Num("; print_int n; print_endline ")"
        | Bool(b) -> print_endline ("Bool(" ^ (if b then "true" else "false") ^ ")")
        | Unit -> print_endline "Unit"
