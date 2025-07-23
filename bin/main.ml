open Appendix_c_verifier.Ast
open Appendix_c_verifier.Interpreter
open Appendix_c_verifier.Parse
open Appendix_c_verifier.Analysis
open Appendix_c_verifier.Symexec
open Appendix_c_verifier.Common

let () = print_endline "Appendix C Verifier"; print_newline ()

let no_type_check = ref false
let no_verify = ref false
let no_interpret = ref false
let print_ast = ref false
let input_file = ref ""

let anon_fun filename = input_file := filename

let speclist = [
  ("--no-type-check", Arg.Set no_type_check, "disables type checker");
  ("--no-verify", Arg.Set no_verify, "disables symbolic execution and verification");
  ("--no-interpret", Arg.Set no_interpret, "disables program interpretation, so the input program is not executed");
  ("--print-ast", Arg.Set print_ast, "prints the AST after parsing")
]

let usage_msg = "Usage: " ^ Array.get Sys.argv 0 ^ " <file> [--no-type-check] [--no-verify] [--no-interpret] [--print-ast]"
let () = Arg.parse speclist anon_fun usage_msg

let env: environment = StringMap.empty
let sdef: struct_definitions = StringMap.empty
let h: heap = IntMap.empty

let () = if String.equal "" !input_file then
    (print_endline usage_msg;
    exit 0)
  else
  let src =
    let lines = ref "" in
    let ic = open_in !input_file in
    try
      while true do
        lines := !lines ^ "\n" ^ input_line ic
      done; !lines
    with End_of_file ->
      close_in ic;
      !lines
  in
    let prog = parse src in
      (if !print_ast then
        (print_endline "AST:";
        print_endline (string_of_expression prog);
        print_newline ()));
      (if not !no_type_check then
      (*try*)
        let (tc_res, _tm) = type_check prog StringMap.empty StringMap.empty IntMap.empty in
          print_endline ("Type: " ^ types_to_string tc_res);
          print_newline ()
      (*with TypeCheckError(e) -> print_string "TypeCheckError: "; print_endline e*));
      (if not !no_interpret then
        (print_endline "Result:";
        (let (res, _) = interp prog env sdef h in
          match res with
          | Loc(l, t) -> print_string "Loc("; print_int l; print_string ", "; print_string t; print_endline ")"
          | Num(n) -> print_string "Num("; print_int n; print_endline ")"
          | Bool(b) -> print_endline ("Bool(" ^ (if b then "true" else "false") ^ ")")
          | Unit -> print_endline "Unit"
        ); print_newline ()));
      (if not !no_verify then
        print_endline (try (let _ = verify prog StringMap.empty IntMap.empty [] in "satisfiable") with
          | Unsatisfiable -> "unsatisfiable"
          | Unknown -> "unknown"
        )
      )
