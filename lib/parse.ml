open Ast
open Parser
open Lexer

(**
[parse s] parses program [s]
@param s program code as string
@returns AST
*)
let parse (s : string) : expression =
  let lexbuf = Lexing.from_string ~with_positions:false s in
    (try
      prog read lexbuf
    with
    | _e ->
        let curr = lexbuf.Lexing.lex_curr_p in
        let line = curr.Lexing.pos_lnum in
        let col = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
        let tok = Lexing.lexeme lexbuf in
        let col = col - (String.length tok - 1) in
        print_endline ("Parsing error in line " ^ string_of_int line ^ " column " ^ string_of_int col ^ ": \"" ^ tok ^ "\"");
        exit(1)
    )
