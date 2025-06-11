open Ast
open Parser
open Lexer

let parse (s : string) : expression =
  let lexbuf = Lexing.from_string s in
    let ast = prog read lexbuf in
      ast
