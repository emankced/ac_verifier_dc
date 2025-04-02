{
open Parser
}

let white = [' ' '\t' '\n']
let num = ['0'-'9']+

rule read =
  parse
  | white { read lexbuf }
  | num { NUM (int_of_string (Lexing.lexeme lexbuf))}
  | eof { EOF }
