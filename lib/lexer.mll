{
open Parser
}

let white = [' ' '\t' '\n']
let num = ['0'-'9']+
let id = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule read =
  parse
  | white { read lexbuf }
  | num { NUM (int_of_string (Lexing.lexeme lexbuf))}
  | "true" { TRUE }
  | "false" { FALSE }
  | "null" { NULL }
  | '+' { ADD }
  | '-' { SUB }
  | '*' { MUL }
  | '/' { DIV }
  | "<=" { LE }
  | '<' { LT }
  | ">=" { GE }
  | ">" { GT }
  | "==" { EQ }
  | "!=" { NE }
  | '(' { LPARAN }
  | ')' { RPARAN }
  | "let" { LET }
  | ":=" { ASSIGN }
  | "in" { IN }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | '!' { DEREF }
  | ',' { COMMA }
  | "malloc" { MALLOC }
  | "mfree" { MFREE }
  | ';' { SEMICOLON }
  | "while" { WHILE }
  | "do" { DO }
  | "for" { FOR }
  | "to" { TO }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | '@' { ASSERT }
  | "&&" { AND }
  | "||" { OR }
  | "not" { NOT }
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }
