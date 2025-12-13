{
open Parser
open Lexing

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
    {
      pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let num = ['0'-'9']+
let id = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule read =
  parse
  | white { read lexbuf }
  | num { NUM (int_of_string (Lexing.lexeme lexbuf))}
  | newline { next_line lexbuf; read lexbuf }
  | "true" { TRUE }
  | "false" { FALSE }
  | "**" { SEP }
  (*| "-*" { SEPIMP }*)
  (*| "->" { POINTSTO }*)
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
  | "struct" { STRUCT }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | "int" { INT }
  | "bool" { BOOL }
  | '.' { DOT }
  | ':' { COLON }
  | "result" { RESULT }
  | "invariant" { INVARIANT }
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }
