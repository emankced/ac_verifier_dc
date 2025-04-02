%{
open Interpreter
%}

%token <int> NUM
%token ADD
%token SUB
%token MUL
%token DIV
%token EOF

(*%nonassoc*)
%left ADD
%left SUB
%left MUL
%left DIV

%start <Interpreter.expression> prog
%%


prog:
| e = expr; EOF { e }
;

expr:
| n = NUM { Num(n) }
| lhs = expr; ADD; rhs = expr { BinOp(Add, lhs, rhs) }
| lhs = expr; SUB; rhs = expr { BinOp(Sub, lhs, rhs) }
| lhs = expr; MUL; rhs = expr { BinOp(Mul, lhs, rhs) }
| lhs = expr; DIV; rhs = expr { BinOp(Div, lhs, rhs) }
;