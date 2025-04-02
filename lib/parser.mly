%{
open Interpreter
%}

%token <int> NUM
%token ADD
%token SUB
%token MUL
%token DIV
%token LPARAN
%token RPARAN
%token EOF

(*%nonassoc*)
%left ADD
%left SUB
%left MUL
%left DIV

%start <Interpreter.expression> prog
%%


prog:
| e = negative_expr; EOF { e }
;

negative_expr:
| SUB; n = NUM { Num(-n) }
| SUB; n = NUM; ADD; rhs = expr { BinOp(Add, Num(-n), rhs) }
| SUB; n = NUM; SUB; rhs = expr { BinOp(Sub, Num(-n), rhs) }
| SUB; n = NUM; MUL; rhs = expr { BinOp(Mul, Num(-n), rhs) }
| SUB; n = NUM; DIV; rhs = expr { BinOp(Div, Num(-n), rhs) }
| SUB; LPARAN; e = negative_expr; RPARAN { BinOp(Sub, Num(0), e) }
| e = expr { e }
;

expr:
| n = NUM { Num(n) }
| lhs = expr; ADD; rhs = expr { BinOp(Add, lhs, rhs) }
| lhs = expr; SUB; rhs = expr { BinOp(Sub, lhs, rhs) }
| lhs = expr; MUL; rhs = expr { BinOp(Mul, lhs, rhs) }
| lhs = expr; DIV; rhs = expr { BinOp(Div, lhs, rhs) }
| LPARAN; e = negative_expr; RPARAN { e }
;
