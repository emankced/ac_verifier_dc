%{
open Interpreter
%}

%token <int> NUM
%token EOF

%start <Interpreter.expression> prog
%%


prog:
| e = expr; EOF { e }
;

expr:
| n = NUM { Num(n) }
;