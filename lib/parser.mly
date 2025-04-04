%{
open Interpreter
%}

%token <int> NUM
%token <string> ID
%token TRUE
%token FALSE

%token ADD
%token SUB
%token MUL
%token DIV

%token LE
%token LT
%token GE
%token GT

%token EQ
%token NE

%token LPARAN
%token RPARAN

%token LET
%token ASSIGN
%token IN

%token IF
%token THEN
%token ELSE

%token EOF

%right EQ NE
%right LE LT GE GT

%left ADD SUB
%left MUL DIV

%start <Interpreter.expression> prog
%%


prog:
| c = command; EOF { c }
;

command:
| LET; id = ID; ASSIGN; value = expr; IN; body = command { Let(id, value, body) }
| IF; cond = expr; THEN; then_body = command; ELSE; else_body = command { Cond(cond, then_body, else_body) }
| e = expr { e }
;

expr:
| t = term { t }
| lhs = expr; ADD; rhs = expr { BinOp(Add, lhs, rhs) }
| lhs = expr; SUB; rhs = expr { BinOp(Sub, lhs, rhs) }
| lhs = expr; MUL; rhs = expr { BinOp(Mul, lhs, rhs) }
| lhs = expr; DIV; rhs = expr { BinOp(Div, lhs, rhs) }
| lhs = expr; EQ; rhs = expr { BinOp(Eq, lhs, rhs) }
| lhs = expr; NE; rhs = expr { BinOp(Ne, lhs, rhs) }
| lhs = expr; LE; rhs = expr { BinOp(Le, lhs, rhs) }
| lhs = expr; LT; rhs = expr { BinOp(Lt, lhs, rhs) }
| lhs = expr; GE; rhs = expr { BinOp(Ge, lhs, rhs) }
| lhs = expr; GT; rhs = expr { BinOp(Gt, lhs, rhs) }
;

term:
| n = NUM { Num(n) }
| SUB; n = NUM { Num(-n) }
| TRUE { Bool(true) }
| FALSE { Bool(false) }
| LPARAN; e = expr; RPARAN { e }
| SUB; LPARAN; e = expr; RPARAN { BinOp(Sub, Num(0), e) }
| id = ID; { Id(id) }
;
