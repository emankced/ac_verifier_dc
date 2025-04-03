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

%left ADD
%left SUB
%left MUL
%left DIV

%start <Interpreter.expression> prog
%%


prog:
| c = command; EOF { c }
;

command:
| LET; id = ID; ASSIGN; value = bool_expr; IN; body = command { Let(id, value, body) }
| IF; cond = bool_expr; THEN; then_body = command; ELSE; else_body = command { Cond(cond, then_body, else_body) }
| e = bool_expr { e }
;

bool_expr:
| TRUE { Bool(true) }
| FALSE { Bool(false) }
| lhs = bool_expr; EQ; rhs = bool_expr { BinOp(Eq, lhs, rhs) }
| lhs = bool_expr; NE; rhs = bool_expr { BinOp(Ne, lhs, rhs) }
| lhs = negative_expr; LE; rhs = negative_expr { BinOp(Le, lhs, rhs) }
| lhs = negative_expr; LT; rhs = negative_expr { BinOp(Lt, lhs, rhs) }
| lhs = negative_expr; GE; rhs = negative_expr { BinOp(Ge, lhs, rhs) }
| lhs = negative_expr; GT; rhs = negative_expr { BinOp(Gt, lhs, rhs) }
| LPARAN; e = bool_expr; RPARAN { e }
| e = negative_expr { e }
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
| id = ID; { Id(id) }
;
