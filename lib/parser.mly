%{
open Interpreter
%}

%token <int> NUM
%token <string> ID
%token TRUE
%token FALSE
%token NULL

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

%token DEREF
%token COMMA
%token MALLOC
%token MFREE

%token SEMICOLON

%token WHILE
%token DO
%token FOR
%token TO
%token LBRACKET
%token RBRACKET

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
| LET; id = ID; ASSIGN; value = command; IN; body = command { Let(id, value, body) }
| IF; cond = expr; THEN; then_body = command; ELSE; else_body = command { Cond(cond, then_body, else_body) }
| IF; cond = expr; THEN; then_body = command { Cond(cond, then_body, Unit) }
| DEREF; loc = term; ASSIGN; e = expr { Mset(loc, e) }
| MALLOC; LPARAN; l = expr_list; RPARAN { Malloc(l) }
| MFREE; LPARAN; e = expr; RPARAN { Mfree(e) }
| WHILE; cond = expr; DO; body = command { While(cond, body) }
| FOR; id = ID; IN; LBRACKET; start = expr; TO; end_ = expr; RBRACKET; DO; body = command { For(id, start, end_, body) }
| LPARAN; c = command; RPARAN { c }
| c0 = command; SEMICOLON; c1 = command { Seq(c0, c1) }
| e = expr { e }
;

expr_list:
| x = expr; COMMA; xs = expr_list { x :: xs }
| x = expr { [x] }
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
| NULL { Loc(0) }
| LPARAN; e = expr; RPARAN { e }
| SUB; LPARAN; e = expr; RPARAN { BinOp(Sub, Num(0), e) }
| DEREF; e = term { Mget(e) }
| SUB; id = ID { BinOp(Sub, Num(0), Id(id)) }
| id = ID; { Id(id) }
;
