%{
open Ast
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

%token AND
%token OR
%token NOT

%token SEP
%token SEPIMP
%token POINTSTO

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

%token ASSERT

%token STRUCT
%token LBRACE
%token RBRACE
%token INT
%token BOOL

%token EOF

%right SEPIMP
%right SEP
%right OR
%right AND
%right EQ NE
%right LE LT GE GT
%right POINTSTO

%left ADD SUB
%left MUL DIV

%start <Ast.expression> prog
%%


prog:
| c = command; EOF { c }
;

type_:
| INT { Num }
| BOOL { Bool }
| id = ID { LocStruct(id) }
;

type_list:
| x = type_; COMMA; xs = type_list { x :: xs }
| x = type_ { [x] }
;

command:
| a = assertion; c = command { Assert(a, c) }
| LET; id = ID; ASSIGN; value = command; IN; body = command { Let(id, value, body) }
| IF; cond = expr; THEN; then_body = command; ELSE; else_body = command { Cond(cond, then_body, else_body) }
| IF; cond = expr; THEN; then_body = command { Cond(cond, then_body, Unit) }
| DEREF; loc = term; ASSIGN; e = expr { Mset(loc, e) }
| MALLOC; LPARAN; id = ID; COMMA; l = expr_list; RPARAN { Malloc(id, l) }
| MFREE; LPARAN; e = expr; RPARAN { Mfree(e) }
| WHILE; cond = expr; DO; body = command { While(cond, body) }
| FOR; id = ID; IN; LBRACKET; start = expr; TO; end_ = expr; RBRACKET; DO; body = command { For(id, start, end_, body) }
| LPARAN; c = command; RPARAN { c }
| STRUCT; id = ID; LBRACE; types = type_list; RBRACE; IN; body = command { Struct(id, types, body) }
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
| lhs = expr; AND; rhs = expr { BinOp(And, lhs, rhs) }
| lhs = expr; OR; rhs = expr { BinOp(Or, lhs, rhs) }
;

term:
| n = NUM { Num(n) }
| SUB; n = NUM { Num(-n) }
| TRUE { Bool(true) }
| FALSE { Bool(false) }
| NULL { Null }
| NOT; TRUE { Bool(false) }
| NOT; FALSE { Bool(true) }
| LPARAN; e = expr; RPARAN { e }
| SUB; LPARAN; e = expr; RPARAN { BinOp(Sub, Num(0), e) }
| NOT; LPARAN; e = expr; RPARAN { BinOp(Eq, e, Bool(false)) }
| DEREF; e = term { Mget(e) }
| SUB; id = ID { BinOp(Sub, Num(0), Id(id)) }
| NOT; id = ID { BinOp(Eq, Id(id), Bool(false)) }
| id = ID; { Id(id) }
;

assertion:
| ASSERT; a = assert_expr; ASSERT { a }
;

assert_expr:
| e = expr_no_deref { e }
| lhs = assert_expr; SEP; rhs = assert_expr { BinOp(Sep, lhs, rhs) }
| lhs = assert_expr; SEPIMP; rhs = assert_expr { BinOp(SepImp, lhs, rhs) }
| lhs = assert_expr; POINTSTO; rhs = assert_expr { BinOp(PointsTo, lhs, rhs) }
| LPARAN; e = assert_expr; RPARAN { e }
(* TODO: predicates, forall, (exists,) always *)
;

expr_no_deref:
| t = term_no_deref { t }
| lhs = expr_no_deref; ADD; rhs = expr_no_deref { BinOp(Add, lhs, rhs) }
| lhs = expr_no_deref; SUB; rhs = expr_no_deref { BinOp(Sub, lhs, rhs) }
| lhs = expr_no_deref; MUL; rhs = expr_no_deref { BinOp(Mul, lhs, rhs) }
| lhs = expr_no_deref; DIV; rhs = expr_no_deref { BinOp(Div, lhs, rhs) }
| lhs = expr_no_deref; EQ; rhs = expr_no_deref { BinOp(Eq, lhs, rhs) }
| lhs = expr_no_deref; NE; rhs = expr_no_deref { BinOp(Ne, lhs, rhs) }
| lhs = expr_no_deref; LE; rhs = expr_no_deref { BinOp(Le, lhs, rhs) }
| lhs = expr_no_deref; LT; rhs = expr_no_deref { BinOp(Lt, lhs, rhs) }
| lhs = expr_no_deref; GE; rhs = expr_no_deref { BinOp(Ge, lhs, rhs) }
| lhs = expr_no_deref; GT; rhs = expr_no_deref { BinOp(Gt, lhs, rhs) }
| lhs = expr_no_deref; AND; rhs = expr_no_deref { BinOp(And, lhs, rhs) }
| lhs = expr_no_deref; OR; rhs = expr_no_deref { BinOp(Or, lhs, rhs) }
;

term_no_deref:
| n = NUM { Num(n) }
| SUB; n = NUM { Num(-n) }
| TRUE { Bool(true) }
| FALSE { Bool(false) }
| NULL { Null }
| NOT; TRUE { Bool(false) }
| NOT; FALSE { Bool(true) }
| LPARAN; e = expr_no_deref; RPARAN { e }
| SUB; LPARAN; e = expr_no_deref; RPARAN { BinOp(Sub, Num(0), e) }
| NOT; LPARAN; e = expr_no_deref; RPARAN { BinOp(Eq, e, Bool(false)) }
| SUB; id = ID { BinOp(Sub, Num(0), Id(id)) }
| NOT; id = ID { BinOp(Eq, Id(id), Bool(false)) }
| id = ID; { Id(id) }
;
