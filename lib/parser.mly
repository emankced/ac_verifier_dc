%{
open Ast
let i = ref 0
let get i = let v = !i in i := v+1; v
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
| a = assertion; c = command { Assert(get i, a, c) }
| LET; id = ID; ASSIGN; value = command; IN; body = command { Let(get i, id, value, body) }
| IF; cond = expr; THEN; then_body = command; ELSE; else_body = command { Cond(get i, cond, then_body, else_body) }
| IF; cond = expr; THEN; then_body = command { Cond(get i, cond, then_body, Unit(get i)) }
| DEREF; loc = term; ASSIGN; e = expr { Mset(get i, loc, e) }
| MALLOC; LPARAN; id = ID; COMMA; l = expr_list; RPARAN { Malloc(get i, id, l) }
| MFREE; LPARAN; e = expr; RPARAN { Mfree(get i, e) }
| WHILE; cond = expr; DO; body = command { While(get i, cond, body) }
| FOR; id = ID; IN; LBRACKET; start = expr; TO; end_ = expr; RBRACKET; DO; body = command { For(get i, id, start, end_, body) }
| LPARAN; c = command; RPARAN { c }
| STRUCT; id = ID; LBRACE; types = type_list; RBRACE; IN; body = command { Struct(get i, id, types, body) }
| c0 = command; SEMICOLON; c1 = command { Seq(get i, c0, c1) }
| e = expr { e }
;

expr_list:
| x = expr; COMMA; xs = expr_list { x :: xs }
| x = expr { [x] }
;

expr:
| t = term { t }
| lhs = expr; ADD; rhs = expr { BinOp(get i, Add, lhs, rhs) }
| lhs = expr; SUB; rhs = expr { BinOp(get i, Sub, lhs, rhs) }
| lhs = expr; MUL; rhs = expr { BinOp(get i, Mul, lhs, rhs) }
| lhs = expr; DIV; rhs = expr { BinOp(get i, Div, lhs, rhs) }
| lhs = expr; EQ; rhs = expr { BinOp(get i, Eq, lhs, rhs) }
| lhs = expr; NE; rhs = expr { BinOp(get i, Ne, lhs, rhs) }
| lhs = expr; LE; rhs = expr { BinOp(get i, Le, lhs, rhs) }
| lhs = expr; LT; rhs = expr { BinOp(get i, Lt, lhs, rhs) }
| lhs = expr; GE; rhs = expr { BinOp(get i, Ge, lhs, rhs) }
| lhs = expr; GT; rhs = expr { BinOp(get i, Gt, lhs, rhs) }
| lhs = expr; AND; rhs = expr { BinOp(get i, And, lhs, rhs) }
| lhs = expr; OR; rhs = expr { BinOp(get i, Or, lhs, rhs) }
;

term:
| n = NUM { Num(get i, n) }
| SUB; n = NUM { Num(get i, -n) }
| TRUE { Bool(get i, true) }
| FALSE { Bool(get i, false) }
| NULL { Null(get i) }
| NOT; TRUE { Bool(get i, false) }
| NOT; FALSE { Bool(get i, true) }
| LPARAN; e = expr; RPARAN { e }
| SUB; LPARAN; e = expr; RPARAN { BinOp(get i, Sub, Num(get i, 0), e) }
| NOT; LPARAN; e = expr; RPARAN { BinOp(get i, Eq, e, Bool(get i, false)) }
| DEREF; e = term { Mget(get i, e) }
| SUB; id = ID { BinOp(get i, Sub, Num(get i, 0), Id(get i, id)) }
| NOT; id = ID { BinOp(get i, Eq, Id(get i, id), Bool(get i, false)) }
| id = ID; { Id(get i, id) }
;

assertion:
| ASSERT; a = assert_expr; ASSERT { a }
;

assert_expr:
| e = expr_no_deref { e }
| lhs = assert_expr; SEP; rhs = assert_expr { BinOp(get i, Sep, lhs, rhs) }
| lhs = assert_expr; SEPIMP; rhs = assert_expr { BinOp(get i, SepImp, lhs, rhs) }
| lhs = assert_expr; POINTSTO; rhs = assert_expr { BinOp(get i, PointsTo, lhs, rhs) }
| LPARAN; e = assert_expr; RPARAN { e }
(* TODO: predicates, forall, (exists,) always *)
;

expr_no_deref:
| t = term_no_deref { t }
| lhs = expr_no_deref; ADD; rhs = expr_no_deref { BinOp(get i, Add, lhs, rhs) }
| lhs = expr_no_deref; SUB; rhs = expr_no_deref { BinOp(get i, Sub, lhs, rhs) }
| lhs = expr_no_deref; MUL; rhs = expr_no_deref { BinOp(get i, Mul, lhs, rhs) }
| lhs = expr_no_deref; DIV; rhs = expr_no_deref { BinOp(get i, Div, lhs, rhs) }
| lhs = expr_no_deref; EQ; rhs = expr_no_deref { BinOp(get i, Eq, lhs, rhs) }
| lhs = expr_no_deref; NE; rhs = expr_no_deref { BinOp(get i, Ne, lhs, rhs) }
| lhs = expr_no_deref; LE; rhs = expr_no_deref { BinOp(get i, Le, lhs, rhs) }
| lhs = expr_no_deref; LT; rhs = expr_no_deref { BinOp(get i, Lt, lhs, rhs) }
| lhs = expr_no_deref; GE; rhs = expr_no_deref { BinOp(get i, Ge, lhs, rhs) }
| lhs = expr_no_deref; GT; rhs = expr_no_deref { BinOp(get i, Gt, lhs, rhs) }
| lhs = expr_no_deref; AND; rhs = expr_no_deref { BinOp(get i, And, lhs, rhs) }
| lhs = expr_no_deref; OR; rhs = expr_no_deref { BinOp(get i, Or, lhs, rhs) }
;

term_no_deref:
| n = NUM { Num(get i, n) }
| SUB; n = NUM { Num(get i, -n) }
| TRUE { Bool(get i, true) }
| FALSE { Bool(get i, false) }
| NULL { Null(get i) }
| NOT; TRUE { Bool(get i, false) }
| NOT; FALSE { Bool(get i, true) }
| LPARAN; e = expr_no_deref; RPARAN { e }
| SUB; LPARAN; e = expr_no_deref; RPARAN { BinOp(get i, Sub, Num(get i, 0), e) }
| NOT; LPARAN; e = expr_no_deref; RPARAN { BinOp(get i, Eq, e, Bool(get i, false)) }
| SUB; id = ID { BinOp(get i, Sub, Num(get i, 0), Id(get i, id)) }
| NOT; id = ID { BinOp(get i, Eq, Id(get i, id), Bool(get i, false)) }
| id = ID; { Id(get i, id) }
;
