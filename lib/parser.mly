%{
open Ast
let i = ref 0
let get i = let v = !i in i := v+1; v
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
%token DOT

%token SEMICOLON

%token WHILE
%token DO
%token FOR
%token TO
%token LBRACKET
%token RBRACKET

%token ASSERT
%token RESULT
%token INVARIANT

%token STRUCT
%token LBRACE
%token RBRACE
%token INT
%token BOOL
%token COLON

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

type_list:
| f = ID; COLON; t = type_; COMMA; xs = type_list { (f, t) :: xs }
| f = ID; COLON; t = type_ { [(f, t)] }
;

type_:
| INT { NumT }
| BOOL { BoolT }
(* don't allow memory referencing on the heap *)
(*| id = ID { LocStruct(id) }*)
;

command:
| ASSERT; a = assrt; ASSERT { Assert(get i, a) }
| LET; id = ID; ASSIGN; value = command; IN; body = command { Let(get i, id, value, body) }
| IF; cond = expr; THEN; then_body = command; ELSE; else_body = command { Cond(get i, cond, then_body, else_body) }
| IF; cond = expr; THEN; then_body = command { Cond(get i, cond, then_body, Unit(get i)) }
| DEREF; id = ID; DOT; field = ID; ASSIGN; e = expr { Mset(get i, Id(get i, id), field, e) }
| MALLOC; LPARAN; id = ID; COMMA; l = expr_list; RPARAN { Malloc(get i, id, l) }
| MFREE; LPARAN; e = expr; RPARAN { Mfree(get i, e) }
| ASSERT; INVARIANT; inv = assrt; ASSERT; WHILE; cond = expr; DO; body = command { Invariant(get i, inv, While(get i, cond, body)) }
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
| NOT; TRUE { Bool(get i, false) }
| NOT; FALSE { Bool(get i, true) }
| LPARAN; e = expr; RPARAN { e }
| SUB; LPARAN; e = expr; RPARAN { BinOp(get i, Sub, Num(get i, 0), e) }
| NOT; LPARAN; e = expr; RPARAN { BinOp(get i, Eq, e, Bool(get i, false)) }
| DEREF; id = ID; DOT; field = ID { Mget(get i, Id(get i, id), field) }
| SUB; id = ID { BinOp(get i, Sub, Num(get i, 0), Id(get i, id)) }
| NOT; id = ID { BinOp(get i, Eq, Id(get i, id), Bool(get i, false)) }
| id = ID; { Id(get i, id) }
;

assrt:
| e = expr_with_result { e }
| lhs = assrt; SEP; rhs = assrt { BinOp(get i, Sep, lhs, rhs) }
(*| lhs = assrt; SEPIMP; rhs = assrt { BinOp(get i, SepImp, lhs, rhs) }*)
(*| lhs = assrt; POINTSTO; rhs = assrt { BinOp(get i, PointsTo, lhs, rhs) }*)
| LPARAN; e = assrt; RPARAN { e }
(* TODO: predicates, forall, (exists,) always *)
;

expr_with_result:
| t = term_with_result { t }
| lhs = expr_with_result; ADD; rhs = expr_with_result { BinOp(get i, Add, lhs, rhs) }
| lhs = expr_with_result; SUB; rhs = expr_with_result { BinOp(get i, Sub, lhs, rhs) }
| lhs = expr_with_result; MUL; rhs = expr_with_result { BinOp(get i, Mul, lhs, rhs) }
| lhs = expr_with_result; DIV; rhs = expr_with_result { BinOp(get i, Div, lhs, rhs) }
| lhs = expr_with_result; EQ; rhs = expr_with_result { BinOp(get i, Eq, lhs, rhs) }
| lhs = expr_with_result; NE; rhs = expr_with_result { BinOp(get i, Ne, lhs, rhs) }
| lhs = expr_with_result; LE; rhs = expr_with_result { BinOp(get i, Le, lhs, rhs) }
| lhs = expr_with_result; LT; rhs = expr_with_result { BinOp(get i, Lt, lhs, rhs) }
| lhs = expr_with_result; GE; rhs = expr_with_result { BinOp(get i, Ge, lhs, rhs) }
| lhs = expr_with_result; GT; rhs = expr_with_result { BinOp(get i, Gt, lhs, rhs) }
| lhs = expr_with_result; AND; rhs = expr_with_result { BinOp(get i, And, lhs, rhs) }
| lhs = expr_with_result; OR; rhs = expr_with_result { BinOp(get i, Or, lhs, rhs) }
;

term_with_result:
| n = NUM { Num(get i, n) }
| SUB; n = NUM { Num(get i, -n) }
| TRUE { Bool(get i, true) }
| FALSE { Bool(get i, false) }
| NOT; TRUE { Bool(get i, false) }
| NOT; FALSE { Bool(get i, true) }
| LPARAN; e = expr_with_result; RPARAN { e }
| SUB; LPARAN; e = expr_with_result; RPARAN { BinOp(get i, Sub, Num(get i, 0), e) }
| NOT; LPARAN; e = expr_with_result; RPARAN { BinOp(get i, Eq, e, Bool(get i, false)) }
| DEREF; id = ID; DOT; field = ID { Mget(get i, Id(get i, id), field) }
| SUB; id = ID { BinOp(get i, Sub, Num(get i, 0), Id(get i, id)) }
| NOT; id = ID { BinOp(get i, Eq, Id(get i, id), Bool(get i, false)) }
| RESULT {Id(get i, "result")}
| NOT; RESULT { BinOp(get i, Eq, Id(get i, "result"), Bool(get i, false)) }
| id = ID; { Id(get i, id) }
;
