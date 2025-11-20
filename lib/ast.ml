(** Binary operators *)
type binop =
| Add
| Sub
| Mul
| Div
| Eq
| Ne
| Le
| Lt
| Ge
| Gt
| And
| Or
| Sep
| SepImp
| PointsTo

(** Types used creating a struct *)
type struct_type =
| NumT
| BoolT
(*| LocStruct of string*)

(** Expressions as AST *)
type expression =
| Null of int
| Num of int * int
| Bool of int * bool
| Unit of int
| Let of int * string * expression * expression
| Struct of int * string * ((string * struct_type) list) * expression
| Id of int * string
| Cond of int * expression * expression * expression
| BinOp of int * binop * expression * expression
| Seq of int * expression * expression
| Malloc of int * string * (expression list)
| Mset of int * expression * string * expression
| Mget of int * expression * string
| Mfree of int * expression
| While of int * expression * expression
| For of int * string * expression * expression * expression
| Invariant of int * expression * expression
| Assert of int * expression
(* functions *)
(* recursive let *)

let string_of_struct_type (t: struct_type) : string = match t with
| NumT -> "Num"
| BoolT -> "Bool"
(*| LocStruct(id) -> "LocStruct(" ^ id ^ ")"*)

let rec string_of_expression (expr: expression) : string = match expr with
| Num(i, n) -> "Num:" ^ string_of_int i ^ "(" ^ string_of_int n ^ ")"
| Bool(i, b) -> "Bool:" ^ string_of_int i ^ "(" ^ (if b then "true" else "false") ^ ")"
| Null(i) -> "Null:" ^ string_of_int i
| Unit(i) -> "Unit:" ^ string_of_int i
| Struct(i, name, fields, body) -> "Struct:" ^ string_of_int i ^ "(" ^ name ^ ", [" ^
    List.fold_right (fun (f, t) s -> if String.equal s "" then f ^ ": " ^ string_of_struct_type t else f ^ ": " ^ string_of_struct_type t ^
    "; " ^ s) fields "" ^ "], " ^ string_of_expression body ^ ")"
| BinOp(i, op, lhs, rhs) ->
  let op = (match op with
    | Add -> "Add"
    | Sub -> "Sub"
    | Mul -> "Mul"
    | Div -> "Div"
    | Eq -> "Eq"
    | Ne -> "Ne"
    | Le -> "Le"
    | Lt -> "Lt"
    | Ge -> "Ge"
    | Gt -> "Gt"
    | And -> "And"
    | Or -> "Or"
    | Sep -> "Sep"
    | SepImp -> "SepImp"
    | PointsTo -> "PointsTo"
    )
  in
    "BinOp:" ^ string_of_int i ^ "(" ^ op ^ ", " ^ (string_of_expression lhs) ^ ", " ^ (string_of_expression rhs) ^ ")"
| Id(i, id) -> "Id:" ^ string_of_int i ^ "(\"" ^ id ^ "\")"
| Let(i, id, bound, body) -> "Let:" ^ string_of_int i ^ "(\"" ^ id ^ "\", " ^ string_of_expression bound ^ ", " ^ string_of_expression body ^ ")"
| Cond(i, cond, then_body, else_body) -> "Cond:" ^ string_of_int i ^ "(" ^ string_of_expression cond ^ ", " ^ string_of_expression then_body ^ ", " ^ string_of_expression else_body ^ ")"
| Seq(i, expr0, expr1) -> "Seq:" ^ string_of_int i ^ "(" ^ string_of_expression expr0 ^ ", " ^ string_of_expression expr1 ^ ")"
| Malloc(i, id, exprs) -> "Malloc:" ^ string_of_int i ^ "(" ^ id ^ ", [" ^ (List.fold_right (fun e s -> if String.equal s "" then string_of_expression e else string_of_expression e ^ "; " ^ s) exprs "") ^ "])"
| Mfree(i, loc) -> "Mfree:" ^ string_of_int i ^ "(" ^ string_of_expression loc ^ ")"
| Mset(i, loc, field, expr) -> "Mset:" ^ string_of_int i ^ "(" ^ string_of_expression loc ^ ", " ^ field ^ ", " ^ string_of_expression expr ^ ")"
| Mget(i, loc, field) -> "Mget:" ^ string_of_int i ^ "(" ^ string_of_expression loc ^ ", " ^ field ^ ")"
| For(i, id, start, end_, body) -> "For:" ^ string_of_int i ^ "(\"" ^ id ^ "\", " ^ string_of_expression start ^ ", " ^ string_of_expression end_ ^ ", " ^ string_of_expression body ^ ")"
| While(i, cond, body) -> "While:" ^ string_of_int i ^ "(" ^ string_of_expression cond ^ ", " ^ string_of_expression body ^ ")"
| Assert(i, assertion) -> "Assert:" ^ string_of_int i ^ "(" ^ string_of_expression assertion ^ ")"
| Invariant(i, inv, loop) -> "Invariant:" ^ string_of_int i ^ "(" ^ string_of_expression inv ^ "," ^ string_of_expression loop ^ ")"

(** returns the int of an ast expression *)
let get_ast_id (expr: expression) : int = match expr with
| Null(i) -> i
| Num(i, _) -> i
| Bool(i, _) -> i
| Unit(i) -> i
| Let(i, _, _, _) -> i
| Struct(i, _, _, _) -> i
| Id(i, _) -> i
| Cond(i, _, _, _) -> i
| BinOp(i, _, _, _) -> i
| Seq(i, _, _) -> i
| Malloc(i, _, _) -> i
| Mset(i, _, _, _) -> i
| Mget(i, _, _) -> i
| Mfree(i, _) -> i
| While(i, _, _) -> i
| For(i, _, _, _, _) -> i
| Assert(i, _) -> i
| Invariant(i, _, _) -> i
