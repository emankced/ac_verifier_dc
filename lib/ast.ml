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
type struct_types =
| Num
| Bool
| LocStruct of string

(** ID type used to uniquely identify AST nodes *)
type ast_id = int

(** Expressions as AST *)
type expression =
| Null of ast_id
| Num of ast_id * int
| Bool of ast_id * bool
| Unit of ast_id
| Let of ast_id * string * expression * expression
| Struct of ast_id * string * ((string * struct_types) list) * expression
| Id of ast_id * string
| Cond of ast_id * expression * expression * expression
| BinOp of ast_id * binop * expression * expression
| Seq of ast_id * expression * expression
| Malloc of ast_id * string * (expression list)
| Mset of ast_id * expression * string * expression
| Mget of ast_id * expression * string
| Mfree of ast_id * expression
| While of ast_id * expression * expression
| For of ast_id * string * expression * expression * expression
| Assert of ast_id * expression * expression
(* functions *)
(* recursive let *)

let string_of_struct_type (t: struct_types) : string = match t with
| Num -> "Num"
| Bool -> "Bool"
| LocStruct(id) -> "LocStruct(" ^ id ^ ")"

let rec string_of_expression (expr: expression) : string = match expr with
| Num(i, n) -> "Num:" ^ string_of_int i ^ "(" ^ string_of_int n ^ ")"
| Bool(i, b) -> "Bool:" ^ string_of_int i ^ "(" ^ (if b then "true" else "false") ^ ")"
| Null(i) -> "Null:" ^ string_of_int i
| Unit(i) -> "Unit:" ^ string_of_int i
| Struct(i, name, types, body) -> "Struct:" ^ string_of_int i ^ "(" ^ name ^ ", [" ^
    List.fold_right (fun (f, t) s -> if String.equal s "" then f ^ ": " ^ string_of_struct_type t else f ^ ": " ^ string_of_struct_type t ^
    "; " ^ s) types "" ^ "], " ^ string_of_expression body ^ ")"
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
| Assert(i, assertion, command) -> "Assert:" ^ string_of_int i ^ "(" ^ string_of_expression assertion ^ ", " ^ string_of_expression command ^ ")"

(** returns the ast_id of an ast expression *)
let get_ast_id (expr: expression) : ast_id = match expr with
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
| Assert(i, _, _) -> i
