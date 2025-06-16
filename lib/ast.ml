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

(** Expressions as AST *)
type expression =
| Loc of int
| Num of int
| Bool of bool
| Unit
| Let of string * expression * expression
| Struct of string * (struct_types list) * expression
| Id of string
| Cond of expression * expression * expression
| BinOp of binop * expression * expression
| Seq of expression * expression
| Malloc of string * (expression list)
| Mset of expression * expression
| Mget of expression
| Mfree of expression
| While of expression * expression
| For of string * expression * expression * expression
| Assert of expression * expression
| Annotation of (string * string) list * expression (* notes consist of key and value pairs *)
(* functions *)
(* recursive let *)

let string_of_struct_type (t: struct_types) : string = match t with
| Num -> "Num"
| Bool -> "Bool"
| LocStruct(id) -> "LocStruct(" ^ id ^ ")"

let rec string_of_expression (expr: expression) : string = match expr with
| Num(n) -> "Num(" ^ string_of_int n ^ ")"
| Bool(b) -> "Bool(" ^ (if b then "true" else "false") ^ ")"
| Loc(l) -> "Loc(" ^ string_of_int l ^ ")"
| Unit -> "Unit"
| Struct(name, types, body) -> "Struct(" ^ name ^ ", [" ^
    List.fold_right (fun t s -> if String.equal s "" then string_of_struct_type t else string_of_struct_type t ^
    "; " ^ s) types "" ^ "], " ^ string_of_expression body ^ ")"
| BinOp(op, lhs, rhs) ->
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
    "BinOp(" ^ op ^ ", " ^ (string_of_expression lhs) ^ ", " ^ (string_of_expression rhs) ^ ")"
| Id(id) -> "Id(\"" ^ id ^ "\")"
| Let(id, bound, body) -> "Let(\"" ^ id ^ "\", " ^ string_of_expression bound ^ ", " ^ string_of_expression body ^ ")"
| Cond(cond, then_body, else_body) -> "Cond(" ^ string_of_expression cond ^ ", " ^ string_of_expression then_body ^ ", " ^ string_of_expression else_body ^ ")"
| Seq(expr0, expr1) -> "Seq(" ^ string_of_expression expr0 ^ ", " ^ string_of_expression expr1 ^ ")"
| Malloc(id, exprs) -> "Malloc(" ^ id ^ ", [" ^ (List.fold_right (fun e s -> if String.equal s "" then string_of_expression e else string_of_expression e ^ "; " ^ s) exprs "") ^ "])"
| Mfree(loc) -> "Mfree(" ^ string_of_expression loc ^ ")"
| Mset(loc, expr) -> "Mset(" ^ string_of_expression loc ^ ", " ^ string_of_expression expr ^ ")"
| Mget(loc) -> "Mget(" ^ string_of_expression loc ^ ")"
| For(id, start, end_, body) -> "For(\"" ^ id ^ "\", " ^ string_of_expression start ^ ", " ^ string_of_expression end_ ^ ", " ^ string_of_expression body ^ ")"
| While(cond, body) -> "While(" ^ string_of_expression cond ^ ", " ^ string_of_expression body ^ ")"
| Assert(assertion, command) -> "Assert(" ^ string_of_expression assertion ^ ", " ^ string_of_expression command ^ ")"
| Annotation(notes, expr) -> "Annotation([" ^ List.fold_right (fun (k, v) s -> (if String.equal s "" then "(" else s ^ "; (") ^ k ^ ", " ^ v ^ ")") notes "" ^ "], " ^ string_of_expression expr ^ ")"
