open Ast

(** Map that holds the environment store *)
module TypeEnvironmentMap = Map.Make(String)

(** Map that holds the heap store *)
module TypeHeapMap = Map.Make(Int)

type types =
| Null
| Loc of string
| Num
| Bool
| Unit
| Unknown

(** Type of the environment map *)
type type_environment = (types TypeEnvironmentMap.t)

(** Type of the struct definition map *)
type struct_type_definitions = (types list TypeEnvironmentMap.t)

(** Exception used by the type checker *)
exception TypeCheckError of string

let type_check_id = "type"
let get_type_id (t: types) : string = match t with
| Null -> "Null"
| Loc(id) -> "Loc(" ^ id ^ ")"
| Num -> "Num"
| Bool -> "Bool"
| Unit -> "Unit"
| Unknown -> "Unknown"

let rec type_check (annotation: Ast.expression) (env: type_environment) (sdef: struct_type_definitions) : types * Ast.expression = match annotation with
| Annotation(notes, expr) ->
  (match expr with
  | Null -> (Null, Annotation((type_check_id, get_type_id Null) :: notes, expr))
  | Num(_) -> (Num, Annotation((type_check_id, get_type_id Num) :: notes, expr))
  | Bool(_) -> (Bool, Annotation((type_check_id, get_type_id Bool) :: notes, expr))
  | Unit -> (Unit, Annotation((type_check_id, get_type_id Unit) :: notes, expr))
  | BinOp(op, lhs, rhs) ->
      let (lhs, lhs_expr) = type_check lhs env sdef in
        let (rhs, rhs_expr) = type_check rhs env sdef in
          let t = (match (op, lhs, rhs) with
          | (Add, Num, Num) -> Num
          | (Sub, Num, Num) -> Num
          | (Mul, Num, Num) -> Num
          | (Div, Num, Num) -> Num
          | (Add, Loc(id), Num) -> Loc(id)
          | (Sub, Loc(id), Num) -> Loc(id)
          | (Add, Num, Loc(id)) -> Loc(id)
          | (Sub, Num, Loc(id)) -> Loc(id)
          | (Eq, Num, Num) -> Bool
          | (Ne, Num, Num) -> Bool
          | (Eq, Bool, Bool) -> Bool
          | (Ne, Bool, Bool) -> Bool
          | (Eq, Loc(_), Loc(_)) -> Bool
          | (Ne, Loc(_), Loc(_)) -> Bool
          (* should unit get a comparison definition? *)
          | (Le, Num, Num) -> Bool
          | (Lt, Num, Num) -> Bool
          | (Ge, Num, Num) -> Bool
          | (Gt, Num, Num) -> Bool
          | (And, Bool, Bool) -> Bool
          | (Or, Bool, Bool) -> Bool
          | _ -> raise (TypeCheckError "BinOp: Operator and operands do not match!")
          ) in (t, Annotation((type_check_id, get_type_id t) :: notes, BinOp(op, lhs_expr, rhs_expr)))
  | Id(id) -> let t = env |> TypeEnvironmentMap.find id in (t, Annotation((type_check_id, get_type_id t) :: notes, expr))
  | Let(id, bound, body) ->
      let (bound, bound_expr) = type_check bound env sdef in
        let env = env |> TypeEnvironmentMap.add id bound in
          let (body, body_expr) = type_check body env sdef in
            (body, Annotation((type_check_id, get_type_id body) :: notes, Let(id, bound_expr, body_expr)))
  | Cond(cond, then_body, else_body) ->
    (match (type_check cond env sdef, type_check then_body env sdef, type_check else_body env sdef) with
    | ((Bool, cond), (lhs, then_body), (rhs, else_body)) -> if lhs == rhs then (lhs, Annotation((type_check_id, get_type_id lhs) :: notes, Cond(cond, then_body, else_body))) else raise (TypeCheckError "Cond requires both branches to have the same type!")
    | _ -> raise (TypeCheckError "Cond requires a bool as condition!")
    )
  | Seq(expr0, expr1) ->
      let (_, expr0) = type_check expr0 env sdef in
        let (t, expr1) = type_check expr1 env sdef in
          (t, Annotation((type_check_id, get_type_id t) :: notes, Seq(expr0, expr1)))
  | Struct(id, types, body) ->
      if TypeEnvironmentMap.exists (fun k _ -> String.equal id k) sdef || TypeEnvironmentMap.exists (fun k _ -> String.equal id k) env then
        raise (TypeCheckError "Struct name is already taken!")
      else
        let sdef = sdef |> TypeEnvironmentMap.add id (List.map (fun (t: struct_types) -> match t with
          | Num -> Num
          | Bool -> Bool
          | LocStruct(name) -> if String.equal id name || TypeEnvironmentMap.exists (fun k _ -> String.equal k name) sdef then Loc(name) else raise (TypeCheckError "Struct type does not exists!")
          ) types) in
        let (t, body) = type_check body env sdef in
          (t, Annotation((type_check_id, get_type_id t) :: notes, Struct(id, types, body)))
  | _ -> raise (TypeCheckError "TODO: implement all cases")
  )
| _ -> raise (TypeCheckError "Expected Annotation node!")

(** Exception used by the annotation preparation *)
exception PrepareAnnotationException of string

(** Wraps every AST node with an Annotation node *)
let rec prepare_annotation (expr: Ast.expression) : Ast.expression = match expr with
| Null -> Annotation([], expr)
| Num(_) -> Annotation([], expr)
| Bool(_) -> Annotation([], expr)
| Unit -> Annotation([], expr)
| Let(id, bound, body) -> Annotation([], Let(id, prepare_annotation bound, prepare_annotation body))
| Id(_) -> Annotation([], expr)
| Cond(cond, then_body, else_body) -> Annotation([], Cond(prepare_annotation cond, prepare_annotation then_body, prepare_annotation else_body))
| BinOp(op, lhs, rhs) -> Annotation([], BinOp(op, prepare_annotation lhs, prepare_annotation rhs))
| Seq(expr0, expr1) -> Annotation([], Seq(prepare_annotation expr0, prepare_annotation expr1))
| Struct(id, types, body) -> Annotation([], Struct(id, types, prepare_annotation body))
| Assert(assertion, command) -> Annotation([], Assert(prepare_annotation assertion, prepare_annotation command))
| Malloc(id, exprs) -> Annotation([], Malloc(id, List.map (fun e -> prepare_annotation e) exprs))
| Mfree(loc) -> Annotation([], Mfree(prepare_annotation loc))
| Mset(loc, expr) -> Annotation([], Mset(prepare_annotation loc, prepare_annotation expr))
| Mget(loc) -> Annotation([], Mget(prepare_annotation loc))
| For(id, start, end_, body) -> Annotation([], For(id, prepare_annotation start, prepare_annotation end_, prepare_annotation body))
| While(cond, body) -> Annotation([], While(prepare_annotation cond, prepare_annotation body))
| Annotation(_, _) -> raise (PrepareAnnotationException "This AST already contains Annotation nodes!")
