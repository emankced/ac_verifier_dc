open Ast

(** Map that holds the environment store *)
module TypeEnvironmentMap = Map.Make(String)

(** Map that holds the heap store *)
module TypeHeapMap = Map.Make(Int)

type types =
| Loc
| Num
| Bool
| Unit
| Unknown

(** Type of the environment *)
type type_environment = (types TypeEnvironmentMap.t)

(** Exception used by the type checker *)
exception TypeCheckError of string

let type_check_id = "type"
let get_type_id (t: types) : string = match t with
| Loc -> "Loc"
| Num -> "Num"
| Bool -> "Bool"
| Unit -> "Unit"
| Unknown -> "Unknown"

let rec type_check (annotation: Ast.expression) (env: type_environment) : types * Ast.expression = match annotation with
| Annotation(notes, expr) ->
  (match expr with
  | Num(_) -> (Num, Annotation((type_check_id, get_type_id Num) :: notes, expr))
  | Bool(_) -> (Bool, Annotation((type_check_id, get_type_id Bool) :: notes, expr))
  | Unit -> (Unit, Annotation((type_check_id, get_type_id Unit) :: notes, expr))
  | BinOp(op, lhs, rhs) ->
      let (lhs, lhs_expr) = type_check lhs env in
        let (rhs, rhs_expr) = type_check rhs env in
          let t = (match (op, lhs, rhs) with
          | (Add, Num, Num) -> Num
          | (Sub, Num, Num) -> Num
          | (Mul, Num, Num) -> Num
          | (Div, Num, Num) -> Num
          | (Add, Loc, Num) -> Loc
          | (Sub, Loc, Num) -> Loc
          | (Add, Num, Loc) -> Loc
          | (Sub, Num, Loc) -> Loc
          | (Eq, Num, Num) -> Bool
          | (Ne, Num, Num) -> Bool
          | (Eq, Bool, Bool) -> Bool
          | (Ne, Bool, Bool) -> Bool
          | (Eq, Loc, Loc) -> Bool
          | (Ne, Loc, Loc) -> Bool
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
      let (bound, bound_expr) = type_check bound env in
        let env = env |> TypeEnvironmentMap.add id bound in
          let (body, body_expr) = type_check body env in
            (body, Annotation((type_check_id, get_type_id body) :: notes, Let(id, bound_expr, body_expr)))
  (* TODO: how to handle state tracking for conditions? *)
  | Cond(cond, then_body, else_body) ->
    ((match (type_check cond env, type_check then_body env, type_check else_body env) with
    | ((Bool, cond), (lhs, then_body), (rhs, else_body)) -> if lhs == rhs then (lhs, Annotation((type_check_id, get_type_id lhs) :: notes, Cond(cond, then_body, else_body))) else raise (TypeCheckError "Cond requires both branches to have the same type!")
    | _ -> raise (TypeCheckError "Cond requires a bool as condition!")
    ))
  (* TODO: how to handle state tracking for sequences? *)
  | Seq(expr0, expr1) ->
      let (_, expr0) = type_check expr0 env in
        let (t, expr1) = type_check expr1 env in
          (t, Annotation((type_check_id, get_type_id t) :: notes, Seq(expr0, expr1)))
  | _ -> raise (TypeCheckError "TODO: implement all cases")
  )
| _ -> raise (TypeCheckError "Expected Annotation node!")

let rec prepare_annotation (expr: Ast.expression) : Ast.expression = match expr with
| Loc(_) -> Annotation([], expr)
| Num(_) -> Annotation([], expr)
| Bool(_) -> Annotation([], expr)
| Unit -> Annotation([], expr)
| Let(id, bound, body) -> Annotation([], Let(id, prepare_annotation bound, prepare_annotation body))
| Id(_) -> Annotation([], expr)
| Cond(cond, then_body, else_body) -> Annotation([], Cond(prepare_annotation cond, prepare_annotation then_body, prepare_annotation else_body))
| BinOp(op, lhs, rhs) -> Annotation([], BinOp(op, prepare_annotation lhs, prepare_annotation rhs))
| Seq(expr0, expr1) -> Annotation([], Seq(prepare_annotation expr0, prepare_annotation expr1))
| _ -> exit 1 (* TODO: rest of AST nodes *)
