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

(** Type of the heap *)
type type_heap = ((types list) TypeHeapMap.t)

(** Exception used by the type checker *)
exception TypeCheckError of string

let rec type_check (expr: Ast.expression) (env: type_environment) (h: type_heap) : types * type_heap = match expr with
| Num(_) -> (Num, h)
| Bool(_) -> (Bool, h)
| Unit -> (Unit, h)
| BinOp(op, lhs, rhs) ->
    let (lhs, h) = type_check lhs env h in
      let (rhs, h) = type_check rhs env h in
        ((match (op, lhs, rhs) with
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
        ), h)
| Id(id) -> (env |> TypeEnvironmentMap.find id, h)
| Let(id, bound, body) ->
    let (bound, h) = type_check bound env h in
      let env = env |> TypeEnvironmentMap.add id bound in
        type_check body env h
(* TODO: how to handle state tracking for conditions? *)
| Cond(cond, then_body, else_body) -> ((match (type_check cond env h, type_check then_body env h, type_check else_body env h) with
  | ((Bool, _), (lhs, _), (rhs, _)) -> if lhs == rhs then lhs else raise (TypeCheckError "Cond requires both branches to have the same type!")
  | _ -> raise (TypeCheckError "Cond requires a bool as condition!")
  ), h)
(* TODO: how to handle state tracking for sequences? *)
| Seq(expr0, expr1) ->
    let _ = type_check expr0 env h in
      type_check expr1 env h
| _ -> raise (TypeCheckError "TODO: implement all cases")