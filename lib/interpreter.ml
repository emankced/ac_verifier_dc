module EnvironmentMap = Map.Make(String)
module HeapMap = Map.Make(Int)

type values =
| Loc of int
| Num of int
| Bool of bool
| Unit

(** HObjs are still TODO *)

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

type expression =
| Loc of int
| Num of int
| Bool of bool
| Unit
| Let of string * expression * expression
| Id of string
| Cond of expression * expression * expression
| BinOp of binop * expression * expression
| Seq of expression * expression

(** HObjs are still TODO *)
(** ops *)
(** while do *)
(** for in to do *)
(** deref *)
(** setref *)
(** HCmds like malloc and free *)

type environment = (values EnvironmentMap.t)
type heap = (values HeapMap.t)
exception InterpreterException of string

let rec interp (expr: expression) (env: environment) (h: heap) : values * heap = match expr with
| Loc(l) -> (Loc(l), h)
| Num(n) -> (Num(n), h)
| Bool(b) -> (Bool(b), h)
| Unit -> (Unit, h)
| Let(id, bound, body) ->
    let (bound, h) = interp bound env h in
      let env = env |> EnvironmentMap.add id bound in
        interp body env h
| Id(id) -> (env |> EnvironmentMap.find id, h)
| Cond(cond, then_body, else_body) -> let (cond, h) = interp cond env h in
    (match cond with
    | Bool(b) -> if b then interp then_body env h else interp else_body env h
    | _ -> raise (InterpreterException "Cond requires a bool!")
    )
| BinOp(op, lhs, rhs) ->
    let (lhs, h) = interp lhs env h in
      let (rhs, h) = interp rhs env h in
        (match (op, lhs, rhs) with
        | (Add, Num(lhs), Num(rhs)) -> (Num(lhs + rhs), h)
        | (Sub, Num(lhs), Num(rhs)) -> (Num(lhs - rhs), h)
        | (Mul, Num(lhs), Num(rhs)) -> (Num(lhs * rhs), h)
        | (Div, Num(lhs), Num(rhs)) -> (Num(lhs / rhs), h)
        | (Eq, Num(lhs), Num(rhs)) -> (Bool(lhs == rhs), h)
        | (Eq, Bool(lhs), Bool(rhs)) -> (Bool(lhs == rhs), h)
        | (Ne, Num(lhs), Num(rhs)) -> (Bool(lhs != rhs), h)
        | (Ne, Bool(lhs), Bool(rhs)) -> (Bool(lhs != rhs), h)
        | (Le, Num(lhs), Num(rhs)) -> (Bool(lhs <= rhs), h)
        | (Lt, Num(lhs), Num(rhs)) -> (Bool(lhs < rhs), h)
        | (Ge, Num(lhs), Num(rhs)) -> (Bool(lhs >= rhs), h)
        | (Gt, Num(lhs), Num(rhs)) -> (Bool(lhs > rhs), h)
        | _ -> raise (InterpreterException "Unsupported binary operation!")
        )
| Seq(expr0, expr1) -> let (_, h) = interp expr0 env h in interp expr1 env h
