(** Map that holds the environment store *)
module EnvironmentMap = Map.Make(String)

(** Map that holds the heap store *)
module HeapMap = Map.Make(Int)

(** Return values of the interpreter *)
type values =
| Loc of int
| Num of int
| Bool of bool
| Unit
(* closures *)

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

(** Expressions as AST *)
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
| Malloc of expression list
| Mset of expression * expression
| Mget of expression
| Mfree of expression
| While of expression * expression
| For of string * expression * expression * expression
(* functions *)
(* recursive let *)

(** Type of the environment *)
type environment = (values EnvironmentMap.t)

(** Type of the heap *)
type heap = ((values list) HeapMap.t)

(** Exception used by the interpreter *)
exception InterpreterException of string

(** Memory allocation on the heap *)
let malloc (init_values: values list) (h: heap) : int * heap =
  if List.length init_values == 0 then
    raise (InterpreterException "malloc cannot allocate nothing")
  else
    let max_available_loc =
      HeapMap.fold
        (fun loc values_list previous_max ->
          let size = List.length values_list in
            let loc = loc + size in
              if loc > previous_max then loc else previous_max)
        h
        0
    in
      (max_available_loc, h |> HeapMap.add max_available_loc init_values)

(** Memory deallocation on the heap *)
let mfree (loc: int) (h: heap) : heap = h |> HeapMap.remove loc

(** Memory featching from the heap *)
let mget (loc: int) (h: heap) : values =
  if HeapMap.is_empty h then
    raise (InterpreterException "mget cannot get anything from an empty heap!")
  else
    let (hloc, values_list) =
      HeapMap.fold
        (fun hloc values_list (previous_hloc, previous_values_list) ->
          if hloc <= loc && hloc > previous_hloc then (hloc, values_list) else (previous_hloc, previous_values_list))
        h
        (-1, [])
      in
        let offset = loc - hloc in
          if offset >= List.length values_list then
            raise (InterpreterException ("mget got location out of range: " ^ string_of_int loc))
          else
            List.nth values_list offset

(** Replace nth element if the type matches *)
let rec replace_nth (l: values list) (v: values) (n: int) : values list =
  match l with
  | [] -> []
  | (x :: xs) ->
      if n == 0 then
        (match (x, v) with
        | (Num(_), Num(_)) -> v :: xs
        | (Loc(_), Loc(_)) -> v :: xs
        | (Bool(_), Bool(_)) -> v :: xs (* should unit even be allowed on heap? it doesn't hold a value and data types cannot be changed afeterwards... *)
        | (Unit, Unit) -> v :: xs
        | _ -> raise (InterpreterException "mset cannot change data type of field!")
        )
      else
        x :: replace_nth xs v (n-1)

(** Memory mutation on the heap *)
let mset (loc: int) (v: values) (h: heap) : heap =
  if HeapMap.is_empty h then
    raise (InterpreterException "mset cannot set anything on an empty heap!")
  else
    let (hloc, values_list) =
      HeapMap.fold
        (fun hloc values_list (previous_hloc, previous_values_list) ->
          if hloc <= loc && hloc > previous_hloc then (hloc, values_list) else (previous_hloc, previous_values_list))
        h
        (-1, [])
      in
        let offset = loc - hloc in
          if offset >= List.length values_list then
            raise (InterpreterException ("mget got offset out of range: " ^ string_of_int loc))
          else
            let values_list = replace_nth values_list v offset in
              h |> HeapMap.add hloc values_list

(** Evaluates expressions based on an environment and heap *)
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
| Cond(cond, then_body, else_body) ->
    let (cond, h) = interp cond env h in
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
        | (Add, Loc(lhs), Loc(rhs)) -> (Loc(lhs + rhs), h)
        | (Sub, Loc(lhs), Loc(rhs)) -> (Loc(lhs - rhs), h)
        | (Mul, Loc(lhs), Loc(rhs)) -> (Loc(lhs * rhs), h)
        | (Div, Loc(lhs), Loc(rhs)) -> (Loc(lhs / rhs), h)
        | (Add, Loc(lhs), Num(rhs)) -> (Loc(lhs + rhs), h)
        | (Sub, Loc(lhs), Num(rhs)) -> (Loc(lhs - rhs), h)
        | (Mul, Loc(lhs), Num(rhs)) -> (Loc(lhs * rhs), h)
        | (Div, Loc(lhs), Num(rhs)) -> (Loc(lhs / rhs), h)
        | (Add, Num(lhs), Loc(rhs)) -> (Loc(lhs + rhs), h)
        | (Sub, Num(lhs), Loc(rhs)) -> (Loc(lhs - rhs), h)
        | (Mul, Num(lhs), Loc(rhs)) -> (Loc(lhs * rhs), h)
        | (Div, Num(lhs), Loc(rhs)) -> (Loc(lhs / rhs), h)
        | (Eq, Num(lhs), Num(rhs)) -> (Bool(lhs == rhs), h)
        | (Ne, Num(lhs), Num(rhs)) -> (Bool(lhs != rhs), h)
        | (Eq, Bool(lhs), Bool(rhs)) -> (Bool(lhs == rhs), h)
        | (Ne, Bool(lhs), Bool(rhs)) -> (Bool(lhs != rhs), h)
        | (Eq, Loc(lhs), Loc(rhs)) -> (Bool(lhs == rhs), h)
        | (Ne, Loc(lhs), Loc(rhs)) -> (Bool(lhs != rhs), h)
        (* should unit get a comparison definition? *)
        | (Le, Num(lhs), Num(rhs)) -> (Bool(lhs <= rhs), h)
        | (Lt, Num(lhs), Num(rhs)) -> (Bool(lhs < rhs), h)
        | (Ge, Num(lhs), Num(rhs)) -> (Bool(lhs >= rhs), h)
        | (Gt, Num(lhs), Num(rhs)) -> (Bool(lhs > rhs), h)
        | (Le, Loc(lhs), Loc(rhs)) -> (Bool(lhs <= rhs), h)
        | (Lt, Loc(lhs), Loc(rhs)) -> (Bool(lhs < rhs), h)
        | (Ge, Loc(lhs), Loc(rhs)) -> (Bool(lhs >= rhs), h)
        | (Gt, Loc(lhs), Loc(rhs)) -> (Bool(lhs > rhs), h)
        | _ -> raise (InterpreterException "Unsupported binary operation!")
        )
| Seq(expr0, expr1) -> let (_, h) = interp expr0 env h in interp expr1 env h
| Malloc(exprs) ->
    let (values_list, h) =
      List.fold_right
        (fun expr (values_list, h) ->
          let (v, h) = interp expr env h in
            (v :: values_list, h))
        exprs
        ([], h)
      in
        let (loc, h) = malloc values_list h in
          (Loc(loc), h)
| Mfree(loc) ->
    let (loc, h) = interp loc env h in
      (match loc with
      | Loc(l) -> (Unit, mfree l h)
      | _ -> raise (InterpreterException "Mfree requires a location!")
      )
| Mget(loc) ->
    let (loc, h) = interp loc env h in
      (match loc with
      | Loc(l) -> (mget l h, h)
      | _ -> raise (InterpreterException "Mget requires a location!")
      )
| Mset(loc, expr) ->
    let (loc, h) = interp loc env h in
      (match loc with
      | Loc(l) ->
        let (expr, h) = interp expr env h in
          (Unit, mset l expr h)
      | _ -> raise (InterpreterException "Mset requires a location!")
      )
| While(condition, body) ->
  let (condition, h) = interp condition env h in
    (match condition with
    | Bool(condition) ->
      if condition
        then let (_, h) = interp body env h in
          interp expr env h
        else (Unit, h)
    | _ -> raise (InterpreterException "While requires a bool!")
    )
| For(id, start, end_, body) ->
  let (start, h) = interp start env h in
    let (end_, h) = interp end_ env h in
      let env = env |> EnvironmentMap.add id start in
        (match (start, end_) with
        | (Num(start), Num(end_)) ->
          let (_, h) = interp body env h in
            if start == end_ then
              (Unit, h)
            else if start < end_ then
              interp (For(id, Num(start+1), Num(end_), body)) env h
            else
              interp (For(id, Num(start-1), Num(end_), body)) env h
        | _ -> raise (InterpreterException "For requires numbers for iterating!")
        )

let (==) (lhs: values) (rhs: values) : bool = match (lhs, rhs) with
| (Num(lhs), Num(rhs)) -> lhs == rhs
| (Loc(lhs), Loc(rhs)) -> lhs == rhs
| (Bool(lhs), Bool(rhs)) -> lhs == rhs
| _ -> false

let (!=) (lhs: values) (rhs: values) : bool = not (lhs == rhs)

let rec string_of_expression (expr: expression) : string = match expr with
| Num(n) -> "Num(" ^ string_of_int n ^ ")"
| Bool(b) -> "Bool(" ^ (if b then "true" else "false") ^ ")"
| Loc(l) -> "Loc(" ^ string_of_int l ^ ")"
| Unit -> "Unit"
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
    )
  in
    "BinOp(" ^ op ^ ", " ^ (string_of_expression lhs) ^ ", " ^ (string_of_expression rhs) ^ ")"
| Id(id) -> "Id(" ^ id ^ ")"
| _ -> "unsupported"
