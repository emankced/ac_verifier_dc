open Ast
open Common

(** Return values of the interpreter *)
type values =
| Loc of int * string (* base location and type id *)
| Num of int
| Bool of bool
| Unit
(* closures *)

(** Map that holds the environment store *)
type environment = (values StringMap.t)

(** Map that holds the struct definitions *)
type struct_definitions = ((string * struct_types) list StringMap.t)

(** Map that holds the heap store *)
type heap = ((values list) IntMap.t)

(** Exception used by the interpreter *)
exception InterpreterException of string

(** Memory allocation on the heap *)
let malloc (init_values: values list) (h: heap) : int * heap =
  if List.length init_values == 0 then
    raise (InterpreterException "malloc cannot allocate nothing")
  else
    let max_available_loc =
      IntMap.fold
        (fun loc values_list previous_max ->
          let size = List.length values_list in
            let loc = loc + size in
              if loc > previous_max then loc else previous_max)
        h
        0x400000
    in
      (max_available_loc, h |> IntMap.add max_available_loc init_values)

(** Memory deallocation on the heap *)
let mfree (loc: int) (h: heap) : heap = h |> IntMap.remove loc

(** Memory featching from the heap *)
let mget (loc: int) (field: string) (type_id: string) (h: heap) (sdef: struct_definitions) : values =
  if IntMap.is_empty h then
    raise (InterpreterException "mget cannot get anything from an empty heap!")
  else
    let td = sdef |> StringMap.find type_id in
    (match List.find_index (fun (tid, _) -> String.equal tid field) td with
    | Some off ->
    let values_list = IntMap.find loc h in
      if off < 0 || off >= List.length values_list then
        raise (InterpreterException ("mget got location out of range: " ^ string_of_int loc))
      else
        List.nth values_list off
    | None -> raise (InterpreterException ("mget: field could not be found: " ^ field))
    )

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
let mset (loc: int) (field: string) (type_id: string) (v: values) (h: heap) (sdef: struct_definitions) : heap =
  if IntMap.is_empty h then
    raise (InterpreterException "mset cannot set anything on an empty heap!")
  else
    let values_list = IntMap.find loc h in
    let td = sdef |> StringMap.find type_id in
    (match List.find_index (fun (tid, _) -> String.equal tid field) td with
    | Some off ->
      if off < 0 || off >= List.length values_list then
        raise (InterpreterException ("mget got offset out of range: " ^ string_of_int loc))
      else
        let values_list = replace_nth values_list v off in
          h |> IntMap.add loc values_list
    | None -> raise (InterpreterException ("mset: field could not be found: " ^ field))
    )

(** Evaluates expressions based on an environment and heap *)
let rec interp (expr: Ast.expression) (env: environment) (sdef: struct_definitions) (h: heap) : values * heap = match expr with
| Null(_i) -> (Loc(0, ""), h)
| Num(_i, n) -> (Num(n), h)
| Bool(_i, b) -> (Bool(b), h)
| Unit(_i) -> (Unit, h)
| Struct(_i, id, types, body) ->
    if List.length types == 0 then
      raise (InterpreterException "Type list cannot be empty for struct construction!")
    else if (StringMap.exists (fun k _ -> String.equal k id) env) || (StringMap.exists (fun k _ -> String.equal k id) sdef) then
      raise (InterpreterException "Struct name is already used!")
    else
      let sdef = sdef |> StringMap.add id types in
        interp body env sdef h
| Let(_i, id, bound, body) ->
    if (StringMap.exists (fun k _ -> String.equal k id) sdef) then
      raise (InterpreterException "Let ID already exists as struct name!")
    else
      let (bound, h) = interp bound env sdef h in
        let env = env |> StringMap.add id bound in
          interp body env sdef h
| Id(_i, id) -> (env |> StringMap.find id, h)
| Cond(_i, cond, then_body, else_body) ->
    let (cond, h) = interp cond env sdef h in
      (match cond with
      | Bool(b) -> if b then interp then_body env sdef h else interp else_body env sdef h
      | _ -> raise (InterpreterException "Cond requires a bool!")
      )
| BinOp(_i, op, lhs, rhs) ->
    let (lhs, h) = interp lhs env sdef h in
      let (rhs, h) = interp rhs env sdef h in
        (match (op, lhs, rhs) with
        | (Add, Num(lhs), Num(rhs)) -> (Num(lhs + rhs), h)
        | (Sub, Num(lhs), Num(rhs)) -> (Num(lhs - rhs), h)
        | (Mul, Num(lhs), Num(rhs)) -> (Num(lhs * rhs), h)
        | (Div, Num(lhs), Num(rhs)) -> (Num(lhs / rhs), h)
        | (Eq, Num(lhs), Num(rhs)) -> (Bool(lhs == rhs), h)
        | (Ne, Num(lhs), Num(rhs)) -> (Bool(lhs != rhs), h)
        | (Eq, Bool(lhs), Bool(rhs)) -> (Bool(lhs == rhs), h)
        | (Ne, Bool(lhs), Bool(rhs)) -> (Bool(lhs != rhs), h)
        | (Eq, Loc(lhs, lid), Loc(rhs, rid)) -> (Bool(lhs == rhs && String.equal lid rid), h)
        | (Ne, Loc(lhs, lid), Loc(rhs, rid)) -> (Bool(lhs != rhs || not (String.equal lid rid)), h)
        (* should unit get a comparison definition? *)
        | (Le, Num(lhs), Num(rhs)) -> (Bool(lhs <= rhs), h)
        | (Lt, Num(lhs), Num(rhs)) -> (Bool(lhs < rhs), h)
        | (Ge, Num(lhs), Num(rhs)) -> (Bool(lhs >= rhs), h)
        | (Gt, Num(lhs), Num(rhs)) -> (Bool(lhs > rhs), h)
        | (And, Bool(lhs), Bool(rhs)) -> (Bool(lhs && rhs), h)
        | (Or, Bool(lhs), Bool(rhs)) -> (Bool(lhs || rhs), h)
        | _ -> raise (InterpreterException "Unsupported binary operation!")
        )
| Seq(_i, expr0, expr1) -> let (_, h) = interp expr0 env sdef h in interp expr1 env sdef h
| Malloc(_i, id, exprs) ->
    (*TODO check that the expression list matches the expected types *)
    let _expected_types = sdef |> StringMap.find id in
    let (values_list, h) =
      List.fold_right
        (fun expr (values_list, h) ->
          let (v, h) = interp expr env sdef h in
            (v :: values_list, h))
        exprs
        ([], h)
      in
        let (loc, h) = malloc values_list h in
          (Loc(loc, id), h)
| Mfree(_i, loc) ->
    let (loc, h) = interp loc env sdef h in
      (match loc with
      | Loc(l, _id) -> (Unit, mfree l h)
      | _ -> raise (InterpreterException "Mfree requires a base location!")
      )
| Mget(_i, loc, field) ->
    let (loc, h) = interp loc env sdef h in
      (match loc with
      | Loc(l, id) ->
            (mget l field id h sdef, h)
      | _ -> raise (InterpreterException "Mget requires a location!")
      )
| Mset(_i, loc, field, expr) ->
    let (loc, h) = interp loc env sdef h in
      (match loc with
      | Loc(l, id) ->
        let (expr, h) = interp expr env sdef h in
          (Unit, mset l field id expr h sdef)
      | _ -> raise (InterpreterException "Mset requires a location!")
      )
| While(_i, condition, body) ->
  let (condition, h) = interp condition env sdef h in
    (match condition with
    | Bool(condition) ->
      if condition
        then let (_, h) = interp body env sdef h in
          interp expr env sdef h
        else (Unit, h)
    | _ -> raise (InterpreterException "While requires a bool!")
    )
| For(i, id, start, end_, body) ->
  let (start, h) = interp start env sdef h in
    let (end_, h) = interp end_ env sdef h in
      let env = env |> StringMap.add id start in
        (match (start, end_) with
        | (Num(start), Num(end_)) ->
          let (_, h) = interp body env sdef h in
            if start == end_ then
              (Unit, h)
            else if start < end_ then
              interp (For(i, id, Num(-1, start+1), Num(-1, end_), body)) env sdef h
            else
              interp (For(i, id, Num(-1, start-1), Num(-1, end_), body)) env sdef h
        | _ -> raise (InterpreterException "For requires numbers for iterating!")
        )
| Assert(_i, _assertion, command) -> interp command env sdef h

let (===) (lhs: values) (rhs: values) : bool = match (lhs, rhs) with
| (Num(lhs), Num(rhs)) -> lhs == rhs
| (Loc(lhs, lid), Loc(rhs, rid)) -> lhs == rhs && String.equal lid rid
| (Bool(lhs), Bool(rhs)) -> lhs == rhs
| (Unit, Unit) -> true
| _ -> false

let (!==) (lhs: values) (rhs: values) : bool = not (lhs === rhs)
