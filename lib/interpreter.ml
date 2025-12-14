open Ast
open Common

(** [value] is the type for return values of the interpreter *)
type value =
| Loc of int * string (* base location and type id *)
| Num of int
| Bool of bool
| Unit
(* closures *)

(** [environment] maps identifiers to values *)
type environment = (value StringMap.t)

(** [struct_definitions] maps structure names to a list of field names and types *)
type struct_definitions = ((string * struct_type) list StringMap.t)

(** [heap] maps locations to a list holding a structure's fields *)
type heap = ((value list) IntMap.t)

(** Exception used by the interpreter *)
exception InterpreterException of string

(**
[malloc init_values h] allocates a structure on the heap [h] and initilizes the fields with [init_values]
@param init_values initial values for the allocated structure
@param h heap to modify
@returns modified heap [h]
@raise InterpreterException may raise [InterpreterException]
*)
let malloc (init_values: value list) (h: heap) : int * heap =
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
        0x1 (*first available address*)
    in
      (max_available_loc, h |> IntMap.add max_available_loc init_values)

(**
[mfree loc h] deletes a structure from the heap [h] at location [loc]
@param loc location of the structure
@param h heap to modify
@returns modified heap [h]
*)
let mfree (loc: int) (h: heap) : heap = h |> IntMap.remove loc

(**
[mget loc field type_id h sdef] fetches the field [field] of the structure at location [loc] from the heap [h]
@param loc location of the structure
@param field field name
@param type_id structure name
@param h current heap
@param sdef structure definitions
@returns value of field [loc].[field]
@raise InterpreterException may raise [InterpreterException]
*)
let mget (loc: int) (field: string) (type_id: string) (h: heap) (sdef: struct_definitions) : value =
  if IntMap.is_empty h then
    raise (InterpreterException "mget cannot get anything from an empty heap!")
  else
    let td =
      (match sdef |> StringMap.find_opt type_id with
      | Some(td) -> td
      | None -> raise (InterpreterException ("mget cannot find structure definition \"" ^ type_id ^ "\""))
      )
    in
    (match List.find_index (fun (tid, _) -> String.equal tid field) td with
    | Some off ->
      let values_list =
        (match IntMap.find_opt loc h with
        | Some values_list -> values_list
        | None -> raise (InterpreterException ("mget cannot find location on the heap: " ^ string_of_int loc))
        )
      in
        if off < 0 || off >= List.length values_list then
          raise (InterpreterException ("mget got location out of range: " ^ string_of_int loc))
        else
          List.nth values_list off
    | None -> raise (InterpreterException ("mget: field could not be found: " ^ field))
    )

(**
[replace_nth l v n] replaces the [n]th value of the list [l] with value [v]
@param l list to modify
@param v value to insert
@param n index to replace in [l]
@raise InterpreterException raises [InterpreterException] if the type does not match
*)
let rec replace_nth (l: value list) (v: value) (n: int) : value list =
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

(**
[mset loc field type_id v h sdef] sets the field [field] of the structure at location [loc] on the heap [h] to value [v]
@param loc location of the structure
@param field field name
@param type_id structure name
@param v value to set
@param h heap to modify
@param sdef structure definitions
@returns modified heap [h]
@raise InterpreterException may raise [InterpreterException]
*)
let mset (loc: int) (field: string) (type_id: string) (v: value) (h: heap) (sdef: struct_definitions) : heap =
  if IntMap.is_empty h then
    raise (InterpreterException "mset cannot set anything on an empty heap!")
  else
    let td =
      (match sdef |> StringMap.find_opt type_id with
      | Some(td) -> td
      | None -> raise (InterpreterException ("mset cannot find structure definition \"" ^ type_id ^ "\""))
      )
    in
    let values_list =
      (match IntMap.find_opt loc h with
      | Some values_list -> values_list
      | None -> raise (InterpreterException ("mset cannot find location on the heap: " ^ string_of_int loc))
      )
    in
    (match List.find_index (fun (tid, _) -> String.equal tid field) td with
    | Some off ->
      if off < 0 || off >= List.length values_list then
        raise (InterpreterException ("mget got offset out of range: " ^ string_of_int loc))
      else
        let values_list = replace_nth values_list v off in
          h |> IntMap.add loc values_list
    | None -> raise (InterpreterException ("mset: field could not be found: " ^ field))
    )

(**
[interp expr env sdef res h] interpretates the expression [expr] and returens a value and mutated heap
@param expr expression to interpret
@param env environment
@param sdef structure definitions
@param res result of the previous command (this is needed for skipping assertions without losing a result)
@param h heap
@returns value of interpreted [expr] and potentially modified [h]
@raise InterpreterException may raise [InterpreterException]
*)
let rec interp (expr: Ast.expression) (env: environment) (sdef: struct_definitions) (res: value) (h: heap) : value * heap = match expr with
| Num(_i, n) -> (Num(n), h)
| Bool(_i, b) -> (Bool(b), h)
| Unit(_i) -> (Unit, h)
| Struct(_i, id, fields, body) ->
    if List.length fields == 0 then
      raise (InterpreterException "Field list cannot be empty for struct construction!")
    else if (StringMap.exists (fun k _ -> String.equal k id) env) || (StringMap.exists (fun k _ -> String.equal k id) sdef) then
      raise (InterpreterException "Struct name is already used!")
    else
      let sdef = sdef |> StringMap.add id fields in
        interp body env sdef res h
| Let(_i, id, bound, body) ->
    if (StringMap.exists (fun k _ -> String.equal k id) sdef) then
      raise (InterpreterException "Let ID already exists as struct name!")
    else
      let (bound, h) = interp bound env sdef Unit h in
        let env = env |> StringMap.add id bound in
          interp body env sdef Unit h
| Id(_i, id) ->
    (match env |> StringMap.find_opt id with
    | Some v -> v, h
    | None -> raise (InterpreterException ("Id could not be found: " ^ id))
    )
| Cond(_i, cond, then_body, else_body) ->
    let (cond, h) = interp cond env sdef Unit h in
      (match cond with
      | Bool(b) -> if b then interp then_body env sdef Unit h else interp else_body env sdef Unit h
      | _ -> raise (InterpreterException "Cond requires a bool!")
      )
| BinOp(_i, op, lhs, rhs) ->
    let (lhs, h) = interp lhs env sdef res h in
      let (rhs, h) = interp rhs env sdef res h in
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
| Seq(_i, expr0, expr1) -> let (res, h) = interp expr0 env sdef res h in interp expr1 env sdef res h
| Malloc(_i, id, exprs) ->
    let (values_list, h) =
      List.fold_right
        (fun expr (values_list, h) ->
          let (v, h) = interp expr env sdef Unit h in
            (v :: values_list, h))
        exprs
        ([], h)
      in
        let (loc, h) = malloc values_list h in
          (Loc(loc, id), h)
| Mfree(_i, loc) ->
    let (loc, h) = interp loc env sdef Unit h in
      (match loc with
      | Loc(l, _id) -> (Unit, mfree l h)
      | _ -> raise (InterpreterException "Mfree requires a base location!")
      )
| Mget(_i, loc, field) ->
    let (loc, h) = interp loc env sdef Unit h in
      (match loc with
      | Loc(l, id) ->
            (mget l field id h sdef, h)
      | _ -> raise (InterpreterException "Mget requires a location!")
      )
| Mset(_i, loc, field, expr) ->
    let (loc, h) = interp loc env sdef Unit h in
      (match loc with
      | Loc(l, id) ->
        let (expr, h) = interp expr env sdef Unit h in
          (Unit, mset l field id expr h sdef)
      | _ -> raise (InterpreterException "Mset requires a location!")
      )
| While(_i, condition, body) ->
  let (condition, h) = interp condition env sdef Unit h in
    (match condition with
    | Bool(condition) ->
      if condition
        then let (_, h) = interp body env sdef Unit h in
          interp expr env sdef Unit h
        else (Unit, h)
    | _ -> raise (InterpreterException "While requires a bool!")
    )
| For(i, id, start, end_, body) ->
  let (start, h) = interp start env sdef Unit h in
    let (end_, h) = interp end_ env sdef Unit h in
      let env = env |> StringMap.add id start in
        (match (start, end_) with
        | (Num(start), Num(end_)) ->
          let (_, h) = interp body env sdef Unit h in
            if start == end_ then
              (Unit, h)
            else if start < end_ then
              interp (For(i, id, Num(-1, start+1), Num(-1, end_), body)) env sdef Unit h
            else
              interp (For(i, id, Num(-1, start-1), Num(-1, end_), body)) env sdef Unit h
        | _ -> raise (InterpreterException "For requires numbers for iterating!")
        )
| Assert(_i, _assertion) -> res, h
| Invariant(_i, _inv, body) -> interp body env sdef res h

(**
[lhs === rhs] returns whether value [lhs] is equal to [rhs]
@param lhs a value
@param rhs a value
@returns [true] if [lhs] and [rhs] are equal; [false] otherwise
*)
let (===) (lhs: value) (rhs: value) : bool = match (lhs, rhs) with
| (Num(lhs), Num(rhs)) -> lhs == rhs
| (Loc(lhs, lid), Loc(rhs, rid)) -> lhs == rhs && String.equal lid rid
| (Bool(lhs), Bool(rhs)) -> lhs == rhs
| (Unit, Unit) -> true
| _ -> false

(**
[lhs !== rhs] returns whether value [lhs] is not equal to [rhs]
@param lhs a value
@param rhs a value
@returns [true] if [lhs] and [rhs] are not equal; [false] otherwise
*)
let (!==) (lhs: value) (rhs: value) : bool = not (lhs === rhs)
