open Ast
(*open Analysis*)
open Common

let ctx = Z3.mk_context [("proof", "true")]

let int_symbol index = Z3.Symbol.mk_int ctx index
let string_symbol name = Z3.Symbol.mk_string ctx name

let int_sort = Z3.Arithmetic.Integer.mk_sort ctx
let bool_sort = Z3.Boolean.mk_sort ctx

let solver = Z3.Solver.mk_simple_solver ctx

exception SymbolicExecutionException of string

exception Unsatisfiable
exception Unknown

let solve formula = match Z3.Solver.check solver formula with
| SATISFIABLE -> ()
| UNSATISFIABLE -> raise Unsatisfiable
| UNKNOWN -> raise Unknown (* should unknown raise an exception? *)


(** Interpretation values used in the symbolic execution *)
type value =
| Num of int
| Bool of bool
| Loc of int * string
| InvalidatedNum
| InvalidatedBool
| InvalidatedLoc of string
| Unit

(** Map that holds the environment store *)
type environment = (value StringMap.t)

(** Map that holds the struct definitions *)
type struct_definitions = ((string * struct_type) list StringMap.t)

(** Map that holds the heap store *)
type heap = ((value list) IntMap.t)

(** Memory allocation on the heap *)
let malloc (init_values: value list) (h: heap) : int * heap =
  if List.length init_values == 0 then
    raise (SymbolicExecutionException "malloc cannot allocate nothing")
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
let mget (loc: int) (field: string) (type_id: string) (h: heap) (sdef: struct_definitions) : value =
  if IntMap.is_empty h then
    raise (SymbolicExecutionException "mget cannot get anything from an empty heap!")
  else
    let td = sdef |> StringMap.find type_id in
    (match List.find_index (fun (tid, _) -> String.equal tid field) td with
    | Some off ->
    let values_list = IntMap.find loc h in
      if off < 0 || off >= List.length values_list then
        raise (SymbolicExecutionException ("mget got location out of range: " ^ string_of_int loc))
      else
        List.nth values_list off
    | None -> raise (SymbolicExecutionException ("mget: field could not be found: " ^ field))
    )

(** Replace nth element if the type matches *)
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
        | _ -> raise (SymbolicExecutionException "mset cannot change data type of field!")
        )
      else
        x :: replace_nth xs v (n-1)

(** Memory mutation on the heap *)
let mset (loc: int) (field: string) (type_id: string) (v: value) (h: heap) (sdef: struct_definitions) : heap =
  if IntMap.is_empty h then
    raise (SymbolicExecutionException "mset cannot set anything on an empty heap!")
  else
    let values_list = IntMap.find loc h in
    let td = sdef |> StringMap.find type_id in
    (match List.find_index (fun (tid, _) -> String.equal tid field) td with
    | Some off ->
      if off < 0 || off >= List.length values_list then
        raise (SymbolicExecutionException ("mget got offset out of range: " ^ string_of_int loc))
      else
        let values_list = replace_nth values_list v off in
          h |> IntMap.add loc values_list
    | None -> raise (SymbolicExecutionException ("mset: field could not be found: " ^ field))
    )

let invalidate (h: heap): heap =
  IntMap.map
    (fun vl ->
      List.map
        (fun v ->
          match v with
          | Num(_) -> InvalidatedNum
          | Bool(_) -> InvalidatedBool
          | Loc(_, id) -> InvalidatedLoc(id)
          | v -> v
        )
        vl
    )
    h

let rec derive (expr: expression) (env: environment) (sdef: struct_definitions) (h: heap) : Z3.Expr.expr * Z3.Symbol.symbol * Z3.Sort.sort = match expr with
| Num(i, n) ->
    let sym = int_symbol i in
    let c = Z3.Arithmetic.Integer.mk_const ctx sym in
    let v = Z3.Arithmetic.Integer.mk_numeral_i ctx n in
      (Z3.Boolean.mk_eq ctx c v, sym, int_sort)
| Bool(i, b) ->
    let sym = int_symbol i in
    let c = Z3.Boolean.mk_const ctx sym in
    let v = if b then Z3.Boolean.mk_true ctx else Z3.Boolean.mk_false ctx in
      (Z3.Boolean.mk_eq ctx c v, sym, bool_sort)
| BinOp(i, op, lhs, rhs) ->
    let (lhs_expr, lhs_sym, lhs_sort) = derive lhs env sdef h in
    let (rhs_expr, rhs_sym, rhs_sort) = derive rhs env sdef h in
    let lhs_c = Z3.Expr.mk_const ctx lhs_sym lhs_sort in
    let rhs_c = Z3.Expr.mk_const ctx rhs_sym rhs_sort in
    let (v, is_int) =
      (match op with
      | Add -> (Z3.Arithmetic.mk_add ctx [lhs_c; rhs_c], true)
      | Sub -> (Z3.Arithmetic.mk_sub ctx [lhs_c; rhs_c], true)
      | Mul -> (Z3.Arithmetic.mk_mul ctx [lhs_c; rhs_c], true)
      | Div -> (Z3.Arithmetic.mk_div ctx lhs_c rhs_c, true)
      | Eq -> (Z3.Boolean.mk_eq ctx lhs_c rhs_c, false)
      | Ne -> (Z3.Boolean.mk_not ctx (Z3.Boolean.mk_eq ctx lhs_c rhs_c), false)
      | Le -> (Z3.Arithmetic.mk_le ctx lhs_c rhs_c, false)
      | Lt -> (Z3.Arithmetic.mk_lt ctx lhs_c rhs_c, false)
      | Ge -> (Z3.Arithmetic.mk_ge ctx lhs_c rhs_c, false)
      | Gt -> (Z3.Arithmetic.mk_gt ctx lhs_c rhs_c, false)
      | And -> (Z3.Boolean.mk_and ctx [lhs_c; rhs_c], false)
      | Or -> (Z3.Boolean.mk_or ctx [lhs_c; rhs_c], false)
      | Sep -> (Z3.Boolean.mk_and ctx [lhs_c; rhs_c], false) (* separation check is not done by derive *)
      | _ -> raise (SymbolicExecutionException "TODO: derive does not support all BinOps yet!")
      ) in
    let sym = int_symbol i in
    if is_int then
      let c = Z3.Arithmetic.Integer.mk_const ctx sym in
      let eq = Z3.Boolean.mk_eq ctx c v in
        (Z3.Boolean.mk_and ctx [lhs_expr; rhs_expr; eq], sym, int_sort)
    else
      let c = Z3.Boolean.mk_const ctx sym in
      let eq = Z3.Boolean.mk_eq ctx c v in
        (Z3.Boolean.mk_and ctx [lhs_expr; rhs_expr; eq], sym, bool_sort)
| Id(i, id) -> let v = env |> StringMap.find id in
      (match v with
      | Num(n) ->
          let sym = int_symbol i in
          let c = Z3.Arithmetic.Integer.mk_const ctx sym in
          let v = Z3.Arithmetic.Integer.mk_numeral_i ctx n in
            (Z3.Boolean.mk_eq ctx c v, sym, int_sort)
      | Bool(b) ->
          let sym = int_symbol i in
          let c = Z3.Boolean.mk_const ctx sym in
          let v = if b then Z3.Boolean.mk_true ctx else Z3.Boolean.mk_false ctx in
            (Z3.Boolean.mk_eq ctx c v, sym, bool_sort)
      | _ -> raise (SymbolicExecutionException "TODO: Derive Id does not support all types yet")
      )
| Mget(i, loc, field) ->
    let l = ref Unit in
    let k = (fun (res: value) (_h: heap) ->
        l := res
      )
    in
      symexec loc env sdef Unit h k [];
      (match !l with
      | Loc(v, id) -> (match (mget v field id h sdef) with
        | Num(n) ->
            let sym = int_symbol i in
            let c = Z3.Arithmetic.Integer.mk_const ctx sym in
            let v = Z3.Arithmetic.Integer.mk_numeral_i ctx n in
              (Z3.Boolean.mk_eq ctx c v, sym, int_sort)
        | Bool(b) ->
            let sym = int_symbol i in
            let c = Z3.Boolean.mk_const ctx sym in
            let v = if b then Z3.Boolean.mk_true ctx else Z3.Boolean.mk_false ctx in
              (Z3.Boolean.mk_eq ctx c v, sym, bool_sort)
        | InvalidatedNum ->
            let sym = int_symbol i in
              (Z3.Boolean.mk_true ctx, sym, int_sort)
        | InvalidatedBool ->
            let sym = int_symbol i in
              (Z3.Boolean.mk_true ctx, sym, bool_sort)
        | _ -> raise (SymbolicExecutionException "TODO: Derive Mget does not support all types yet")
        )
      | _ -> raise (SymbolicExecutionException "Derive: Mget needs a location!"))
| _ -> raise (SymbolicExecutionException "TODO: Derive does not support this AST node (yet?)")

and symexec (expr: expression) (env: environment) (sdef: struct_definitions) (res: value) (h: heap) (k: value -> heap -> unit) (assumption: Z3.Expr.expr list): unit = match expr with
| Num(_i, n) -> k (Num(n)) h
| Bool(_i, b) -> k (Bool(b)) h
| Null(_i) -> k (Loc(0, "")) h
| Unit(_i) -> k Unit h
| Let(_i, id, bound, body) ->
    (* TODO do we need to check that no struct name is used, as the interpreter does? Maybe we can built a preprocessing step for that *)
    if (StringMap.exists (fun k _ -> String.equal k id) sdef) then
      raise (SymbolicExecutionException "Let ID already exists as struct name!")
    else
      let k = (fun (res: value) (h: heap) ->
        let env = env |> StringMap.add id res in
        symexec body env sdef Unit h k assumption)
      in
        symexec bound env sdef Unit h k assumption
| Id(_i, id) -> k (env |> StringMap.find id) h
| BinOp(_i, op, lhs, rhs) ->
    let k = (fun (res_lhs: value) (h: heap) ->
        let k = (fun (res_rhs: value) (h: heap) ->
          let res_binop = (match (op, res_lhs, res_rhs) with
            | (Add, Num(lhs), Num(rhs)) -> Num(lhs + rhs)
            | (Sub, Num(lhs), Num(rhs)) -> Num(lhs - rhs)
            | (Mul, Num(lhs), Num(rhs)) -> Num(lhs * rhs)
            | (Div, Num(lhs), Num(rhs)) -> Num(lhs / rhs)
            | (Eq, Num(lhs), Num(rhs)) -> Bool(lhs == rhs)
            | (Ne, Num(lhs), Num(rhs)) -> Bool(lhs != rhs)
            | (Eq, Bool(lhs), Bool(rhs)) -> Bool(lhs == rhs)
            | (Ne, Bool(lhs), Bool(rhs)) -> Bool(lhs != rhs)
            | (Eq, Loc(lhs, lid), Loc(rhs, rid)) -> Bool(lhs == rhs && String.equal lid rid)
            | (Ne, Loc(lhs, lid), Loc(rhs, rid)) -> Bool(lhs != rhs || not (String.equal lid rid))
            (* should unit get a comparison definition? *)
            | (Le, Num(lhs), Num(rhs)) -> Bool(lhs <= rhs)
            | (Lt, Num(lhs), Num(rhs)) -> Bool(lhs < rhs)
            | (Ge, Num(lhs), Num(rhs)) -> Bool(lhs >= rhs)
            | (Gt, Num(lhs), Num(rhs)) -> Bool(lhs > rhs)
            | (And, Bool(lhs), Bool(rhs)) -> Bool(lhs && rhs)
            | (Or, Bool(lhs), Bool(rhs)) -> Bool(lhs || rhs)
            | _ -> raise (SymbolicExecutionException "Unsupported binary operation!")
            )
          in
            k res_binop h
          )
        in
          symexec rhs env sdef res h k assumption
      )
    in
      symexec lhs env sdef res h k assumption
| Assert(_i, assertion) ->
    let _ = check_separation assertion env sdef h in
    let assert_env = env |> StringMap.add "result" res in
    let (assertion, sym, sort) = derive assertion assert_env sdef h in
    let c = Z3.Expr.mk_const ctx sym sort in
    let eq = Z3.Boolean.mk_eq ctx assertion c in
    let formula = Z3.Boolean.mk_and ctx [assertion; eq; c] in
      solve (formula :: assumption);
      k res h
| Seq(_i, expr0, expr1) ->
    let k = (fun (res: value) (h: heap) ->
        symexec expr1 env sdef res h k assumption
      )
    in
      symexec expr0 env sdef res h k assumption
| Cond(_i, cond, then_body, else_body) ->
    let k = (fun (_res: value) (h: heap) ->
      let (cond, sym, sort) = derive cond env sdef h in
          let c = Z3.Expr.mk_const ctx sym sort in
          let eq = Z3.Boolean.mk_eq ctx cond c in
          let formula = Z3.Boolean.mk_and ctx [cond; eq; c] in
            if (try solve (formula :: assumption); true with
                | Unsatisfiable -> symexec else_body env sdef Unit h k assumption; false
                | Unknown ->
                    let k = (fun (_res: value) (h: heap) ->
                        let formula = Z3.Boolean.mk_not ctx formula in
                          symexec else_body env sdef Unit h k (formula :: assumption)
                      )
                    in
                      symexec then_body env sdef Unit h k (formula :: assumption);
                      false
                )
            then
              symexec then_body env sdef Unit h k assumption
      )
    in
      symexec cond env sdef res h k assumption
| Struct(_i, id, fields, body) ->
    if List.length fields == 0 then
      raise (SymbolicExecutionException "Field list cannot be empty for struct construction!")
    else if (StringMap.exists (fun k _ -> String.equal k id) env) || (StringMap.exists (fun k _ -> String.equal k id) sdef) then
      raise (SymbolicExecutionException "Struct name is already used!")
    else
      let sdef = sdef |> StringMap.add id fields in
        symexec body env sdef Unit h k assumption
| Malloc(_i, id, exprs) ->
    (*TODO check that the expression list matches the expected types *)
    let _expected_types = sdef |> StringMap.find id in
    let (values_list, h) =
      List.fold_right
        (fun expr (values_list, h) ->
          let value = ref Unit in
          let value_h = ref h in
          let concat = (fun (res: value) (h: heap): unit ->
            value := res;
            value_h := h
          )
          in
            symexec expr env sdef Unit h concat assumption;
            (!value :: values_list, !value_h)
        )
        exprs
        ([], h)
      in
        let (loc, h) = malloc values_list h in
          k (Loc(loc, id)) h
| Mfree(_i, loc) ->
    let k = (fun (res: value) (h: heap) ->
      match res with
      | Loc(l, _id) -> k Unit (mfree l h)
      | _ -> raise (SymbolicExecutionException "Mfree requires a base location!")
      )
    in
      symexec loc env sdef Unit h k assumption
| Mget(_i, loc, field) ->
    let k = (fun (res: value) (h: heap) ->
      (match res with
      | Loc(l, id) ->
          k (mget l field id h sdef) h
      | _ -> raise (SymbolicExecutionException "Mget requires a location!")
      )
    )
    in
      symexec loc env sdef Unit h k assumption
| Mset(_i, loc, field, expr) ->
    let k = (fun (res: value) (h: heap) ->
      match res with
      | Loc(l, id) ->
          let k = (fun (res: value) (h: heap) ->
            k Unit (mset l field id res h sdef)
            )
          in
            symexec expr env sdef Unit h k assumption
      | _ -> raise (SymbolicExecutionException "Mset requires a location!")
      )
    in
      symexec loc env sdef Unit h k assumption
| Invariant(_, inv, While(_, cond, body)) ->
    let _ = check_separation inv env sdef h in
    (* k for checking the invariant*)
    let k_check_inv = (fun (res: value) (h: heap) ->
      let inv_env = env |> StringMap.add "result" res in
      let (inv, inv_sym, inv_sort) = derive inv inv_env sdef h in
      let inv_c = Z3.Expr.mk_const ctx inv_sym inv_sort in
        solve [inv; inv_c]
      )
    in
      (* k for cond=false and invariant*)
      let k_cond_false = (fun (res: value) (h: heap) ->
        let (cond_form, cond_sym, cond_sort) = derive cond env sdef h in
        let cond_c = Z3.Expr.mk_const ctx cond_sym cond_sort in
        let inv_env = env |> StringMap.add "result" res in
        let (inv, inv_sym, inv_sort) = derive inv inv_env sdef h in
        let inv_c = Z3.Expr.mk_const ctx inv_sym inv_sort in
        if try solve [cond_form; Z3.Boolean.mk_not ctx cond_c; inv; inv_c]; true with
        | _ -> false
        then
          k res h
        else
          (*invalidate heap and retry*)
          let h = invalidate h in
          let (cond_form, cond_sym, cond_sort) = derive cond env sdef h in
          let cond_c = Z3.Expr.mk_const ctx cond_sym cond_sort in
            if try solve [cond_form; Z3.Boolean.mk_not ctx cond_c; inv; inv_c]; true with
            | Unknown -> true
            | Unsatisfiable -> false
            then
              k res h
            else
              raise (SymbolicExecutionException "symexec cannot prove loop will terminate at some point TODO")
        )
      in
        (* k for cond=true and invariant*)
        let k_cond_true = (fun (res: value) (h: heap) ->
        let (cond, cond_sym, cond_sort) = derive cond env sdef h in
        let cond_c = Z3.Expr.mk_const ctx cond_sym cond_sort in
        let inv_env = env |> StringMap.add "result" res in
        let (inv, inv_sym, inv_sort) = derive inv inv_env sdef h in
        let inv_c = Z3.Expr.mk_const ctx inv_sym inv_sort in
        if try solve [cond; cond_c; inv; inv_c]; true with
        | Unknown -> raise (SymbolicExecutionException "symexec cannot prove loop will terminate at some point")
        | Unsatisfiable -> false
        then
          let k = (fun (res: value) (h: heap) ->
              k_check_inv res h;
              symexec expr env sdef Unit h k assumption
            )
          in
            symexec body env sdef Unit h k assumption
        else
          k res h
        )
        in
          k_check_inv res h;
          k_cond_false res h;
          k_cond_true res h
| _ -> raise (SymbolicExecutionException "symexec does not support this AST node (yet?)")

and check_separation (a: expression) (env: environment) (sdef: struct_definitions) (h: heap): IntSet.t = match a with
| BinOp(_, Sep, lhs, rhs) ->
    let lhs = check_separation lhs env sdef h in
    let rhs = check_separation rhs env sdef h in
      if IntSet.disjoint lhs rhs then
        IntSet.union lhs rhs
      else
        raise (SymbolicExecutionException "Separation violated!")
| BinOp(_, _, lhs, rhs) -> IntSet.union (check_separation lhs env sdef h) (check_separation rhs env sdef h)
| Null(_) -> IntSet.empty
| Num(_, _) -> IntSet.empty
| Bool(_, _) -> IntSet.empty
| Unit(_) -> IntSet.empty
| Id(_, _) -> IntSet.empty
| Mget(_, loc, _) ->
    let r = ref Unit in
    let k = (fun (res: value) (_h: heap) ->
        r := res
      ) in
      symexec loc env sdef Unit h k [];
      (match !r with
      | InvalidatedLoc(_) -> raise (SymbolicExecutionException "Separation violated due to invalidated location!")
      | Loc(l, _) -> IntSet.empty |> IntSet.add l
      | _ -> raise (SymbolicExecutionException "check_separation expected location!")
      )
| _ -> raise (SymbolicExecutionException "check_separation does not support this AST node!")

let verify (expr: expression) =
  let env = StringMap.empty in
  let sdef = StringMap.empty in
  let res = Unit in
  let h = IntMap.empty in
  let k = (fun (_res: value) (_h: heap) -> ()) in
    symexec expr env sdef res h k []
