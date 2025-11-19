open Ast
open Analysis
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

type formula =
| Num of int
| Bool of bool
| Id of string
| Mget of int * string * string
| BinOp of binop * formula * formula

(** Interpretation values used in the symbolic execution *)
type value =
| Num of int
| Bool of bool
| Loc of int * string
| InvalidatedNum
| InvalidatedBool
| InvalidatedLoc of string
| Formula of formula
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
        | (_, Formula(_)) -> v :: xs (* always allow a formula *)
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

let value_to_formula (value: value) (_env: environment) (_sdef: struct_definitions) (_h: heap) : formula = match value with
| Num(n) -> Num(n)
| Bool(b) -> Bool(b)
| Formula(form) -> form
| _ -> raise (SymbolicExecutionException "value_to_formula does not support all values")

let rec formula_to_Z3 (formula: formula) (env: environment) (sdef: struct_definitions) (h: heap) : Z3.Expr.expr = match formula with
| Num(n) -> Z3.Arithmetic.Integer.mk_numeral_i ctx n
| Bool(b) -> if b then Z3.Boolean.mk_true ctx else Z3.Boolean.mk_false ctx
| Id(id) ->
    let sym = string_symbol id in
      Z3.Arithmetic.Integer.mk_const ctx sym (*TODO also support bool type*)
| Mget(loc, field, struct_name) ->
    let struct_info = sdef |> StringMap.find struct_name in
    (match List.find_index (fun (name, _) -> String.equal name field) struct_info with
    | Some(offset) ->
        let sym = int_symbol (loc+offset) in
          Z3.Arithmetic.Integer.mk_const ctx sym (*TODO also support bool type*)
    | None -> raise (SymbolicExecutionException "formula_to_Z3 could not find the field")
    )
| BinOp(op, lhs, rhs) ->
  let lhs, rhs = (formula_to_Z3 lhs env sdef h), (formula_to_Z3 rhs env sdef h) in
  (match op with
  | Add -> Z3.Arithmetic.mk_add ctx [lhs; rhs]
  | Sub -> Z3.Arithmetic.mk_sub ctx [lhs; rhs]
  | Mul -> Z3.Arithmetic.mk_mul ctx [lhs; rhs]
  | Div -> Z3.Arithmetic.mk_div ctx lhs rhs
  | Le -> Z3.Arithmetic.mk_le ctx lhs rhs
  | Lt -> Z3.Arithmetic.mk_lt ctx lhs rhs
  | Ge -> Z3.Arithmetic.mk_ge ctx lhs rhs
  | Gt -> Z3.Arithmetic.mk_gt ctx lhs rhs
  | Eq -> Z3.Boolean.mk_eq ctx lhs rhs
  | Ne -> Z3.Boolean.mk_not ctx (Z3.Boolean.mk_eq ctx lhs rhs)
  | And | Sep -> Z3.Boolean.mk_and ctx [lhs; rhs]
  | Or -> Z3.Boolean.mk_or ctx [lhs; rhs]
  | _ -> raise (SymbolicExecutionException "formula_to_Z3 does not support all binops")
  )

let rec derive (expr: expression) (env: environment) (sdef: struct_definitions) (h: heap) : Z3.Expr.expr = match expr with
| Num(_i, n) ->
    Z3.Arithmetic.Integer.mk_numeral_i ctx n
| Bool(_i, b) ->
    if b then Z3.Boolean.mk_true ctx else Z3.Boolean.mk_false ctx
| Null(_i) ->
    Z3.Arithmetic.Integer.mk_numeral_i ctx 0
| BinOp(_i, op, lhs, rhs) ->
    let lhs_expr = derive lhs env sdef h in
    let rhs_expr = derive rhs env sdef h in
      (match op with
      | Add -> Z3.Arithmetic.mk_add ctx [lhs_expr; rhs_expr]
      | Sub -> Z3.Arithmetic.mk_sub ctx [lhs_expr; rhs_expr]
      | Mul -> Z3.Arithmetic.mk_mul ctx [lhs_expr; rhs_expr]
      | Div -> Z3.Arithmetic.mk_div ctx lhs_expr rhs_expr
      | Eq -> Z3.Boolean.mk_eq ctx lhs_expr rhs_expr
      | Ne -> Z3.Boolean.mk_not ctx (Z3.Boolean.mk_eq ctx lhs_expr rhs_expr)
      | Le -> Z3.Arithmetic.mk_le ctx lhs_expr rhs_expr
      | Lt -> Z3.Arithmetic.mk_lt ctx lhs_expr rhs_expr
      | Ge -> Z3.Arithmetic.mk_ge ctx lhs_expr rhs_expr
      | Gt -> Z3.Arithmetic.mk_gt ctx lhs_expr rhs_expr
      | And -> Z3.Boolean.mk_and ctx [lhs_expr; rhs_expr]
      | Or -> Z3.Boolean.mk_or ctx [lhs_expr; rhs_expr]
      | Sep -> Z3.Boolean.mk_and ctx [lhs_expr; rhs_expr] (* separation check is not done by derive *)
      | _ -> raise (SymbolicExecutionException "TODO: derive does not support all BinOps yet!")
      )
| Id(i, id) -> (*let v = env |> StringMap.find id in*)
    let sym = string_symbol id in
      (match !type_map |> IntMap.find i with
      | Null ->
          Z3.Arithmetic.Integer.mk_const ctx sym
      | Loc(_name) ->
          Z3.Arithmetic.Integer.mk_const ctx sym
      | Num ->
          Z3.Arithmetic.Integer.mk_const ctx sym
      | Bool ->
          Z3.Boolean.mk_const ctx sym
      | _ -> raise (SymbolicExecutionException "Derive Id does not support all types yet")
      )
| Mget(i, loc, _field) ->
    let l = ref Unit in
    let k = (fun (res: value) (_h: heap) -> l := res) in
      symexec loc env sdef Unit h k;
      (match !l with
      | Loc(addr, _) ->
          let sym = int_symbol addr in
            (match !type_map |> IntMap.find i with
            | Num ->
                Z3.Arithmetic.Integer.mk_const ctx sym
            | Bool ->
                Z3.Boolean.mk_const ctx sym
            | _ -> raise (SymbolicExecutionException "Derive Mget does not support all types yet")
            )
      | _ -> raise (SymbolicExecutionException "Derive Mget needs a location")
      )
| _ -> raise (SymbolicExecutionException ("TODO: Derive does not support this AST node (yet?): " ^ string_of_expression expr))

and symexec (expr: expression) (env: environment) (sdef: struct_definitions) (res: value) (h: heap) (k: value -> heap -> unit): unit = match expr with
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
        symexec body env sdef Unit h k)
      in
        symexec bound env sdef Unit h k
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
            | (op, Formula(lhs), Formula(rhs)) -> Formula(BinOp(op, lhs, rhs))
            | (op, Formula(form), rhs) -> Formula(BinOp(op, form, value_to_formula rhs env sdef h))
            | (op, lhs, Formula(form)) -> Formula(BinOp(op, value_to_formula lhs env sdef h, form))
            | _ -> raise (SymbolicExecutionException "Unsupported binary operation!")
            (*TODO handle formulae*)
            )
          in
            k res_binop h
          )
        in
          symexec rhs env sdef res h k
      )
    in
      symexec lhs env sdef res h k
| Assert(_i, assertion) ->
    let _ = check_separation assertion env sdef h in
    let assert_env = if res == Unit then env else env |> StringMap.add "result" res in
    let premise = get_premise assert_env sdef h in
    let assertion = derive assertion env sdef h in
    let formula = Z3.Boolean.mk_and ctx [premise; assertion] in
      solve [formula];
      k res h
| Seq(_i, expr0, expr1) ->
    let k = (fun (res: value) (h: heap) ->
        symexec expr1 env sdef res h k
      )
    in
      symexec expr0 env sdef res h k
| Cond(_i, cond, then_body, else_body) ->
    (*let k = (fun (_res: value) (h: heap) ->*)
    let cond = derive cond env sdef h in
    let premise = get_premise env sdef h in

    let pos =
      (try solve [premise; cond]; true with
      | Unsatisfiable -> false
      | Unknown ->
          (*TODO abstract with cond*)
          raise (SymbolicExecutionException "TODO: Cond unknown is not supported yet")
      )
    in
    let neg =
      (try solve [premise; Z3.Boolean.mk_not ctx cond]; true with
      | Unsatisfiable -> false
      | Unknown ->
          (*TODO abstract with cond*)
          raise (SymbolicExecutionException "TODO: Cond unknown is not supported yet")
      )
    in
      (match pos, neg with
      | true, false -> symexec then_body env sdef Unit h k
      | false, true -> symexec else_body env sdef Unit h k
      | true, true ->
          (*TODO abstract with cond*)
          raise (SymbolicExecutionException "TODO: Cond is satisfiable for both cases")
      | false, false ->
          (*TODO abstract with cond*)
          raise (SymbolicExecutionException "TODO: Cond is satisfiable for no case")
      )

| Struct(_i, id, fields, body) ->
    if List.length fields == 0 then
      raise (SymbolicExecutionException "Field list cannot be empty for struct construction!")
    else if (StringMap.exists (fun k _ -> String.equal k id) env) || (StringMap.exists (fun k _ -> String.equal k id) sdef) then
      raise (SymbolicExecutionException "Struct name is already used!")
    else
      let sdef = sdef |> StringMap.add id fields in
        symexec body env sdef Unit h k
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
            symexec expr env sdef Unit h concat;
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
      symexec loc env sdef Unit h k
| Mget(_i, loc, field) ->
    let k = (fun (res: value) (h: heap) ->
      (match res with
      | Loc(l, id) ->
          k (mget l field id h sdef) h
      | _ -> raise (SymbolicExecutionException "Mget requires a location!")
      )
    )
    in
      symexec loc env sdef Unit h k
| Mset(_i, loc, field, expr) ->
    let k = (fun (res: value) (h: heap) ->
      match res with
      | Loc(l, id) ->
          let k = (fun (res: value) (h: heap) ->
            k Unit (mset l field id res h sdef)
            )
          in
            symexec expr env sdef Unit h k
      | _ -> raise (SymbolicExecutionException "Mset requires a location!")
      )
    in
      symexec loc env sdef Unit h k
| Invariant(_, inv, While(_, cond, body)) ->
    let rec find_derefs (expr: expression) : (string * StringSet.t) IntMap.t =
      (match expr with
      | BinOp(_, _op, lhs, rhs) -> IntMap.union (fun _l (t, lhs) (_t, rhs) -> Some(t, StringSet.union lhs rhs)) (find_derefs lhs) (find_derefs rhs)
      | Mget(_, loc, field) ->
          let r = ref Unit in
          let k =
            (fun res _h ->
              r := res
            )
          in
            symexec loc env sdef Unit h k;
            (match !r with
            | Loc(addr, struct_name) ->
                IntMap.empty |> IntMap.add addr (struct_name, StringSet.empty |> StringSet.add field)
            | _ -> raise (SymbolicExecutionException "find_derefs requires location!")
            )
      | _ -> IntMap.empty
      )
    in

    let rec contains_deref (code: expression) (addr: int) (field: string) : bool =
      (match code with
      | Mget(_, loc, field_) ->
          if not (String.equal field field_) then
            false
          else
            let r = ref Unit in
            let k =
              (fun res _h ->
                r := res
              )
            in
              symexec loc env sdef Unit h k;
              (match !r with
              | Loc(addr_, _struct_name) ->
                  addr == addr_
              | _ -> raise (SymbolicExecutionException "find_derefs requires location!")
              )
      | BinOp(_, _op, lhs, rhs) -> (contains_deref lhs addr field) || (contains_deref rhs addr field)
      | _ -> false
      )
    in

    let rec formulae_of_deref (code: expression) (addr: int) (struct_name: string) (field: string) : formula list =
      (match code with
      | BinOp(_, And, lhs, rhs) -> (*TODO does Or has to be specially handled as well? *)
        (match
          contains_deref lhs addr field,
          contains_deref rhs addr field
        with
        | true, true -> List.append (formulae_of_deref lhs addr struct_name field) (formulae_of_deref rhs addr struct_name field)
        | true, false -> formulae_of_deref lhs addr struct_name field
        | false, true -> formulae_of_deref rhs addr struct_name field
        | false, false -> []
        )
      | x -> [formula_of x env sdef h]
      )
    in

    let assumption: expression = (BinOp(-1, And, inv, cond)) in
    let derefs_map = find_derefs assumption in
    let h =
      IntMap.fold
        (fun addr (struct_name, fields) h ->
          StringSet.fold
            (fun field h ->
              let formulae = formulae_of_deref assumption addr struct_name field in
              let form =
                match formulae with
                | x :: xs -> List.fold_right (fun a b -> BinOp(And, a, b)) xs x
                | _ -> raise (SymbolicExecutionException "symexec: formula list needs at least one element!")
              in
              let h = mset addr field struct_name (Formula(form)) h sdef in
                h
            )
            fields
            h
        )
        derefs_map
        h
    in

    (*let assumption = BinOp(-1, And, inv, cond) in
    let assumption_ids = bound_variables assumption in
    (*let assumptions =
      StringSet.fold
        (fun id m -> m |> StringMap.add id (formulae_of_id id assumption))
        assumption_ids
        StringMap.empty
    in*)
    (*TODO maybe only abstract values on the heap as formula*)
    let env, assumption_locs =
      StringSet.fold
        (fun id (m, assumption_locs) ->
          match env |> StringMap.find id with
          | Loc(l, field) -> m, (l, field, Formula(formulae_of_id id assumption)) :: assumption_locs
          | _ -> m |> StringMap.add id (Formula(formulae_of_id id assumption)), assumption_locs)
        assumption_ids
        (env, [])
    in

    let h =
      List.fold_right
        (fun (loc, _field, form) h ->
          let offset = 0 in
          h |> IntMap.add loc (
            List.mapi
              (fun i v -> if i == offset then form else v)
              (IntMap.find loc h)
          )
        )
        assumption_locs
        h
    in*)

    let _ = check_separation inv env sdef h in
    (* k for checking the invariant*)
    let k_check_inv = (fun (res: value) (h: heap) ->
      let inv_env = if res == Unit then env else env |> StringMap.add "result" res in
      let premise = get_premise inv_env sdef h in
      let inv = derive inv env sdef h in
        solve [premise; inv]
      )
    in
      (* k for cond=false and invariant*)
      let k_cond_false = (fun (res: value) (h: heap) ->
        let cond_form = derive cond env sdef h in
        let inv_env = if res == Unit then env else env |> StringMap.add "result" res in
        let premise = get_premise inv_env sdef h in
        let inv = derive inv env sdef h in
        let formula = Z3.Boolean.mk_implies
          ctx
          (Z3.Boolean.mk_and ctx [premise; inv])
          (Z3.Boolean.mk_not ctx cond_form)
        in
        if try solve [formula]; true with
        | _ -> false
        then
          k res h
        else
          raise (SymbolicExecutionException "symexec cannot prove loop will terminate at some point TODO")
          (*
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
            *)
        )
      in
        (* k for cond=true and invariant*)
        let k_cond_true = (fun (res: value) (h: heap) ->
        let cond = derive cond env sdef h in
        let inv_env = if res == Unit then env else env |> StringMap.add "result" res in
        let premise = get_premise inv_env sdef h in
        let inv = derive inv env sdef h in
        let formula = Z3.Boolean.mk_implies
          ctx
          (Z3.Boolean.mk_and ctx [premise; inv])
          cond
        in
        if try solve [formula]; true with
        | Unknown -> raise (SymbolicExecutionException "symexec cannot prove loop will terminate at some point")
        | Unsatisfiable -> false
        then
          let k = (fun (res: value) (h: heap) ->
              k_check_inv res h;
              symexec expr env sdef Unit h k
            )
          in
            symexec body env sdef Unit h k
        else
          k_cond_false res h
        )
        in
          k_check_inv res h;
          k_cond_false res h;
          k_cond_true res h
| _ -> raise (SymbolicExecutionException ("symexec does not support this AST node (yet?): " ^ string_of_expression expr))

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
      symexec loc env sdef Unit h k;
      (match !r with
      | InvalidatedLoc(_) -> raise (SymbolicExecutionException "Separation violated due to invalidated location!")
      | Loc(l, _) -> IntSet.empty |> IntSet.add l
      | Formula(_) -> raise (SymbolicExecutionException "Separation violated due to abstracted location!")
      | _ -> raise (SymbolicExecutionException "check_separation expected location!")
      )
| _ -> raise (SymbolicExecutionException "check_separation does not support this AST node!")

and get_premise (env: environment) (sdef: struct_definitions) (h: heap) : Z3.Expr.expr =
  let env_list = StringMap.fold
    (fun id v l ->
      let v, sort = match v with
      | Bool(b) -> (if b then Z3.Boolean.mk_true ctx else Z3.Boolean.mk_false ctx), bool_sort
      | Num(n) -> Z3.Arithmetic.Integer.mk_numeral_i ctx n, int_sort
      | Loc(l, _name) -> Z3.Arithmetic.Integer.mk_numeral_i ctx l, int_sort
      | Formula(_form) -> raise (SymbolicExecutionException "get_premise TODO") (*formula_to_Z3 form env sdef h, bool_sort*)
      | _ -> raise (SymbolicExecutionException "get_premise does not support all value types yet TODO")
      in
        let sym = string_symbol id in
        let c = Z3.Expr.mk_const ctx sym sort in
        let eq = Z3.Boolean.mk_eq ctx c v in
          eq :: l
    )
    env
    []
  in
  let h_list = IntMap.fold
    (fun loc vs l ->
      let vs = List.mapi (fun i v -> i, v) vs in
      List.fold_right
        (fun (i, v) l ->
          let v, sort = match v with
          | Bool(b) -> (if b then Z3.Boolean.mk_true ctx else Z3.Boolean.mk_false ctx), bool_sort
          | Num(n) -> Z3.Arithmetic.Integer.mk_numeral_i ctx n, int_sort
          | Formula(form) -> formula_to_Z3 form env sdef h, bool_sort
          | _ -> raise (SymbolicExecutionException "get_premise does not support all value types yet TODO")
          in
            let sym = int_symbol (loc+i) in
            let c = Z3.Expr.mk_const ctx sym sort in
            let eq = Z3.Boolean.mk_eq ctx c v in
              eq :: l
        )
        vs
        l
    )
    h
    []
  in
    Z3.Boolean.mk_and ctx (List.append env_list h_list)
  (*TODO bring heap locations to the premise*)

and formula_of (expr: expression) (env: environment) (sdef: struct_definitions) (h: heap) : formula  = match expr with
| Num(_, n) -> Num(n)
| Bool(_, b) -> Bool(b)
| BinOp(_, op, lhs, rhs) -> BinOp(op, formula_of lhs env sdef h, formula_of rhs env sdef h)
| Mget(_, loc, field) ->
    let r = ref Unit in
    let k = (fun res _h -> r := res) in
      symexec loc env sdef Unit h k;
      (match !r with
      | Loc(addr, struct_name) -> Mget(addr, field, struct_name)
      | _ -> raise (SymbolicExecutionException "formula_of needs a location for Mget!")
      )
| Id(_, id) -> Id(id)
| _ -> raise (SymbolicExecutionException "formula_of does not support all AST nodes")

let verify (expr: expression) =
  let env = StringMap.empty in
  let sdef = StringMap.empty in
  let res = Unit in
  let h = IntMap.empty in
  let k = (fun (_res: value) (_h: heap) -> ()) in
    symexec expr env sdef res h k
