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
| Formula of formula
| Unit

(** Map that holds the environment store *)
type environment = (value StringMap.t)

(** Map that holds the struct definitions *)
type struct_definitions = ((string * struct_type) list StringMap.t)

(** Map that holds the heap store *)
type heap = (((value list) StringMap.t) IntMap.t)

(** Memory allocation on the heap *)
let malloc (init_values: value StringMap.t) (h: heap) : int * heap =
  if StringMap.cardinal init_values == 0 then
    raise (SymbolicExecutionException "malloc cannot allocate nothing")
  else
    let init_values = init_values |> StringMap.map (fun v -> [v]) in
    let max_available_loc =
      IntMap.fold
        (fun loc fields previous_max ->
          let size = StringMap.cardinal fields in
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
    | Some _ ->
      let struct_data = IntMap.find loc h in
      let field_history = StringMap.find field struct_data in
        List.hd field_history
    | None -> raise (SymbolicExecutionException ("mget: field could not be found: " ^ field))
    )

(** Memory mutation on the heap *)
let mset (loc: int) (field: string) (type_id: string) (v: value) (h: heap) (sdef: struct_definitions) : heap =
  if IntMap.is_empty h then
    raise (SymbolicExecutionException "mset cannot set anything on an empty heap!")
  else
    let td = sdef |> StringMap.find type_id in
    (match List.find_index (fun (tid, _) -> String.equal tid field) td with
    | Some _ ->
      let struct_data = h |> IntMap.find loc in
      let field_history = struct_data |> StringMap.find field in
      let field_history = v :: field_history in
      let struct_data = struct_data |> StringMap.add field field_history in
        h |> IntMap.add loc struct_data
    | None -> raise (SymbolicExecutionException ("mset: field could not be found: " ^ field))
    )

let value_to_formula (value: value) (_env: environment) (_sdef: struct_definitions) (_h: heap) : formula = match value with
| Num(n) -> Num(n)
| Bool(b) -> Bool(b)
| Formula(form) -> form
| _ -> raise (SymbolicExecutionException "value_to_formula does not support all values")

let sort_of_formula (_formula: formula) (_env: environment) (_sdef: struct_definitions) (_h: heap) : Z3.Sort.sort =
  raise (SymbolicExecutionException "sort_of_formula TODO")

let rec formula_to_Z3 (formula: formula) (env: environment) (sdef: struct_definitions) (h: heap) : Z3.Expr.expr = match formula with
| Num(n) -> Z3.Arithmetic.Integer.mk_numeral_i ctx n
| Bool(b) -> Z3.Boolean.mk_val ctx b
| Id(id) ->
    let sort = (match env |> StringMap.find id with
      | Num(_)
      | Loc(_) -> int_sort
      | Bool(_) -> bool_sort
      | Formula(form) -> sort_of_formula form env sdef h
      | Unit -> raise (SymbolicExecutionException "formula_to_Z3 cannot get sort of Unit...")
      )
    in
    let sym = string_symbol id in
      Z3.Expr.mk_const ctx sym sort
| Mget(loc, field, struct_name) ->
    let struct_info = sdef |> StringMap.find struct_name in
    (match List.find_index (fun (name, _) -> String.equal name field) struct_info with
    | Some(_offset) ->
        let sym = string_symbol (string_of_int loc ^ "." ^ field) in
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

let rec insert_op_in_formula (op: binop) (formula: formula) (insert: formula) : formula = match formula with
| BinOp(Add, lhs, rhs) -> BinOp(Add, lhs, BinOp(op, rhs, insert))
| BinOp(Sub, lhs, rhs) -> BinOp(Sub, lhs, BinOp(op, rhs, insert))
| BinOp(Mul, lhs, rhs) -> BinOp(Mul, lhs, BinOp(op, rhs, insert))
| BinOp(Div, lhs, rhs) -> BinOp(Div, lhs, BinOp(op, rhs, insert))
| BinOp(op_, lhs, rhs) -> BinOp(op_, lhs, insert_op_in_formula op rhs insert)
| other -> BinOp(op, other, insert)

let rec derive (expr: expression) (env: environment) (sdef: struct_definitions) (h: heap) : Z3.Expr.expr = formula_to_Z3 (formula_of expr env sdef h) env sdef h (*match expr with
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
| _ -> raise (SymbolicExecutionException ("TODO: Derive does not support this AST node (yet?): " ^ string_of_expression expr))*)

and symexec (expr: expression) (env: environment) (sdef: struct_definitions) (res: value) (h: heap) (k: value -> heap -> unit): unit = match expr with
| Num(_i, n) -> k (Num(n)) h
| Bool(_i, b) -> k (Bool(b)) h
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
            | (_, Formula(_), Formula(_))
            | (_, _, Formula(_)) -> raise (SymbolicExecutionException "symexec BinOp: a formula may only appear on the left-hand side")
            | (op, Formula(form), rhs) -> Formula(insert_op_in_formula op form (value_to_formula rhs env sdef h))
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
    let assertion = derive assertion assert_env sdef h in
      solve [premise; assertion];
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
    let expected_types = sdef |> StringMap.find id in
    let field_exprs = List.combine expected_types exprs in
    let (values_list, h) =
      List.fold_right
        (fun ((field, _), expr) (fields, h) ->
          let value = ref Unit in
          let value_h = ref h in
          let concat = (fun (res: value) (h: heap): unit ->
            value := res;
            value_h := h
          )
          in
            symexec expr env sdef Unit h concat;
            (fields |> StringMap.add field !value, !value_h)
        )
        field_exprs
        (StringMap.empty, h)
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

    let update_h h assumption derefs_map : heap = IntMap.fold
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

    let _ = check_separation inv env sdef h in
    (* k for checking the invariant*)
    let k_check_inv = (fun (res: value) (h: heap) ->
      let inv_env = if res == Unit then env else env |> StringMap.add "result" res in
      let premise = get_premise inv_env sdef h in
      let inv = derive inv inv_env sdef h in
      let formula = Z3.Boolean.mk_implies ctx premise inv in
        solve [premise; formula];
      )
    in
      (* k for cond=false and invariant*)
      let k_cond_false = (fun (res: value) (h: heap) ->
        let inv_env = if res == Unit then env else env |> StringMap.add "result" res in

        let assumption: expression = BinOp(-1, And, inv, BinOp(-2, Eq, cond, Bool(-3, false))) in
        let derefs_map = find_derefs assumption in
        let h = update_h h assumption derefs_map in

        let premise = get_premise inv_env sdef h in
        let inv = derive inv inv_env sdef h in
        let formula = Z3.Boolean.mk_implies ctx premise inv in
          solve [premise; formula];
          k res h
        )
      in

      (* k for cond=true and invariant*)
      let k_cond_true = (fun (res: value) (h: heap) ->
        let inv_env = if res == Unit then env else env |> StringMap.add "result" res in

        let assumption: expression = BinOp(-1, And, inv, cond) in
        let derefs_map = find_derefs assumption in
        let h = update_h h assumption derefs_map in

        let premise = get_premise inv_env sdef h in
        let inv = derive inv inv_env sdef h in
        let formula = Z3.Boolean.mk_implies ctx premise inv in
          solve [premise; formula];
          symexec body env sdef Unit h k_check_inv
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
    (fun loc fields l ->
      StringMap.fold
        (fun field field_history l ->
          List.fold_right
            (fun (i, v) l ->
              match v with
              | Bool(b) ->
                  let id = if i == 0 then (string_of_int loc ^ "." ^ field) else (string_of_int loc ^ "." ^ field ^ ":" ^ string_of_int i) in
                  let sym = string_symbol id in
                  let c = Z3.Expr.mk_const ctx sym bool_sort in
                  let eq = Z3.Boolean.mk_eq ctx c (Z3.Boolean.mk_val ctx b) in
                    eq :: l
              | Num(n) ->
                  let id = if i == 0 then (string_of_int loc ^ "." ^ field) else (string_of_int loc ^ "." ^ field ^ ":" ^ string_of_int i) in
                  let sym = string_symbol id in
                  let c = Z3.Expr.mk_const ctx sym int_sort in
                  let eq = Z3.Boolean.mk_eq ctx c (Z3.Arithmetic.Integer.mk_numeral_i ctx n) in
                    eq :: l
              | Formula(form) -> formula_to_Z3 form env sdef h :: l
              | _ -> raise (SymbolicExecutionException "get_premise does not support all value types yet TODO")
            )
            (List.mapi (fun i v -> i, v) field_history)
            l
        )
        fields
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
