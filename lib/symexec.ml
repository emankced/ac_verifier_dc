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

exception Unsatisfiable of string
exception Unknown of string

let solve formula = match Z3.Solver.check solver formula with
| SATISFIABLE -> ()
| UNSATISFIABLE -> raise (Unsatisfiable ("Solver returned UNSATISFIABLE! formula:\n" ^ Z3.Expr.to_string (if List.length formula == 1 then List.hd formula else Z3.Boolean.mk_and ctx formula)))
| UNKNOWN -> raise (Unknown ("Solver returned UNKNOWN! formula:\n" ^ Z3.Expr.to_string (if List.length formula == 1 then List.hd formula else Z3.Boolean.mk_and ctx formula)))

type formula =
| Num of int
| Bool of bool
| Id of string
| Mget of int * string * string * int (* location, field, struct name, version*)
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
type heap = ((((value * bool) list) StringMap.t) IntMap.t) (* value and flag, which is true if the value was assigned by the assign command. For an assumption the flag would be false. *)

(** List of all environments, struct definitions and heaps at the end of the symbolic execution. This is used by the postcondition generator. *)
let env_sdef_h_collection: (environment * struct_definitions * heap) list ref = ref []

(** Memory allocation on the heap *)
let malloc (init_values: value StringMap.t) (h: heap) : int * heap =
  if StringMap.cardinal init_values == 0 then
    raise (SymbolicExecutionException "malloc cannot allocate nothing")
  else
    let init_values = init_values |> StringMap.map (fun v -> [(v, true)]) in
    let max_available_loc =
      IntMap.fold
        (fun loc fields previous_max ->
          let size = StringMap.cardinal fields in
            let loc = loc + size in
              if loc > previous_max then loc else previous_max)
        h
        0x1 (*first available address*)
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
      let (v, _assigned_by_command) = List.hd field_history in
        v
    | None -> raise (SymbolicExecutionException ("mget: field could not be found: " ^ field))
    )

let rec pin_heap_version (form: formula) (h: heap) (assigned_by_command: bool) : formula = match form with
| BinOp(op, lhs, rhs) -> BinOp(op, pin_heap_version lhs h assigned_by_command, pin_heap_version rhs h assigned_by_command)
| Mget(loc, field, struct_name, version) ->
    if version != -1 then
      form
    else
      let field_history = h |> IntMap.find loc |> StringMap.find field in
      let history_length = List.length field_history in
      let version = if assigned_by_command then history_length - 1 else history_length in
        Mget(loc, field, struct_name, version)
| _ -> form

(** Memory mutation on the heap *)
let mset (loc: int) (field: string) (type_id: string) (v: value) (h: heap) (sdef: struct_definitions) (assigned_by_command: bool) : heap =
  if IntMap.is_empty h then
    raise (SymbolicExecutionException "mset cannot set anything on an empty heap!")
  else
    let v =
      (match v with
      | Formula(form) -> Formula(pin_heap_version form h assigned_by_command)
      | _ -> v
      )
    in
    let td = sdef |> StringMap.find type_id in
    (match List.find_index (fun (tid, _) -> String.equal tid field) td with
    | Some _ ->
      let struct_data = h |> IntMap.find loc in
      let field_history = struct_data |> StringMap.find field in
      let field_history = (v, assigned_by_command) :: field_history in
      let struct_data = struct_data |> StringMap.add field field_history in
        h |> IntMap.add loc struct_data
    | None -> raise (SymbolicExecutionException ("mset: field could not be found: " ^ field))
    )

let value_to_formula (value: value) (_env: environment) (_sdef: struct_definitions) (_h: heap) : formula = match value with
| Num(n) -> Num(n)
| Bool(b) -> Bool(b)
| Formula(form) -> form
| _ -> raise (SymbolicExecutionException "value_to_formula does not support all values")

let sort_of_formula (formula: formula) (sdef: struct_definitions): Z3.Sort.sort = match formula with
| Num(_) -> int_sort
| Bool(_) -> bool_sort
| BinOp(Add, _, _)
| BinOp(Sub, _, _)
| BinOp(Mul, _, _)
| BinOp(Div, _, _) -> int_sort
| BinOp(_) -> bool_sort
| Mget(_loc, field, struct_name, _version) ->
    let struct_definitions = sdef |> StringMap.find struct_name in
    let (_field, expected_type) = struct_definitions |> List.find (fun (f, _) -> String.equal field f) in
      (match expected_type with
      | NumT -> int_sort
      | BoolT -> bool_sort
      )
| _ -> raise (SymbolicExecutionException "Sort of formula may only be int or bool!")

let rec formula_to_Z3 (formula: formula) (env: environment) (sdef: struct_definitions) (h: heap) : Z3.Expr.expr * Z3.Expr.expr StringMap.t = match formula with
| Num(n) -> Z3.Arithmetic.Integer.mk_numeral_i ctx n, StringMap.empty
| Bool(b) -> Z3.Boolean.mk_val ctx b, StringMap.empty
| Id(id) ->
    let sort = (match env |> StringMap.find id with
      | Num(_)
      | Loc(_) -> int_sort
      | Bool(_) -> bool_sort
      | Formula(form) -> sort_of_formula form sdef
      | Unit -> raise (SymbolicExecutionException "formula_to_Z3 cannot get sort of Unit...")
      )
    in
    let sym = string_symbol id in
    let c = Z3.Expr.mk_const ctx sym sort in
      c, StringMap.empty |> StringMap.add id c
| Mget(loc, field, struct_name, version) ->
    let version =
      if version == -1 then
        let field_history = (h |> IntMap.find loc) |> StringMap.find field in
        let total_versions = List.length field_history in
          total_versions - 1
      else
        version
    in
    let struct_info = sdef |> StringMap.find struct_name in
    let (_name, expected_type) = List.find (fun (name, _expected_type) -> String.equal name field) struct_info in
    let id = (string_of_int loc ^ "." ^ field ^ ":" ^ string_of_int version) in
    let sym = string_symbol id in
      (match expected_type with
      | NumT -> let c = Z3.Arithmetic.Integer.mk_const ctx sym in c, StringMap.empty |> StringMap.add id c
      | BoolT -> let c = Z3.Boolean.mk_const ctx sym in c, StringMap.empty |> StringMap.add id c
      )
| BinOp(op, lhs, rhs) ->
  let (lhs, lhc_cs), (rhs, rhs_cs) = (formula_to_Z3 lhs env sdef h), (formula_to_Z3 rhs env sdef h) in
  let cs = lhc_cs |> StringMap.union (fun _id a _b -> Some(a)) rhs_cs in
  (match op with
  | Add -> Z3.Arithmetic.mk_add ctx [lhs; rhs], cs
  | Sub -> Z3.Arithmetic.mk_sub ctx [lhs; rhs], cs
  | Mul -> Z3.Arithmetic.mk_mul ctx [lhs; rhs], cs
  | Div -> Z3.Arithmetic.mk_div ctx lhs rhs, cs
  | Le -> Z3.Arithmetic.mk_le ctx lhs rhs, cs
  | Lt -> Z3.Arithmetic.mk_lt ctx lhs rhs, cs
  | Ge -> Z3.Arithmetic.mk_ge ctx lhs rhs, cs
  | Gt -> Z3.Arithmetic.mk_gt ctx lhs rhs, cs
  | Eq -> Z3.Boolean.mk_eq ctx lhs rhs, cs
  | Ne -> Z3.Boolean.mk_not ctx (Z3.Boolean.mk_eq ctx lhs rhs), cs
  | And | Sep -> Z3.Boolean.mk_and ctx [lhs; rhs], cs
  | Or -> Z3.Boolean.mk_or ctx [lhs; rhs], cs
  | _ -> raise (SymbolicExecutionException "formula_to_Z3 does not support all binops")
  )

let rec derive (expr: expression) (env: environment) (sdef: struct_definitions) (h: heap) : Z3.Expr.expr =
  let formula, _constants = formula_to_Z3 (formula_of expr env sdef h) env sdef h in formula

and symexec (expr: expression) (env: environment) (sdef: struct_definitions) (res: value) (h: heap) (k: value -> heap -> environment -> struct_definitions -> unit): unit = match expr with
| Num(_i, n) -> k (Num(n)) h env sdef
| Bool(_i, b) -> k (Bool(b)) h env sdef
| Unit(_i) -> k Unit h env sdef
| Let(_i, id, bound, body) ->
    (* TODO do we need to check that no struct name is used, as the interpreter does? Maybe we can built a preprocessing step for that *)
    if (StringMap.exists (fun k _ -> String.equal k id) sdef) then
      raise (SymbolicExecutionException "Let ID already exists as struct name!")
    else
      let k =
        (fun (res: value) (h: heap) _ _ ->
          let res =
            match res with
              | Formula(_form) -> Formula(formula_of bound env sdef h)
              | _ -> res
          in
            let env = env |> StringMap.add id res in
            symexec body env sdef Unit h k
        )
      in
        symexec bound env sdef Unit h k
| Id(_i, id) -> k (env |> StringMap.find id) h env sdef
| BinOp(_i, op, lhs, rhs) ->
    let k = (fun (res_lhs: value) (h: heap) _ _ ->
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
            | (op, Formula(_lhs), Formula(_rhs)) -> Formula(BinOp(op, formula_of lhs env sdef h, formula_of rhs env sdef h)) (* get formula from lhs without symexec result *)
            | (op, lhs, Formula(_form)) -> Formula(BinOp(op, value_to_formula lhs env sdef h, formula_of rhs env sdef h))
            | (op, Formula(_form), rhs) -> Formula(BinOp(op, formula_of lhs env sdef h, value_to_formula rhs env sdef h))
            | _ -> raise (SymbolicExecutionException "Unsupported binary operation!")
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
    let (premise, constants) = get_premise assert_env sdef h in
    let assertion = derive assertion assert_env sdef h in
    let formula = Z3.Boolean.mk_implies ctx premise assertion in
      (if StringMap.is_empty constants then
        solve [premise; formula]
      else
        let constants =
          StringMap.fold
            (fun _id c l -> c :: l)
            constants
            []
        in
        let forall = Z3.Quantifier.mk_forall_const ctx constants formula None [] [] None None in
        let forall = Z3.Quantifier.expr_of_quantifier forall in
          solve [forall]
      );

      k res h env sdef
| Seq(_i, expr0, expr1) ->
    let k = (fun (res: value) (h: heap) _ _ ->
        symexec expr1 env sdef res h k
      )
    in
      symexec expr0 env sdef res h k
| Cond(_i, cond, then_body, else_body) ->
    let (premise, _constants) = get_premise env sdef h in
    let derived_cond = derive cond env sdef h in
    let pos =
    (try solve [premise; derived_cond]; true with
    | Unsatisfiable(_) -> false
    | Unknown(_) ->
        (*TODO abstract with cond*)
        raise (SymbolicExecutionException "TODO: Cond unknown is not supported yet")
    )
  in
  let neg =
    (try solve [premise; Z3.Boolean.mk_not ctx derived_cond]; true with
    | Unsatisfiable(_) -> false
    | Unknown(_) ->
        (*TODO abstract with cond*)
        raise (SymbolicExecutionException "TODO: Cond unknown is not supported yet")
    )
  in
    (match pos, neg with
    | true, false -> symexec then_body env sdef Unit h k
    | false, true -> symexec else_body env sdef Unit h k
    | true, true ->
        (* assume cond and execute both branches symbolically *)
        (* k for cond=true *)
        let k_cond_true = (fun (res: value) (h: heap) ->
          let assumption: expression = cond in
          let derefs_map = find_derefs cond env sdef h in
          let h = update_h h assumption derefs_map env sdef in
            symexec then_body env sdef res h k
          )
        in
        (* k for cond=false *)
        let k_cond_false = (fun (res: value) (h: heap) ->
          let assumption: expression = BinOp(-1, Eq, cond, Bool(-2, false)) in
          let derefs_map = find_derefs cond env sdef h in
          let h = update_h h assumption derefs_map env sdef in
            symexec else_body env sdef res h k
          )
        in
          k_cond_true Unit h;
          k_cond_false Unit h
    | false, false ->
        raise (SymbolicExecutionException "Cond is not satisfiable at all. This case should be impossible!")
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
          let concat = (fun (res: value) (h: heap) _ _: unit ->
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
          k (Loc(loc, id)) h env sdef
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
    let k = (fun (res: value) (h: heap) _ _ ->
      match res with
      | Loc(l, id) ->
          let k = (fun (res: value) (h: heap) ->
            k Unit (mset l field id res h sdef true)
            )
          in
            symexec expr env sdef Unit h k
      | _ -> raise (SymbolicExecutionException "Mset requires a location!")
      )
    in
      symexec loc env sdef Unit h k
| Invariant(_, inv, While(_, cond, body)) ->
    let _ = check_separation inv env sdef h in
    (* k for checking the invariant*)
    let k_check_inv = (fun (res: value) (h: heap) _ _ ->
      let inv_env = if res == Unit then env else env |> StringMap.add "result" res in
      let (premise, constants) = get_premise inv_env sdef h in
      let inv = derive inv inv_env sdef h in
      let formula = Z3.Boolean.mk_implies ctx premise inv in
      if StringMap.is_empty constants then
        solve [premise; formula] (* cannot quantify over empty constant list, therefore just check satisfiability *)
      else
        let constants =
          StringMap.fold
            (fun _id c l -> c :: l)
            constants
            []
        in
        let forall = Z3.Quantifier.mk_forall_const ctx constants formula None [] [] None None in
        let forall = Z3.Quantifier.expr_of_quantifier forall in
          solve [forall]
      )
    in
      (* k for cond=false and invariant*)
      let k_cond_false = (fun (res: value) (h: heap) ->
          let assumption: expression = BinOp(-1, And, inv, BinOp(-2, Eq, cond, Bool(-3, false))) in
          let derefs_map = find_derefs assumption env sdef h in
          let h = update_h h assumption derefs_map env sdef in
          k res h env sdef
        )
      in

      (* k for cond=true and invariant*)
      let k_cond_true = (fun (res: value) (h: heap) ->
        (* check whether the loop body is reachable*)
        let (premise, _constants) = get_premise env sdef h in
        let cond_formula = derive cond env sdef h in
        let formula = Z3.Boolean.mk_implies ctx premise cond_formula in
        let reachable =
          (try
            solve [premise; formula];
            true
          with
          | Unsatisfiable(_) -> false
          | Unknown(_) -> raise (SymbolicExecutionException "symexec: satisfiability of while condition must never be unknown!")
          )
        in
        if reachable then
          let inv_env = if res == Unit then env else env |> StringMap.add "result" res in

          let assumption: expression = cond (*BinOp(-1, And, inv, cond)*) in
          let derefs_map = find_derefs assumption env sdef h in
          let h' = update_h h assumption derefs_map env sdef in

          let (premise, constants) = get_premise inv_env sdef h' in
          let inv_formula = derive inv inv_env sdef h' in
          let formula = Z3.Boolean.mk_implies ctx premise inv_formula in
            (if StringMap.is_empty constants then
              solve [premise; formula] (* cannot quantify over empty constant list, therefore just check satisfiability *)
            else
              let constants =
                StringMap.fold
                  (fun _id c l -> c :: l)
                  constants
                  []
              in
              let forall = Z3.Quantifier.mk_forall_const ctx constants formula None [] [] None None in
              let forall = Z3.Quantifier.expr_of_quantifier forall in
                solve [forall]
            );

            let assumption: expression = BinOp(-1, And, inv, cond) in
            let derefs_map = find_derefs assumption env sdef h in
            let h = update_h h assumption derefs_map env sdef in
              symexec body env sdef Unit h k_check_inv
        )
      in
        k_check_inv res h env sdef;
        k_cond_true res h;
        k_cond_false res h
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
    let k = (fun (res: value) (_h: heap) _ _ ->
        r := res
      ) in
      symexec loc env sdef Unit h k;
      (match !r with
      | Loc(l, _) -> IntSet.empty |> IntSet.add l
      | Formula(_) -> raise (SymbolicExecutionException "Separation violated due to abstracted location!")
      | _ -> raise (SymbolicExecutionException "check_separation expected location!")
      )
| _ -> raise (SymbolicExecutionException "check_separation does not support this AST node!")

and get_premise (env: environment) (sdef: struct_definitions) (h: heap) : Z3.Expr.expr * Z3.Expr.expr StringMap.t =
  let env_list, env_constants = StringMap.fold
    (fun id v (l, cs) ->
      let v, sort, more_cs = match v with
      | Bool(b) -> (if b then Z3.Boolean.mk_true ctx else Z3.Boolean.mk_false ctx), bool_sort, StringMap.empty
      | Num(n) -> Z3.Arithmetic.Integer.mk_numeral_i ctx n, int_sort, StringMap.empty
      | Loc(l, _name) -> Z3.Arithmetic.Integer.mk_numeral_i ctx l, int_sort, StringMap.empty
      | Formula(form) ->
          let formula, constants = formula_to_Z3 form env sdef h in
            formula, sort_of_formula form sdef, constants
      | _ -> raise (SymbolicExecutionException "get_premise does not support all value types yet TODO")
      in
        let sym = string_symbol id in
        let c = Z3.Expr.mk_const ctx sym sort in
        let eq = Z3.Boolean.mk_eq ctx c v in
          eq :: l, more_cs |> StringMap.add id c |> StringMap.union (fun _id a _b -> Some(a)) cs
    )
    env
    ([], StringMap.empty)
  in
  let h_list, h_constants = IntMap.fold
    (fun loc fields (l, cs) ->
      StringMap.fold
        (fun field field_history (l, cs) ->
          let newest_element_index = (List.length field_history) - 1 in
            List.fold_right
              (fun (i, v, assigned_by_command) (l, cs) ->
                match v with
                | Bool(b) ->
                    let id = string_of_int loc ^ "." ^ field ^ ":" ^ string_of_int i in
                    let sym = string_symbol id in
                    let c = Z3.Expr.mk_const ctx sym bool_sort in
                    let eq = Z3.Boolean.mk_eq ctx c (Z3.Boolean.mk_val ctx b) in
                      eq :: l, cs |> StringMap.add id c
                | Num(n) ->
                    let id = string_of_int loc ^ "." ^ field ^ ":" ^ string_of_int i in
                    let sym = string_symbol id in
                    let c = Z3.Expr.mk_const ctx sym int_sort in
                    let eq = Z3.Boolean.mk_eq ctx c (Z3.Arithmetic.Integer.mk_numeral_i ctx n) in
                      eq :: l, cs |> StringMap.add id c
                | Formula(form) ->
                  if assigned_by_command then
                    let id = string_of_int loc ^ "." ^ field ^ ":" ^ string_of_int i in
                    let sym = string_symbol id in
                    let c = Z3.Expr.mk_const ctx sym (sort_of_formula form sdef) in
                    let form, more_cs = formula_to_Z3 form env sdef h in
                    let eq = Z3.Boolean.mk_eq ctx c form in
                      eq :: l, more_cs |> StringMap.add id c |> StringMap.union (fun _id a _b -> Some(a)) cs
                  else
                    let form, more_cs = formula_to_Z3 form env sdef h in
                      form :: l, more_cs |> StringMap.union (fun _id a _b -> Some(a)) cs
                | _ -> raise (SymbolicExecutionException "get_premise does not support all value types yet TODO")
              )
              (List.mapi (fun i (v, assigned_by_command) -> newest_element_index - i, v, assigned_by_command) field_history)
              (l, cs)
        )
        fields
        (l, cs)
    )
    h
    ([], StringMap.empty)
  in
  let constants = env_constants |> StringMap.union (fun _id a _b -> Some(a)) h_constants in
    Z3.Boolean.mk_and ctx (List.append env_list h_list), constants

and find_derefs (expr: expression) (env: environment) (sdef: struct_definitions) (h: heap) : (string * StringSet.t) IntMap.t =
  (match expr with
  | BinOp(_, _op, lhs, rhs) -> IntMap.union (fun _l (t, lhs) (_t, rhs) -> Some(t, StringSet.union lhs rhs)) (find_derefs lhs env sdef h) (find_derefs rhs env sdef h)
  | Mget(_, loc, field) ->
      let r = ref Unit in
      let k =
        (fun res _h _ _ ->
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

and contains_deref (code: expression) (addr: int) (field: string) (env: environment) (sdef: struct_definitions) (h: heap) : bool =
  (match code with
  | Mget(_, loc, field_) ->
      if not (String.equal field field_) then
        false
      else
        let r = ref Unit in
        let k =
          (fun res _h _ _ ->
            r := res
          )
        in
          symexec loc env sdef Unit h k;
          (match !r with
          | Loc(addr_, _struct_name) ->
              addr == addr_
          | _ -> raise (SymbolicExecutionException "find_derefs requires location!")
          )
  | BinOp(_, _op, lhs, rhs) -> (contains_deref lhs addr field env sdef h) || (contains_deref rhs addr field env sdef h)
  | _ -> false
  )

and formulae_of_deref (code: expression) (addr: int) (struct_name: string) (field: string) (env: environment) (sdef: struct_definitions) (h: heap) : formula list =
  (match code with
  | BinOp(_, And, lhs, rhs) -> (*TODO does Or has to be specially handled as well? *)
    (match
      contains_deref lhs addr field env sdef h,
      contains_deref rhs addr field env sdef h
    with
    | true, true -> List.append (formulae_of_deref lhs addr struct_name field env sdef h) (formulae_of_deref rhs addr struct_name field env sdef h)
    | true, false -> formulae_of_deref lhs addr struct_name field env sdef h
    | false, true -> formulae_of_deref rhs addr struct_name field env sdef h
    | false, false -> []
    )
  | x -> [formula_of x env sdef h]
  )

and update_h h assumption derefs_map (env: environment) (sdef: struct_definitions) : heap = IntMap.fold
    (fun addr (struct_name, fields) h ->
      StringSet.fold
        (fun field h ->
          let formulae = formulae_of_deref assumption addr struct_name field env sdef h in
          let form =
            match formulae with
            | x :: xs -> List.fold_right (fun a b -> BinOp(And, a, b)) xs x
            | _ -> raise (SymbolicExecutionException "symexec: formula list needs at least one element!")
          in
          let h = mset addr field struct_name (Formula(form)) h sdef false in
            h
        )
        fields
        h
    )
  derefs_map
  h

and formula_of (expr: expression) (env: environment) (sdef: struct_definitions) (h: heap) : formula  = match expr with
| Num(_, n) -> Num(n)
| Bool(_, b) -> Bool(b)
| BinOp(_, op, lhs, rhs) -> BinOp(op, formula_of lhs env sdef h, formula_of rhs env sdef h)
| Mget(_, loc, field) ->
    let r = ref Unit in
    let k = (fun res _h _ _ -> r := res) in
      symexec loc env sdef Unit h k;
      (match !r with
      | Loc(addr, struct_name) -> Mget(addr, field, struct_name, -1) (* insert stub version *)
      | _ -> raise (SymbolicExecutionException "formula_of needs a location for Mget!")
      )
| Id(_, id) -> Id(id)
| _ -> raise (SymbolicExecutionException "formula_of does not support all AST nodes")

let verify (expr: expression) =
  let env = StringMap.empty in
  let sdef = StringMap.empty in
  let res = Unit in
  let h = IntMap.empty in
  let k = (fun (_res: value) (h: heap) (env: environment) (sdef: struct_definitions) -> env_sdef_h_collection := (env, sdef, h) :: !env_sdef_h_collection) in
    symexec expr env sdef res h k

let generate_postcondition (_: unit) : string =
  let premises =
    List.map
      (fun (env, sdef, h) -> let premise, _constants = get_premise env sdef h in premise)
      !env_sdef_h_collection
  in
  let postcondition = Z3.Boolean.mk_or ctx premises in
    Z3.Expr.to_string postcondition

let get_locations_missing_symbol_definition (_: unit): IntSet.t =
  let rec check_missing_in_formula (form: formula) (h: heap) : IntSet.t =
    match form with
    | BinOp(_op, lhs, rhs) -> check_missing_in_formula lhs h |> IntSet.union (check_missing_in_formula rhs h)
    | Mget(loc, _field, _struct_name, _version) ->
        (match h |> IntMap.find_opt loc with
        | Some(_) -> IntSet.empty
        | None -> IntSet.empty |> IntSet.add loc
        )
    | _ -> IntSet.empty
  in
  let missing =
    List.fold_right
      (fun (env, _sdef, h) missing ->
        let missing =
          StringMap.fold
            (fun _id v missing ->
              match v with
              | Formula(form) -> check_missing_in_formula form h |> IntSet.union missing
              | _ -> missing
            )
            env
            missing
        in

        let missing =
          IntMap.fold
            (fun _loc fields missing ->
              StringMap.fold
                (fun _id values missing ->
                  List.fold_right
                    (fun (v, _by_assign) missing ->
                      match v with
                      | Formula(form) -> check_missing_in_formula form h |> IntSet.union missing
                      | _ -> missing
                    )
                    values
                    missing
                )
                fields
                missing
            )
            h
            missing
        in
          missing
      )
      !env_sdef_h_collection
      IntSet.empty
  in
    missing
