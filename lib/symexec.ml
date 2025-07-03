open Ast

let ctx = Z3.mk_context [("proof", "true")]

let int_symbol index = Z3.Symbol.mk_int ctx index
let string_symbol name = Z3.Symbol.mk_string ctx name

let int_sort = Z3.Arithmetic.Integer.mk_sort ctx
let bool_sort = Z3.Boolean.mk_sort ctx

let solver = Z3.Solver.mk_simple_solver ctx

exception SymbolicExecutionException of string

module StringMap = Map.Make(String)
type verifcation_env = (Z3.Symbol.symbol * Z3.Sort.sort) StringMap.t

let rec derive (expr: expression) (env: verifcation_env) : Z3.Expr.expr * Z3.Symbol.symbol * Z3.Sort.sort = match expr with
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
    let (lhs_expr, lhs_sym, lhs_sort) = derive lhs env in
    let (rhs_expr, rhs_sym, rhs_sort) = derive rhs env in
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
| Id(i, id) -> let (sym, sort) = env |> StringMap.find id in
      (match Z3.Sort.get_sort_kind sort with
      | BOOL_SORT -> (Z3.Boolean.mk_true ctx, sym, sort)
      | INT_SORT -> (Z3.Boolean.mk_true ctx, sym, sort)
      | _ -> raise (SymbolicExecutionException ("Unsupported sort at " ^ string_of_int i  ^ ": " ^ Z3.Sort.to_string sort))
      )
| Let(_i, id, bound, body) ->
    let (bound, bound_sym, bound_sort) = derive bound env in
    let env = env |> StringMap.add id (bound_sym, bound_sort) in
    let (body, body_sym, body_sort) = derive body env in
      (Z3.Boolean.mk_and ctx [bound; body], body_sym, body_sort)
| Seq(_i, expr0, expr1) ->
    let (expr0_formula, _, _) = derive expr0 env in
    let (expr1_formula, result_sym, result_sort) = derive expr1 env in
      (Z3.Boolean.mk_and ctx [expr0_formula; expr1_formula], result_sym, result_sort)
| Assert(_i, assertion, body) ->
    let (body_formula, result_sym, result_sort) = derive body env in
    let env = env |> StringMap.add "result" (result_sym, result_sort) in
    let (assertion_formula, assertion_sym, assertion_sort) = derive assertion env in
    let c = Z3.Expr.mk_const ctx assertion_sym assertion_sort in
      (Z3.Boolean.mk_and ctx [body_formula; assertion_formula; c], result_sym, result_sort)
| _ -> raise (SymbolicExecutionException "TODO: derive does not support all AST nodes yet!")

let rec verify (expr: expression) (env: verifcation_env) : Z3.Solver.status = match expr with
| Assert(_i, assertion, body) ->
  let (body_formula, result_sym, result_sort) = derive body env in
  let env = env |> StringMap.add "result" (result_sym, result_sort) in
  let (assertion_formula, assertion_sym, assertion_sort) = derive assertion env in
  let c = Z3.Expr.mk_const ctx assertion_sym assertion_sort in
    print_endline "Z3 assertion AST:"; print_endline (Z3.Expr.to_string assertion_formula); print_newline ();
    print_endline "Z3 AST: "; print_endline (Z3.Expr.to_string body_formula); print_newline ();
    Z3.Solver.check solver [body_formula; assertion_formula; c]
| e -> verify (Assert(-2, Bool(-1, true), e)) env
(*| _ -> raise (SymbolicExecutionException "TODO: verify does not support all AST nodes yet!")*)
