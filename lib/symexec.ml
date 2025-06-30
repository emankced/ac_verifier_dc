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
    let le = Z3.Arithmetic.mk_le ctx c v in
    let ge = Z3.Arithmetic.mk_ge ctx c v in
      (Z3.Boolean.mk_and ctx [le; ge], sym, int_sort)
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
      | Eq ->
          let le = Z3.Arithmetic.mk_le ctx lhs_c rhs_c in
          let ge = Z3.Arithmetic.mk_ge ctx lhs_c rhs_c in
            (Z3.Boolean.mk_and ctx [ge; le], false)
      | _ -> raise (SymbolicExecutionException "TODO: derive does not support all BinOps yet!")
      ) in
    let sym = int_symbol i in
    if is_int then
      let c = Z3.Arithmetic.Integer.mk_const ctx sym in
      let le = Z3.Arithmetic.mk_le ctx c v in
      let ge = Z3.Arithmetic.mk_ge ctx c v in
        (Z3.Boolean.mk_and ctx [lhs_expr; rhs_expr; le; ge], sym, int_sort)
    else
      let c = Z3.Expr.mk_const ctx sym bool_sort in
        (Z3.Boolean.mk_and ctx [lhs_expr; rhs_expr; v; c], sym, bool_sort)
| Id(i, id) -> let (sym, sort) = env |> StringMap.find id in
      (match Z3.Sort.get_sort_kind sort with
      | BOOL_SORT -> (Z3.Boolean.mk_const ctx sym, sym, sort)
      | INT_SORT -> (Z3.Boolean.mk_true ctx, sym, sort)
      | _ -> raise (SymbolicExecutionException ("Unsupported sort at " ^ string_of_int i  ^ ": " ^ Z3.Sort.to_string sort))
      )
| Let(_i, id, bound, body) ->
    let (bound, bound_sym, bound_sort) = derive bound env in
    let env = env |> StringMap.add id (bound_sym, bound_sort) in
    let (body, body_sym, body_sort) = derive body env in
      (Z3.Boolean.mk_and ctx [bound; body], body_sym, body_sort)
| _ -> raise (SymbolicExecutionException "TODO: derive does not support all AST nodes yet!")

let verify (expr: expression) (env: verifcation_env) : Z3.Solver.status = match expr with
| Assert(_i, assertion, body) ->
  (*TODO handle assertion*)
  let (body_formula, result_sym, result_sort) = derive body env in
  let env = env |> StringMap.add "result" (result_sym, result_sort) in
  let (assertion_formula, _, _) = derive assertion env in
    print_endline ("Z3 AST: " ^ Z3.Expr.to_string assertion_formula);
    print_endline ("Z3 AST: " ^ Z3.Expr.to_string body_formula);
    Z3.Solver.check solver [body_formula; assertion_formula]
| _ -> raise (SymbolicExecutionException "TODO: verify does not support all AST nodes yet!")
