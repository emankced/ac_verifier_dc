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

type verifcation_env = (Z3.Expr.expr * Z3.Symbol.symbol * Z3.Sort.sort) StringMap.t

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
| Id(i, id) -> let (expr, sym, sort) = env |> StringMap.find id in
      (match Z3.Sort.get_sort_kind sort with
      | BOOL_SORT -> (expr, sym, sort)
      | INT_SORT -> (expr, sym, sort)
      | _ -> raise (SymbolicExecutionException ("Unsupported sort at " ^ string_of_int i  ^ ": " ^ Z3.Sort.to_string sort))
      )
| _ -> raise (SymbolicExecutionException "TODO: derive does not support all AST nodes yet!")


exception Unsatisfiable
exception Unknown

let solve formula = match Z3.Solver.check solver formula with
| SATISFIABLE -> ()
| UNSATISFIABLE -> raise Unsatisfiable
| UNKNOWN -> raise Unknown (* should unknown raise an exception? *)

let rec verify (expr: expression) (env: verifcation_env) (constraints: Z3.Expr.expr list) : Z3.Expr.expr * Z3.Symbol.symbol * Z3.Sort.sort = match expr with
| Assert(_i, assertion, body) ->
  let (body_formula, result_sym, result_sort) = verify body env constraints in
  let env_with_result = env |> StringMap.add "result" (body_formula, result_sym, result_sort) in
  let (assertion_formula, assertion_sym, assertion_sort) = derive assertion env_with_result in
  let c = Z3.Expr.mk_const ctx assertion_sym assertion_sort in
    verify body env (assertion_formula :: c :: constraints)
| Let(_i, id, bound, body) ->
    let bound_variable_names = bound_variables bound in
    let (bound, bound_sym, bound_sort) = derive bound env in
    let variable_definitions = List.map (fun x -> let (expr, _, _) = env |> StringMap.find x in expr) bound_variable_names in
      solve (bound :: (List.append variable_definitions constraints));
      let env = env |> StringMap.add id (bound, bound_sym, bound_sort) in
        verify body env constraints
| Seq(_i, expr0, expr1) ->
    let _ = verify expr0 env constraints in
      verify expr1 env constraints
| Cond(i, cond, then_body, else_body) ->
    let bound_variable_names_cond = bound_variables cond in
    let bound_variable_names_then = bound_variables then_body in
    let bound_variable_names_else = bound_variables else_body in
    let variable_definitions_cond = List.map (fun x -> let (expr, _, _) = env |> StringMap.find x in expr) bound_variable_names_cond in
    let variable_definitions_then = List.map (fun x -> let (expr, _, _) = env |> StringMap.find x in expr) bound_variable_names_then in
    let variable_definitions_else = List.map (fun x -> let (expr, _, _) = env |> StringMap.find x in expr) bound_variable_names_else in
    let (cond, cond_sym, _cond_sort) = derive cond env in
    let cond_c = Z3.Boolean.mk_const ctx cond_sym in
      solve (cond :: (List.append variable_definitions_cond constraints));
      let (then_body, then_sym, then_sort) = verify then_body env constraints in
      let (else_body, else_sym, else_sort) = verify else_body env constraints in
      let then_c = Z3.Expr.mk_const ctx then_sym then_sort in
      let else_c = Z3.Expr.mk_const ctx else_sym else_sort in
      let sym = int_symbol i in
      let c = Z3.Expr.mk_const ctx sym then_sort in (* then_sort and else_sort should be the same. If not, then the type checker is to blame *)
      let formula =
        Z3.Boolean.mk_ite
        ctx
        (Z3.Boolean.mk_and ctx (cond :: cond_c :: variable_definitions_cond))
        (Z3.Boolean.mk_and ctx (then_body :: (Z3.Boolean.mk_eq ctx c then_c) :: variable_definitions_then))
        (Z3.Boolean.mk_and ctx (else_body :: (Z3.Boolean.mk_eq ctx c else_c) :: variable_definitions_else))
      in
        (*print_endline (Z3.Expr.to_string (Z3.Boolean.mk_and ctx (formula :: constraints)));*)
        solve (formula :: constraints);
        (formula, sym, then_sort)
| expr ->
    let bound_variable_names = bound_variables expr in
    let (expr, sym, sort) = derive expr env in
    let variable_definitions = List.map (fun x -> let (expr, _, _) = env |> StringMap.find x in expr) bound_variable_names in
    let formula = Z3.Boolean.mk_and ctx (expr :: variable_definitions) in
      solve (formula :: constraints);
      (formula, sym, sort)

(*| _ -> raise (SymbolicExecutionException "TODO: verify does not support all AST nodes yet!")*)
