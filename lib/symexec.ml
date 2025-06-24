let ctx = Z3.mk_context [("proof", "true")]

let int_symbol index = Z3.Symbol.mk_int ctx index

let int_sort = Z3.Arithmetic.Integer.mk_sort ctx

let x = int_symbol 0
let y = int_symbol 1

let expr = 
  let lhs = Z3.Expr.mk_const ctx x int_sort in
  let rhs = Z3.Expr.mk_const ctx y int_sort in
    Z3.Arithmetic.mk_ge ctx lhs rhs

let expr2 =
  let lhs = Z3.Expr.mk_numeral_int ctx 6 int_sort in
  let rhs = Z3.Expr.mk_const ctx x int_sort in
    Z3.Arithmetic.mk_ge ctx lhs rhs

let expr3 =
  let lhs = Z3.Expr.mk_numeral_int ctx 9 int_sort in
  let rhs = Z3.Expr.mk_const ctx y int_sort in
    Z3.Arithmetic.mk_le ctx lhs rhs

let solver = Z3.Solver.mk_simple_solver ctx
let status = Z3.Solver.check solver [expr; expr2; expr3] (* unsatisfiable example code *)

let res = match status with
| UNSATISFIABLE -> "unsatisfiable"
| UNKNOWN -> "unknown"
| SATISFIABLE -> "staisfiable"
