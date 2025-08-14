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

type proof_tree =
| Rules of proof_tree list
| Assert of expression * expression * environment * heap * struct_definitions
| Impl of proof_tree * proof_tree
| Unprocessed of expression
(*| Derived of Z3.Expr.expr * Z3.Symbol.symbol * Z3.Sort.sort*)

let rec symexec (expr: expression) (env: environment) (sdef: struct_definitions) (h: heap): value * heap * (proof_tree list) = match expr with
| Num(_i, n) -> (Num(n), h, [])
| Bool(_i, b) -> (Bool(b), h, [])
| Null(_i) -> (Loc(0, ""), h, [])
| Let(_i, id, bound, body) ->
    (* TODO do we need to check that no struct name is used, as the interpreter does? Maybe we can built a preprocessing step for that *)
    if (StringMap.exists (fun k _ -> String.equal k id) sdef) then
      raise (SymbolicExecutionException "Let ID already exists as struct name!")
    else
      let (bound, h, l_bound) = symexec bound env sdef h in
      let env = env |> StringMap.add id bound in
      let (body, h, l_body) = symexec body env sdef h in
        (body, h, (List.append l_bound l_body))
| Id(_i, id) -> (env |> StringMap.find id, h, [])
| BinOp(_i, op, lhs, rhs) ->
    let (lhs, h, l_lhs) = symexec lhs env sdef h in
      let (rhs, h, l_rhs) = symexec rhs env sdef h in
      let v =
        (match (op, lhs, rhs) with
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
        (v, h, List.append l_lhs l_rhs)
| Assert(_i, assertion, command) ->
    let proof_node = Assert(assertion, command, env, h, sdef) in
    let (v, h, l) = symexec command env sdef h in
      (v, h, proof_node :: l)
| _ -> (Unit, IntMap.empty, [])


let rec derive (expr: expression) (env: environment) (h: heap) : Z3.Expr.expr * Z3.Symbol.symbol * Z3.Sort.sort = match expr with
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
    let (lhs_expr, lhs_sym, lhs_sort) = derive lhs env h in
    let (rhs_expr, rhs_sym, rhs_sort) = derive rhs env h in
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
| Id(i, id) -> let v = env |> StringMap.find id in
      (match v with
      | Num(n) ->
          let sym = int_symbol i in
          let c = Z3.Arithmetic.Integer.mk_const ctx sym in
          let v = Z3.Arithmetic.Integer.mk_numeral_i ctx n in
            (Z3.Boolean.mk_eq ctx c v, sym, int_sort)
      | _ -> raise (SymbolicExecutionException "TODO: Derive Id does not support all types yet")
      )
| _ -> raise (SymbolicExecutionException "TODO: Derive does not support this AST node (yet?)")

let verify (expr: expression) =
  let (_, _, proof_nodes) = symexec expr StringMap.empty StringMap.empty IntMap.empty in
  let solve_node (n: proof_tree) = (
    match n with
    | Assert(assertion, command, env, h, sdef) ->
      let (result, _, _) = symexec command env sdef h in
      let (assertion, assertion_sym, assertion_sort) = derive assertion (env |> StringMap.add "result" result) h in
        let assertion_c = Z3.Expr.mk_const ctx assertion_sym assertion_sort in
        print_endline (Z3.Expr.to_string assertion);
        solve [assertion; assertion_c]
    | _ -> raise (SymbolicExecutionException "TODO: Verify does not support this proof_tree node (yet?)")
  )
  in
  let rec process_all_nodes (l: proof_tree list) = (match l with (x::xs) -> solve_node x; process_all_nodes xs | [] -> ()) in
    process_all_nodes proof_nodes
