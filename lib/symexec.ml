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
| True
| False
| Formula of Z3.Expr.expr
| Rules of proof_tree list
| Impl of proof_tree * proof_tree

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

let rec symexec (expr: expression) (env: environment) (sdef: struct_definitions) (h: heap): ((value * heap) list) * proof_tree = match expr with
| Num(_i, n) -> [(Num(n), h)], True
| Bool(_i, b) -> [(Bool(b), h)], True
| Null(_i) -> [(Loc(0, ""), h)], True
| Let(_i, id, bound, body) ->
    (* TODO do we need to check that no struct name is used, as the interpreter does? Maybe we can built a preprocessing step for that *)
    if (StringMap.exists (fun k _ -> String.equal k id) sdef) then
      raise (SymbolicExecutionException "Let ID already exists as struct name!")
    else
      let bound_vhl, bound_pt = symexec bound env sdef h in (* vhl = value heap list, pt = proof tree*)
      let vhl_pt_l = List.map (fun (v, h) ->
        let env = env |> StringMap.add id v in
        symexec body env sdef h
      ) bound_vhl in
      let vhl, ptl = List.fold_right (fun (vhl, pt) (vhl2, ptl) -> (List.append vhl vhl2, pt::ptl)) vhl_pt_l ([], [bound_pt]) in
        vhl, Rules(ptl)

| Id(_i, id) -> [(env |> StringMap.find id, h)], True
(*| BinOp(_i, op, lhs, rhs) ->
    let (lhs, h, l_lhs) = List.hd (symexec lhs env sdef h) in (* TODO handle lists *)
      let (rhs, h, l_rhs) = List.hd (symexec rhs env sdef h) in
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
        [(v, h, List.append l_lhs l_rhs)]*)
| Assert(_i, assertion, command) ->
    let vhl, pt = symexec command env sdef h in
    let formulae = List.fold_right (fun (v, h) formulae ->
        let env = env |> StringMap.add "result" v in
        let (assertion, sym, sort) = derive assertion env h in
        let c = Z3.Expr.mk_const ctx sym sort in
        let eq = Z3.Boolean.mk_eq ctx assertion c in
        let formula = Z3.Boolean.mk_and ctx [assertion; eq; c] in
        let formula = Formula(formula) in
          formula :: formulae
      ) vhl [] in
      vhl, Rules(pt :: formulae)
(*| Cond(_i, cond, then_body, else_body) ->
    let (then_v, then_h, then_l) = List.hd (symexec then_body env sdef h) in (* TODO support lists *)
    let (else_v, else_h, else_l) = List.hd (symexec else_body env sdef h) in
    let then_node = Impl(cond, then_l, env, h, sdef) in
    let else_node = Impl((BinOp(-1, Eq, cond, Bool(-2, false))), else_l, env, h, sdef) in
      (* TODO invalidate h entries properly *)
      [(then_v, then_h, [then_node]); (else_v, else_h, [else_node])]*)
| _ -> raise (SymbolicExecutionException "symexec does not support this AST node (yet?)")

let rec solve_tree (t: proof_tree) = (
    match t with
    | True -> ()
    | Formula(formula) -> solve [formula]
    | Rules(l) -> List.fold_right (fun t _ -> solve_tree t) l ()
    | _ -> raise (SymbolicExecutionException "TODO: solve_tree does not support this proof_tree node (yet?)")
  )

let verify (expr: expression) =
  let _, pt = symexec expr StringMap.empty StringMap.empty IntMap.empty in
    solve_tree pt
