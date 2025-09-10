open Ast
(*open Common*)

exception PreprocException of string

(*
let rec ssa (expr: expression): expression = match expr with
| _ -> raise (PreprocException "TODO")
*)

let rec inline_seq (i: ast_id) (expr: expression) (to_inline: expression): expression = match expr with
| Num(_) -> Seq(i, expr, to_inline)
| Bool(_) -> Seq(i, expr, to_inline)
| Null(_) -> Seq(i, expr, to_inline)
| Unit(_) -> Seq(i, expr, to_inline)
| Assert(_) -> Seq(i, expr, to_inline)
| Seq(i_, expr0, expr1) -> Seq(i_, expr0, inline_seq i expr1 to_inline)
| Cond(i_, cond, then_body, else_body) -> Cond(i_, cond, inline_seq i then_body to_inline, inline_seq i else_body to_inline)
| Let(i_, id, bound, body) -> Let(i_, id, bound, inline_seq i body to_inline)
| _ -> raise (PreprocException "inline_seq: AST node not yet implemented!")

let rec inline_assert (i: ast_id) (expr: expression) (to_inline: expression): expression = match expr with
| Num(_) -> Assert(i, to_inline, expr)
| Bool(_) -> Assert(i, to_inline, expr)
| Null(_) -> Assert(i, to_inline, expr)
| Unit(_) -> Assert(i, to_inline, expr)
| Seq(_) -> Assert(i, to_inline, expr)
| Let(i_, id, bound, body) -> Let(i_, id, bound, inline_assert i body to_inline)
| Assert(i_, assertion, body) -> Assert(i, BinOp(i_, And, assertion, to_inline), body)
| Cond(i_, cond, then_body, else_body) -> Cond(i_, cond, inline_assert i then_body to_inline, inline_assert i else_body to_inline)
| _ -> raise (PreprocException "inline_assert: AST node not yet implemented!")

let rec preproc (expr: expression): expression = match expr with
| Num(_) -> expr
| Bool(_) -> expr
| Null(_) -> expr
| Unit(_) -> expr
| Id(_) -> expr
| BinOp(i, op, lhs, rhs) -> BinOp(i, op, preproc lhs, preproc rhs)
| Cond(i, cond, then_body, else_body) -> Cond(i, (*preproc*) cond, preproc then_body, preproc else_body)
| Seq(i, expr0, expr1) -> inline_seq i (preproc expr0) (preproc expr1)
| Let(i, id, bound, body) -> Let(i, id, bound, preproc body) (*TODO currently bound can contain all commands. The language should only allow expressions in bound. *)
| Assert(i, assertion, body) -> inline_assert i (preproc body) assertion
| _ -> raise (PreprocException "preproc: AST node not yet implemented!")
