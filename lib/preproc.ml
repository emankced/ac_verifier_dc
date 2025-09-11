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
| BinOp(_) -> Seq(i, expr, to_inline)
| Id(_) -> Seq(i, expr, to_inline)
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
| BinOp(_) -> Assert(i, to_inline, expr)
| Id(_) -> Assert(i, to_inline, expr)
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

(** Returns static single assignment form, so every identifier is unique for its declaration *)
let rec ssa (expr: expression) (id_to_replace: string) (id_replacement: string): expression = match expr with
| Id(i, id) -> Id(i, if String.equal id id_to_replace then id_replacement else id)
| Let(i, id, bound, body) ->
    let bound = ssa bound id_to_replace id_replacement in
    let replacement = id ^ ":" ^ string_of_int i in
    let body =
      if String.equal id id_to_replace then
        ssa body id replacement
      else
        let body = ssa body id_to_replace id_replacement in
          ssa body id replacement
    in
      Let(i, replacement, bound, body)
| Num(_) -> expr
| Bool(_) -> expr
| Null(_) -> expr
| Unit(_) -> expr
| Cond(i, cond, then_body, else_body) ->
    Cond(i, ssa cond id_to_replace id_replacement, ssa then_body id_to_replace id_replacement, ssa else_body id_to_replace id_replacement)
| BinOp(i, op, lhs, rhs) ->
    BinOp(i, op, ssa lhs id_to_replace id_replacement, ssa rhs id_to_replace id_replacement)
| Seq(i, expr0, expr1) ->
    Seq(i, ssa expr0 id_to_replace id_replacement, ssa expr1 id_to_replace id_replacement)
| Assert(i, assertion, body) ->
    Assert(i, ssa assertion id_to_replace id_replacement, ssa body id_to_replace id_replacement)
| _ -> raise (PreprocException "ssa does not support this AST node (yet?)")
