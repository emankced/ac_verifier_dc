open Ast

(** Returns static single assignment form, so every identifier is unique for its declaration *)
let rec ssa (expr: expression) (id_to_replace: string) (id_replacement: string): expression = match expr with
| Id(i, id) -> Id(i, if String.equal id id_to_replace then id_replacement else id)
| Let(i, id, bound, body) ->
    let bound = ssa bound id_to_replace id_replacement in
    if String.contains id ':' then
      Let(i, id, bound, ssa body id_to_replace id_replacement)
    else
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
| Assert(i, assertion) ->
    Assert(i, ssa assertion id_to_replace id_replacement)
| Invariant(i, assertion, loop) ->
    Invariant(i, ssa assertion id_to_replace id_replacement, ssa loop id_to_replace id_replacement)
| While(i, cond, body) ->
    While(i, ssa cond id_to_replace id_replacement, ssa body id_to_replace id_replacement)
| For(i, id, start, end_, body) ->
    if String.contains id ':' then
      For(i, id, ssa start id_to_replace id_replacement, ssa end_ id_to_replace id_replacement, ssa body id_to_replace id_replacement)
    else
      let replacement = id ^ ":" ^ string_of_int i in
      let body =
        if String.equal id id_to_replace then
          body
        else
          ssa body id_to_replace id_replacement
      in
        For(i, replacement, ssa start id_to_replace id_replacement, ssa end_ id_to_replace id_replacement, ssa body id replacement)
| Struct(i, id, fields, body) -> Struct(i, id, fields, ssa body id_replacement id_replacement)
| Malloc(i, id, exprs) ->
    let exprs =
      List.map
        (fun e -> ssa e id_to_replace id_replacement)
        exprs
    in
      Malloc(i, id, exprs)
| Mfree(i, loc) -> Mfree(i, ssa loc id_to_replace id_replacement)
| Mset(i, loc, field, expr) -> Mset(i, ssa loc id_to_replace id_replacement, field, ssa expr id_to_replace id_replacement)
| Mget(i, loc, field) -> Mget(i, ssa loc id_to_replace id_replacement, field)
