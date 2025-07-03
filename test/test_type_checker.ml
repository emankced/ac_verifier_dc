open Appendix_c_verifier.Parse
open Appendix_c_verifier.Analysis

let env: type_environment = TypeEnvironmentMap.empty
let sdef: struct_type_definitions = TypeEnvironmentMap.empty
let tm: ast_types = TypeASTMap.empty

let%test "Type check arithmetics" =
  let prog = parse "3 + 4 - 1 * 8 / 3 + 1" in
    let (res, tm) = type_check prog env sdef tm in
      res == Num && (TypeASTMap.fold (fun _ t b -> b && t == Num) tm true)

let%test "Type check arithmetics mismatch" =
  let prog = parse "3 + 4 - 1 * 8 / null + 1" in
    try
      ignore (type_check prog env sdef tm);
      false
    with
      | TypeCheckError _ -> true
      | _ -> false

let%test "Type check conditional Num" =
  let prog = parse "if true then 5 else 6" in
    let (res, _) = type_check prog env sdef tm in
      res == Num

let%test "Type check conditional Loc 1" =
  let prog = parse "struct num {n: int} in if true then malloc(num, 0) else null" in
    let (res, _) = type_check prog env sdef tm in
      match res with
      | Loc(id) -> String.equal id "num"
      | _ -> false

let%test "Type check conditional Loc 2" =
  let prog = parse "struct num {n: int} in if false then malloc(num, 0) else null" in
    let (res, _) = type_check prog env sdef tm in
      match res with
      | Loc(id) -> String.equal id "num"
      | _ -> false

let%test "Type check conditional Loc" =
  let prog = parse "struct num {n: int} in if true then malloc(num, 0) else null" in
    let (res, _) = type_check prog env sdef tm in
      match res with
      | Loc(id) -> String.equal id "num"
      | _ -> false

let%test "Type check conditional Null" =
  let prog = parse "if true then null else null" in
    let (res, _) = type_check prog env sdef tm in
      res == Null

let%test "Type check conditional Bool" =
  let prog = parse "if true then false else true" in
    let (res, _) = type_check prog env sdef tm in
      res == Bool

let%test "Type check conditional mismatch 1" =
  let prog = parse "if 5 then false else true" in
    try
      ignore (type_check prog env sdef tm);
      false
    with
      | TypeCheckError _ -> true
      | _ -> false

let%test "Type check conditional mismatch 2" =
  let prog = parse "if false then false else 5" in
    try
      ignore (type_check prog env sdef tm);
      false
    with
      | TypeCheckError _ -> true
      | _ -> false

let%test "Type check Deref" =
  let prog = parse "struct num {n: int} in let n := malloc(num, 5) in !n.n" in
    let (res, _) = type_check prog env sdef tm in
      res == Num

let%test "Type check For" =
  let prog = parse "struct num {n: int} in let sum := malloc(num, 0) in (for i in [1 to 5] do !sum.n := !sum.n + i); !sum.n" in
    let (res, _) = type_check prog env sdef tm in
      res == Num

let%test "Type check For mismatch 1" =
  let prog = parse "struct num {n: int} in let sum := malloc(num, 0) in (for i in [true to 5] do !sum.n := !sum.n + i); !sum.n" in
    try
      ignore (type_check prog env sdef tm);
      false
    with
      | TypeCheckError _ -> true
      | _ -> false

let%test "Type check For mismatch 2" =
  let prog = parse "struct num {n: int} in let sum := malloc(num, 0) in (for i in [1 to false] do !sum.n := !sum.n + i); !sum.n" in
    try
      ignore (type_check prog env sdef tm);
      false
    with
      | TypeCheckError _ -> true
      | _ -> false

let%test "Type check While" =
  let prog = parse "struct num {n: int} in let sum := malloc(num, 0) in (while !sum.n < 20 do !sum.n := !sum.n + !sum.n); !sum.n" in
    let (res, _) = type_check prog env sdef tm in
      res == Num

let%test "Type check While mismatch" =
  let prog = parse "struct num {n: int} in let sum := malloc(num, 0) in (while 20 do !sum.n := !sum.n + !sum.n); !sum.n" in
    try
      ignore (type_check prog env sdef tm);
      false
    with
      | TypeCheckError _ -> true
      | _ -> false
