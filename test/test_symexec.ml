open Appendix_c_verifier.Parse
open Appendix_c_verifier.Symexec

let vf (src: string): bool =
  let prog = parse src in
    try (let _ = verify prog in true) with
    | _ -> false

let%test "Verify arithmetics with itself 1" =
  vf "3 + 4 - 1 * 8 / 3 + 1;
      @ result == 3 + 4 - 1 * 8 / 3 + 1 @"

let%test "Verify arithmetics with itself 2" =
  not (vf "3 + 4 - 1 * 8 / 3;
           @ result == 3 + 4 - 1 * 8 / 3 + 1 @")

let%test "Verify arithmetics with itself 3" =
  not (vf "3 + 4 - 1 * 8 / 3 + 1;
           @ result < 3 + 4 - 1 * 8 / 3 + 1 @")

let%test "Verify simple arithmetics" =
  vf "(let x := 5 in
      1 + 2 + 6 + 4 + x);
      @ 18 == result @"

let%test "Verify mixed asserts 1" =
  vf "let x := true in
      (let y := 5 in
        y + 7;
        @ result == 12 && y == 5 || (false == true) && false @);
      x;
      @ result @"

let%test "Verify mixed asserts 2" =
  vf "let x := true in
      (let y := 5 in
        y + 7;
        @ result == 12 && y > 4 || (false == true) && false @);
      x;
      @ result @"

let%test "Verify mixed asserts 3" =
  not (vf "let x := true in
          (let y := 5 in
            y + 7;
            @ result == 12 && y <= 4 || (false == true) && false @);
          x;
          @ result @")

let%test "Verify conditions 1" =
  vf "(let x := 2 in
        (if x > 4 then
          5;
          @ result < 7 @
        else
          10;
          @ result >= 7 @
        );
        @ result >= 5 @
      );
      @ result == 10 @"

let%test "Verify conditions 2" =
  vf "(let x := 2 in
        (if x > 4 then
          5;
          @ result < 7 @
        else
          10;
          @ result >= 7 @
        );
        @ result > 5 @
      );
      @ result == 10 @"

let%test "Verify conditions 3" =
  vf "(let x := 42 in
        (if x > 4 then
          5;
          @ result < 7 @
        else
          10;
          @ result >= 7 @
        );
        @ result >= 5 @
      );
      @ result == 5 @"

let%test "Verify conditions 4" =
  not (vf "(let x := 42 in
            (if x > 4 then
              5;
              @ result < 7 @
            else
              10;
              @ result >= 7 @
            );
            @ result > 5 @
          );
          @ result >= 5 @")

let%test "Verify conditions 5" =
  vf "(let x := 2 in
        if true then x + 8 else 8 + x
      );
      @ result == 10 @"

let%test "Verify shadowing 1" =
  vf "(let x := 2 in
        let x := 10 in
          x
      );
      @ result == 10 @"

let%test "Verify shadowing 2" =
  vf "(let x := 2 in
      let y := x + x in
      let x := 10 in
      let y := x + y in
        y
      );
      @ result == 14 @"

let%test "Verify shadowing 3" =
  vf "let x := 2 in
        @ x == 2 @;
        let x := 10 in
          @ x == 10 @;
          x"
