open Appendix_c_verifier.Parse
open Appendix_c_verifier.Symexec
open Appendix_c_verifier.Preproc

let vf (src: string): bool =
  let prog = parse src in
  let prog = ssa prog "" "" in
  let prog = preproc prog in
    try (let _ = verify prog in true) with
    | _ -> false

let%test "Verify arithmetics with itself 1" =
  vf "@ result == 3 + 4 - 1 * 8 / 3 + 1 @
      3 + 4 - 1 * 8 / 3 + 1"

let%test "Verify arithmetics with itself 2" =
  not (vf "@ result == 3 + 4 - 1 * 8 / 3 + 1 @
          3 + 4 - 1 * 8 / 3")

let%test "Verify arithmetics with itself 3" =
  not (vf "@ result < 3 + 4 - 1 * 8 / 3 + 1 @
          3 + 4 - 1 * 8 / 3 + 1")

let%test "Verify simple arithmetics" =
  vf "@ 18 == result @
      let x := 5 in
      1 + 2 + 6 + 4 + x"

let%test "Verify mixed asserts 1" =
  vf "@ result @
      let x := true in
      (let y := 5 in
          @ result == 12 && y == 5 || (false == true) && false @
          y + 7);
      x"

let%test "Verify mixed asserts 2" =
  vf "@ result @
      let x := true in
      (let y := 5 in
          @ result == 12 && y > 4 || (false == true) && false @
          y + 7);
      x"

let%test "Verify mixed asserts 3" =
  not (vf "@ result @
          let x := true in
          (let y := 5 in
              @ result == 12 && y <= 4 || (false == true) && false @
              y + 7);
          x")

let%test "Verify conditions 1" =
  vf "@ result == 10 @
      let x := 2 in
        @ result >= 5 @
        if x > 4 then
          @ result < 7 @
          5
        else
          @ result >= 7 @
          10"

let%test "Verify conditions 2" =
  vf "@ result == 10 @
      let x := 2 in
        @ result > 5 @
        if x > 4 then
          @ result < 7 @
          5
        else
          @ result >= 7 @
          10"

let%test "Verify conditions 3" =
  vf "@ result == 5 @
      let x := 42 in
        @ result >= 5 @
        if x > 4 then
          @ result < 7 @
          5
        else
          @ result >= 7 @
          10"

let%test "Verify conditions 4" =
  not (vf "@ result >= 5 @
          let x := 42 in
            @ result > 5 @
            if x > 4 then
              @ result < 7 @
              5
            else
              @ result >= 7 @
              10")

let%test "Verify conditions 5" =
  vf "@ result == 10 @
      let x := 2 in
        if true then x + 8 else 8 + x"

let%test "Verify aliasing 1" =
  vf "@ result == 10 @
      let x := 2 in
        let x := 10 in
          x"

let%test "Verify aliasing 2" =
  vf "@ result == 14 @
      let x := 2 in
      let y := x + x in
      let x := 10 in
      let y := x + y in
        y"

let%test "Verify aliasing 3" =
  vf "let x := 2 in
        @ x == 2 @
        let x := 10 in
          @ x == 10 @
            x"
