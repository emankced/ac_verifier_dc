(** Value generic map using strings as keys *)
module StringMap = Map.Make(String)

(** Value generic map using ints as keys *)
module IntMap = Map.Make(Int)