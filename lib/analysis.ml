open Ast

(** Map that holds the environment store *)
module TypeEnvironmentMap = Map.Make(String)

(** Map that holds type information of all AST nodes *)
module TypeASTMap = Map.Make(Int)

type types =
| Null
| Loc of string
| Num
| Bool
| Unit
| Unknown

(** Type of the environment map *)
type type_environment = (types TypeEnvironmentMap.t)

(** Type of the struct definition map *)
type struct_type_definitions = ((string * types) list TypeEnvironmentMap.t)

(** Type of the type map *)
type ast_types = (types TypeASTMap.t)

(** Exception used by the type checker *)
exception TypeCheckError of string

let types_to_string (t: types) : string = match t with
| Null -> "Null"
| Loc(id) -> "Loc(" ^ id ^ ")"
| Num -> "Num"
| Bool -> "Bool"
| Unit -> "Unit"
| Unknown -> "Unknown"

let rec type_check (expr: Ast.expression) (env: type_environment) (sdef: struct_type_definitions) (tm: ast_types) : types * Ast.expression * ast_types = match expr with
| Null(i) -> (Null, expr, tm |> TypeASTMap.add i Null)
| Num(i, _) -> (Num, expr, tm |> TypeASTMap.add i Num)
| Bool(i, _) -> (Bool, expr, tm |> TypeASTMap.add i Bool)
| Unit(i) -> (Unit, expr, tm |> TypeASTMap.add i Unit)
| BinOp(i, op, lhs, rhs) ->
    let (lhs, lhs_expr, tm) = type_check lhs env sdef tm in
      let (rhs, rhs_expr, tm) = type_check rhs env sdef tm in
        let t = (match (op, lhs, rhs) with
        | (Add, Num, Num) -> Num
        | (Sub, Num, Num) -> Num
        | (Mul, Num, Num) -> Num
        | (Div, Num, Num) -> Num
        | (Eq, Num, Num) -> Bool
        | (Ne, Num, Num) -> Bool
        | (Eq, Bool, Bool) -> Bool
        | (Ne, Bool, Bool) -> Bool
        | (Eq, Loc(_), Loc(_)) -> Bool
        | (Ne, Loc(_), Loc(_)) -> Bool
        | (Eq, Loc(_), Null) -> Bool
        | (Ne, Loc(_), Null) -> Bool
        | (Eq, Null, Loc(_)) -> Bool
        | (Ne, Null, Loc(_)) -> Bool
        | (Eq, Null, Null) -> Bool
        | (Ne, Null, Null) -> Bool
        (* should unit get a comparison definition? *)
        | (Le, Num, Num) -> Bool
        | (Lt, Num, Num) -> Bool
        | (Ge, Num, Num) -> Bool
        | (Gt, Num, Num) -> Bool
        | (And, Bool, Bool) -> Bool
        | (Or, Bool, Bool) -> Bool
        | (_, lhs, rhs) -> raise (TypeCheckError ("BinOp:" ^ string_of_int i ^ " Operator and operands do not match: " ^ types_to_string lhs ^ " and " ^ types_to_string rhs))
        ) in (t, BinOp(i, op, lhs_expr, rhs_expr), tm |> TypeASTMap.add i t)
| Id(i, id) -> let t = env |> TypeEnvironmentMap.find id in (t, expr, tm |> TypeASTMap.add i t)
| Let(i, id, bound, body) ->
    let (bound, bound_expr, tm) = type_check bound env sdef tm in
      let env = env |> TypeEnvironmentMap.add id bound in
        let (body, body_expr, tm) = type_check body env sdef tm in
          (body, Let(i, id, bound_expr, body_expr), tm |> TypeASTMap.add i body)
| Cond(i, cond, then_body, else_body) ->
  (match (type_check cond env sdef tm) with
  | (Bool, cond, tm) ->
      let (lhs, then_body, tm) = type_check then_body env sdef tm in
      let (rhs, else_body, tm) = type_check else_body env sdef tm in
      let (t, correct) =
        (match (lhs, rhs) with
        | (Loc(_), Null) -> (lhs, true)
        | (Null, Loc(_)) -> (rhs, true)
        | (Loc(idl), Loc(idr)) -> (lhs, String.equal idl idr)
        | (lhs, rhs) -> (lhs, lhs == rhs))
      in
        if correct then (t, Cond(i, cond, then_body, else_body), tm |> TypeASTMap.add i t)
        else raise (TypeCheckError ("Cond:" ^ string_of_int i ^ " requires both branches to have the same type!"))
  | _ -> raise (TypeCheckError ("Cond:" ^ string_of_int i ^ " requires a bool as condition!"))
  )
| Seq(i, expr0, expr1) ->
    let (_, expr0, tm) = type_check expr0 env sdef tm in
      let (t, expr1, tm) = type_check expr1 env sdef tm in
        (t, Seq(i, expr0, expr1), tm |> TypeASTMap.add i t)
| Struct(i, id, types, body) ->
    if TypeEnvironmentMap.exists (fun k _ -> String.equal id k) sdef || TypeEnvironmentMap.exists (fun k _ -> String.equal id k) env then
      raise (TypeCheckError ("Struct:" ^ string_of_int i ^ " name is already taken!"))
    else
      let sdef = sdef |> TypeEnvironmentMap.add id (List.map (fun ((tid, t): string * struct_types) -> (tid, match t with
        | Num -> Num
        | Bool -> Bool
        | LocStruct(name) -> if String.equal id name || TypeEnvironmentMap.exists (fun k _ -> String.equal k name) sdef then Loc(name) else raise (TypeCheckError "Struct type does not exists!")
        )) types) in
      let (t, body, tm) = type_check body env sdef tm in
        (t, Struct(i, id, types, body), tm |> TypeASTMap.add i t)
| Malloc(i, id, exprs) ->
    let expected_types = TypeEnvironmentMap.find id sdef in
    let expected_types = List.map (fun (_f, t) -> t) expected_types in
      let (actual_types, exprs, tm) = List.fold_right (
        fun e (actual_types, exprs, tm) -> let (t, e, tm) = type_check e env sdef tm in
          (t :: actual_types, List.append exprs [e], tm |> TypeASTMap.add (get_ast_id e) t)
      ) exprs ([], [], tm) in
      let t = Loc(id) in
        let rec zip = (fun l0 l1 -> match (l0, l1) with
          | (x0 :: xs0, x1 :: xs1) -> (x0, x1) :: zip xs0 xs1
          | ([], []) -> []
          | _ -> raise (TypeCheckError ("Malloc:" ^ string_of_int i ^ " expressions list size does not fit expected type list size. Expected " ^ string_of_int (List.length expected_types) ^ ", but got " ^ string_of_int (List.length actual_types)))
          ) in
        let actual_types = List.fold_right (
          fun (e, a) l ->
            let t = (match (e, a) with
            | (Loc(_), Null) -> e
            | _ -> a
            ) in
            t :: l
          )
          (zip expected_types actual_types) []
        in
          if List.fold_right (fun (e, a) b -> (match (e, a) with (Loc(id_e), Loc(id_a)) -> String.equal id_e id_a | _ -> e == a) && b) (zip expected_types actual_types) true then
            (t, Malloc(i, id, exprs), tm |> TypeASTMap.add i t)
          else
            raise (TypeCheckError ("Malloc:" ^ string_of_int i ^ " the initialising expressions do not fit to the data structure. Expected: {" ^ (List.fold_left (fun s e -> (if String.equal "" s then s else s ^ ", ") ^ types_to_string e) "" expected_types) ^ "}, but got: {" ^ (List.fold_left (fun s e -> (if String.equal "" s then s else s ^ ", ") ^ types_to_string e) "" actual_types) ^ "}"))
| Mfree(i, loc) ->
    let (t, loc, tm) = type_check loc env sdef tm in (match t with
      | Loc(id) -> if TypeEnvironmentMap.exists (fun k _ -> String.equal id k) sdef then
            (Unit, Mfree(i, loc), tm |> TypeASTMap.add i Unit)
          else
            raise (TypeCheckError ("Mfree:" ^ string_of_int i ^ " the struct type does not exist!"))
      | _ -> raise (TypeCheckError ("Mfree:" ^ string_of_int i ^ " requires a location, but got: " ^ types_to_string t))
      )
| Mset(i, loc, field, expr) ->
    let (t, loc, tm) = type_check loc env sdef tm in (match t with
      | Loc(id) ->
          let expected_types = TypeEnvironmentMap.find id sdef in
          let (_f, expected_type) = List.find (fun (f, _) -> String.equal f field) expected_types in
          let (actual_type, expr, tm) = type_check expr env sdef tm in
            if (match (expected_type, actual_type) with
            | (Loc(idl), Loc(idr)) -> String.equal idl idr
            | (Loc(_), Null) -> true (* allow assigning null *)
            | (lhs, rhs) -> lhs == rhs
            ) then
              (Unit, Mset(i, loc, field, expr), tm |> TypeASTMap.add i Unit)
            else
              raise (TypeCheckError ("Mset:" ^ string_of_int i ^ " needs the correct type, according to the field. Expected: " ^ types_to_string expected_type ^ ", but got: " ^ types_to_string actual_type))
      | _ -> raise (TypeCheckError ("Mset:" ^ string_of_int i ^ " requires a location, but got: " ^ types_to_string t))
      )
| Mget(i, loc, field) ->
    let (t, loc, tm) = type_check loc env sdef tm in (match t with
      | Loc(id) ->
          let expected_types = TypeEnvironmentMap.find id sdef in
          let (_f, t) = List.find (fun (f, _) -> String.equal f field) expected_types in
              (t, Mget(i, loc, field), tm |> TypeASTMap.add i t)
      | _ -> raise (TypeCheckError ("Mget:" ^ string_of_int i ^ " requires a location, but got: " ^ types_to_string t))
      )
| While(i, cond, body) ->
    let (t, cond, tm) = type_check cond env sdef tm in
      if t == Bool then
        let (_, body, tm) = type_check body env sdef tm in
          (Unit, While(i, cond, body), tm |> TypeASTMap.add i Unit)
      else
        raise (TypeCheckError ("While:" ^ string_of_int i ^ " requires a bool as condition!"))
| For(i, id, start, end_, body) ->
    let (t, start, tm) = type_check start env sdef tm in
      if t == Num then
        let (t, end_, tm) = type_check end_ env sdef tm in
          if t == Num then
            let env = env |> TypeEnvironmentMap.add id Num in
            let (_, body, tm) = type_check body env sdef tm in
              (Unit, For(i, id, start, end_, body), tm |> TypeASTMap.add i Unit)
          else
            raise (TypeCheckError ("For:" ^ string_of_int i ^ " requires a number as end parameter!"))
      else
        raise (TypeCheckError ("For:" ^ string_of_int i ^ " requires a number as start parameter!"))
| Assert(i, assertion, body) ->
    let (t_body, body, tm2) = type_check body env sdef tm in
    let env = env |> TypeEnvironmentMap.add "result" t_body in
    let (t_assertion, _, _) = type_check assertion env sdef tm in
      (match t_assertion with
      | Bool -> ()
      | _ -> raise (TypeCheckError ("Assert:" ^ string_of_int i ^ " requires a bool expression as assertion!"))
      );
      (t_body, body, tm2)
(*| _ -> raise (TypeCheckError "TODO: implement all cases")*)
