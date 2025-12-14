open Ast
open Common

(** type representation that the type checker uses *)
type types =
| Null
| Loc of string
| Num
| Bool
| Unit
| Unknown

(** [type_environment] maps an identifier to an analyzed type *)
type type_environment = (types StringMap.t)

(** [struct_type_definitions] maps a structure name to a list of field names and their types *)
type struct_type_definitions = ((string * types) list StringMap.t)

(** [ast_types] maps AST ids to the type the AST node returns *)
type ast_types = (types IntMap.t)

(** Exception used by the type checker *)
exception TypeCheckError of string

(**
[types_to_string t] returns a string describing type [t]
@param t type to convert
@returns string of type [t]
*)
let types_to_string (t: types) : string = match t with
| Null -> "Null"
| Loc(id) -> "Loc(" ^ id ^ ")"
| Num -> "Num"
| Bool -> "Bool"
| Unit -> "Unit"
| Unknown -> "Unknown"

(**
[type_check expr env sdef tm res] checks type correctnes of expression [expr] and builds a type map [tm], which maps AST ids to the AST node's return types
@param expr expression to analyze
@param env environment
@param sdef structure definitions
@param tm type map that maps AST ids to the return type of their AST node
@param res previous commands type (this is needed, because assertions do not return something, but pass through the previous result)
@returns the type of expression [expr] and the updated type map [tm]
@raise TypeCheckError may raise [TypeCheckError]
*)
let rec type_check (expr: Ast.expression) (env: type_environment) (sdef: struct_type_definitions) (tm: ast_types) (res: types) : types * ast_types = match expr with
| Num(i, _) -> (Num, tm |> IntMap.add i Num)
| Bool(i, _) -> (Bool, tm |> IntMap.add i Bool)
| Unit(i) -> (Unit, tm |> IntMap.add i Unit)
| BinOp(i, op, lhs, rhs) ->
    let (lhs, tm) = type_check lhs env sdef tm Unit in
      let (rhs, tm) = type_check rhs env sdef tm Unit in
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
        | (Sep, Bool, Bool) -> Bool
        | (_, lhs, rhs) -> raise (TypeCheckError ("BinOp:" ^ string_of_int i ^ " Operator and operands do not match: " ^ types_to_string lhs ^ " and " ^ types_to_string rhs))
        ) in (t, tm |> IntMap.add i t)
| Id(i, id) ->
    (match env |> StringMap.find_opt id with
    | Some(t) -> (t, tm |> IntMap.add i t)
    | None -> raise (TypeCheckError ("Id:" ^ string_of_int i ^ " could not find id \"" ^ id ^ "\""))
    )
| Let(i, id, bound, body) ->
    let (bound, tm) = type_check bound env sdef tm Unit in
      let env = env |> StringMap.add id bound in
        let (body, tm) = type_check body env sdef tm Unit in
          (body, tm |> IntMap.add i body)
| Cond(i, cond, then_body, else_body) ->
  (match (type_check cond env sdef tm Unit) with
  | (Bool, tm) ->
      let (lhs, tm) = type_check then_body env sdef tm Unit in
      let (rhs, tm) = type_check else_body env sdef tm Unit in
      let (t, correct) =
        (match (lhs, rhs) with
        | (Loc(_), Null) -> (lhs, true)
        | (Null, Loc(_)) -> (rhs, true)
        | (Loc(idl), Loc(idr)) -> (lhs, String.equal idl idr)
        | (lhs, rhs) -> (lhs, lhs == rhs))
      in
        if correct then (t, tm |> IntMap.add i t)
        else raise (TypeCheckError ("Cond:" ^ string_of_int i ^ " requires both branches to have the same type!"))
  | _ -> raise (TypeCheckError ("Cond:" ^ string_of_int i ^ " requires a bool as condition!"))
  )
| Seq(i, expr0, expr1) ->
    let (res, tm) = type_check expr0 env sdef tm res in
      let (t, tm) = type_check expr1 env sdef tm res in
        (t, tm |> IntMap.add i t)
| Struct(i, id, types, body) ->
    if StringMap.exists (fun k _ -> String.equal id k) sdef || StringMap.exists (fun k _ -> String.equal id k) env then
      raise (TypeCheckError ("Struct:" ^ string_of_int i ^ " name is already taken!"))
    else
      let sdef = sdef |> StringMap.add id (List.map (fun ((tid, t): string * struct_type) -> (tid, match t with
        | NumT -> Num
        | BoolT -> Bool
        (*| LocStruct(name) -> if String.equal id name || StringMap.exists (fun k _ -> String.equal k name) sdef then Loc(name) else raise (TypeCheckError "Struct type does not exists!")*)
        )) types) in
      let (t, tm) = type_check body env sdef tm res in
        (t, tm |> IntMap.add i t)
| Malloc(i, id, exprs) ->
    let expected_types =
      (match StringMap.find_opt id sdef with
      | Some(t) -> t
      | None -> raise (TypeCheckError ("Malloc:" ^ string_of_int i ^ " could not find structure definition \"" ^ id ^ "\""))
      )
    in
    let expected_types = List.map (fun (_f, t) -> t) expected_types in
      let (actual_types, tm) = List.fold_right (
        fun e (actual_types, tm) -> let (t, tm) = type_check e env sdef tm Unit in
          (t :: actual_types, tm |> IntMap.add (get_ast_id e) t)
      ) exprs ([], tm) in
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
            (t, tm |> IntMap.add i t)
          else
            raise (TypeCheckError ("Malloc:" ^ string_of_int i ^ " the initialising expressions do not fit to the data structure. Expected: {" ^ (List.fold_left (fun s e -> (if String.equal "" s then s else s ^ ", ") ^ types_to_string e) "" expected_types) ^ "}, but got: {" ^ (List.fold_left (fun s e -> (if String.equal "" s then s else s ^ ", ") ^ types_to_string e) "" actual_types) ^ "}"))
| Mfree(i, loc) ->
    let (t, tm) = type_check loc env sdef tm Unit in (match t with
      | Loc(id) -> if StringMap.exists (fun k _ -> String.equal id k) sdef then
            (Unit, tm |> IntMap.add i Unit)
          else
            raise (TypeCheckError ("Mfree:" ^ string_of_int i ^ " the struct type does not exist!"))
      | _ -> raise (TypeCheckError ("Mfree:" ^ string_of_int i ^ " requires a location, but got: " ^ types_to_string t))
      )
| Mset(i, loc, field, expr) ->
    let (t, tm) = type_check loc env sdef tm Unit in (match t with
      | Loc(id) ->
          let expected_types =
            (match StringMap.find_opt id sdef with
            | Some(t) -> t
            | None -> raise (TypeCheckError ("Mset:" ^ string_of_int i ^ " could not find structure definition \"" ^ id ^ "\""))
            )
          in
          let (_f, expected_type) =
            (match List.find_opt (fun (f, _) -> String.equal f field) expected_types with
            | Some(t) -> t
            | None -> raise (TypeCheckError ("Mset:" ^ string_of_int i ^ " could not find field \"" ^ field ^ "\""))
            )
          in
          let (actual_type, tm) = type_check expr env sdef tm Unit in
            if (match (expected_type, actual_type) with
            | (Loc(idl), Loc(idr)) -> String.equal idl idr
            | (Loc(_), Null) -> true (* allow assigning null *)
            | (lhs, rhs) -> lhs == rhs
            ) then
              (Unit, tm |> IntMap.add i Unit)
            else
              raise (TypeCheckError ("Mset:" ^ string_of_int i ^ " needs the correct type, according to the field. Expected: " ^ types_to_string expected_type ^ ", but got: " ^ types_to_string actual_type))
      | _ -> raise (TypeCheckError ("Mset:" ^ string_of_int i ^ " requires a location, but got: " ^ types_to_string t))
      )
| Mget(i, loc, field) ->
    let (t, tm) = type_check loc env sdef tm Unit in (match t with
      | Loc(id) ->
          let expected_types =
            (match StringMap.find_opt id sdef with
            | Some(t) -> t
            | None -> raise (TypeCheckError ("Mget:" ^ string_of_int i ^ " could not find structure definition \"" ^ id ^ "\""))
            )
          in
          let (_f, t) =
            (match List.find_opt (fun (f, _) -> String.equal f field) expected_types with
            | Some(t) -> t
            | None -> raise (TypeCheckError ("Mget:" ^ string_of_int i ^ " could not find field \"" ^ field ^ "\""))
            )
          in
              (t, tm |> IntMap.add i t)
      | _ -> raise (TypeCheckError ("Mget:" ^ string_of_int i ^ " requires a location, but got: " ^ types_to_string t))
      )
| While(i, cond, body) ->
    let (t, tm) = type_check cond env sdef tm Unit in
      if t == Bool then
        let (_, tm) = type_check body env sdef tm Unit in
          (Unit, tm |> IntMap.add i Unit)
      else
        raise (TypeCheckError ("While:" ^ string_of_int i ^ " requires a bool as condition!"))
| For(i, id, start, end_, body) ->
    let (t, tm) = type_check start env sdef tm Unit in
      if t == Num then
        let (t, tm) = type_check end_ env sdef tm Unit in
          if t == Num then
            let env = env |> StringMap.add id Num in
            let (_, tm) = type_check body env sdef tm Unit in
              (Unit, tm |> IntMap.add i Unit)
          else
            raise (TypeCheckError ("For:" ^ string_of_int i ^ " requires a number as end parameter!"))
      else
        raise (TypeCheckError ("For:" ^ string_of_int i ^ " requires a number as start parameter!"))
| Assert(i, assertion) ->
    let env = env |> StringMap.add "result" res in
    let (t_assertion, tm) = type_check assertion env sdef tm Unit in
      (match t_assertion with
      | Bool -> ()
      | _ -> raise (TypeCheckError ("Assert:" ^ string_of_int i ^ " requires a bool expression as assertion!"))
      );
      (res, tm |> IntMap.add i Unit)
| Invariant(i, inv, body) ->
    let env = env |> StringMap.add "result" res in (*TODO: should the invariant have access to result?*)
    let (t_assertion, tm) = type_check inv env sdef tm Unit in
      (match t_assertion with
      | Bool -> ()
      | _ -> raise (TypeCheckError ("Assert:" ^ string_of_int i ^ " requires a bool expression as assertion!"))
      );
      let (res, tm) = type_check body env sdef tm res in
        (res, tm |> IntMap.add i res)
(*| _ -> raise (TypeCheckError "TODO: implement all cases")*)

(**
[bound_variables expr] collects all used bound variable names of the expression [expr]
@param expr expression
@returns set of bound identifiers
*)
let rec bound_variables (expr: expression): StringSet.t = match expr with
| Num(_, _) -> StringSet.empty
| Bool(_, _) -> StringSet.empty
| Unit(_) -> StringSet.empty
| Id(_, id) -> StringSet.add id StringSet.empty
| Let(_, _, bound, body) -> StringSet.union (bound_variables bound) (bound_variables body)
| BinOp(_, _, lhs, rhs) -> StringSet.union (bound_variables lhs) (bound_variables rhs)
| Seq(_, expr0, expr1) -> StringSet.union (bound_variables expr0) (bound_variables expr1)
| Cond(_, cond, then_body, else_body) -> StringSet.union (bound_variables cond) (StringSet.union (bound_variables then_body) (bound_variables else_body))
| Assert(_, assertion) -> StringSet.filter (fun s -> not (String.equal s "result")) (bound_variables assertion)
| Invariant(_, inv, body) -> StringSet.union (StringSet.filter (fun s -> not (String.equal s "result")) (bound_variables inv)) (bound_variables body)
| Struct(_, _, _, body) -> bound_variables body
| Malloc(_, _, exprs) -> List.fold_right (fun e set -> StringSet.union set (bound_variables e)) exprs StringSet.empty
| Mfree(_, loc) -> bound_variables loc
| Mset(_, loc, _field, expr) -> StringSet.union (bound_variables loc) (bound_variables expr)
| Mget(_, loc, _field) -> bound_variables loc
| For(_, _, start, end_, body) -> StringSet.union (bound_variables start) (StringSet.union (bound_variables end_) (bound_variables body))
| While(_, cond, body) -> StringSet.union (bound_variables cond) (bound_variables body)
