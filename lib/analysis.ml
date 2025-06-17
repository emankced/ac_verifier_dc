open Ast

(** Map that holds the environment store *)
module TypeEnvironmentMap = Map.Make(String)

(** Map that holds the heap store *)
module TypeHeapMap = Map.Make(Int)

type types =
| Null
| Loc of string * int
| Num
| Bool
| Unit
| Unknown

(** Type of the environment map *)
type type_environment = (types TypeEnvironmentMap.t)

(** Type of the struct definition map *)
type struct_type_definitions = (types list TypeEnvironmentMap.t)

(** Exception used by the type checker *)
exception TypeCheckError of string

let type_check_id = "type"
let get_type_id (t: types) : string = match t with
| Null -> "Null"
| Loc(id, offset) -> "Loc(" ^ id ^ ", " ^ string_of_int offset ^ ")"
| Num -> "Num"
| Bool -> "Bool"
| Unit -> "Unit"
| Unknown -> "Unknown"

let rec type_check (annotation: Ast.expression) (env: type_environment) (sdef: struct_type_definitions) : types * Ast.expression = match annotation with
| Annotation(notes, expr) ->
  (match expr with
  | Null -> (Null, Annotation((type_check_id, get_type_id Null) :: notes, expr))
  | Num(_) -> (Num, Annotation((type_check_id, get_type_id Num) :: notes, expr))
  | Bool(_) -> (Bool, Annotation((type_check_id, get_type_id Bool) :: notes, expr))
  | Unit -> (Unit, Annotation((type_check_id, get_type_id Unit) :: notes, expr))
  | BinOp(op, lhs, rhs) ->
      let (lhs, lhs_expr) = type_check lhs env sdef in
        let (rhs, rhs_expr) = type_check rhs env sdef in
          let t = (match (op, lhs, rhs) with
          | (Add, Num, Num) -> Num
          | (Sub, Num, Num) -> Num
          | (Mul, Num, Num) -> Num
          | (Div, Num, Num) -> Num
          (*TODO offset tracking with static number evaluation*)
          | (Add, Loc(_id, _offset), Num) -> Unknown
          | (Sub, Loc(_id, _offset), Num) -> Unknown
          | (Add, Num, Loc(_id, _offset)) -> Unknown
          | (Sub, Num, Loc(_id, _offset)) -> Unknown
          | (Eq, Num, Num) -> Bool
          | (Ne, Num, Num) -> Bool
          | (Eq, Bool, Bool) -> Bool
          | (Ne, Bool, Bool) -> Bool
          | (Eq, Loc(_), Loc(_)) -> Bool
          | (Ne, Loc(_), Loc(_)) -> Bool
          (* should unit get a comparison definition? *)
          | (Le, Num, Num) -> Bool
          | (Lt, Num, Num) -> Bool
          | (Ge, Num, Num) -> Bool
          | (Gt, Num, Num) -> Bool
          | (And, Bool, Bool) -> Bool
          | (Or, Bool, Bool) -> Bool
          | _ -> raise (TypeCheckError "BinOp: Operator and operands do not match!")
          ) in (t, Annotation((type_check_id, get_type_id t) :: notes, BinOp(op, lhs_expr, rhs_expr)))
  | Id(id) -> let t = env |> TypeEnvironmentMap.find id in (t, Annotation((type_check_id, get_type_id t) :: notes, expr))
  | Let(id, bound, body) ->
      let (bound, bound_expr) = type_check bound env sdef in
        let env = env |> TypeEnvironmentMap.add id bound in
          let (body, body_expr) = type_check body env sdef in
            (body, Annotation((type_check_id, get_type_id body) :: notes, Let(id, bound_expr, body_expr)))
  | Cond(cond, then_body, else_body) ->
    (match (type_check cond env sdef, type_check then_body env sdef, type_check else_body env sdef) with
    | ((Bool, cond), (lhs, then_body), (rhs, else_body)) -> if lhs == rhs then (lhs, Annotation((type_check_id, get_type_id lhs) :: notes, Cond(cond, then_body, else_body))) else raise (TypeCheckError "Cond requires both branches to have the same type!")
    | _ -> raise (TypeCheckError "Cond requires a bool as condition!")
    )
  | Seq(expr0, expr1) ->
      let (_, expr0) = type_check expr0 env sdef in
        let (t, expr1) = type_check expr1 env sdef in
          (t, Annotation((type_check_id, get_type_id t) :: notes, Seq(expr0, expr1)))
  | Struct(id, types, body) ->
      if TypeEnvironmentMap.exists (fun k _ -> String.equal id k) sdef || TypeEnvironmentMap.exists (fun k _ -> String.equal id k) env then
        raise (TypeCheckError "Struct name is already taken!")
      else
        let sdef = sdef |> TypeEnvironmentMap.add id (List.map (fun (t: struct_types) -> match t with
          | Num -> Num
          | Bool -> Bool
          | LocStruct(name) -> if String.equal id name || TypeEnvironmentMap.exists (fun k _ -> String.equal k name) sdef then Loc(name, 0) else raise (TypeCheckError "Struct type does not exists!")
          ) types) in
        let (t, body) = type_check body env sdef in
          (t, Annotation((type_check_id, get_type_id t) :: notes, Struct(id, types, body)))
  | Malloc(id, exprs) ->
      let expected_types = TypeEnvironmentMap.find id sdef in
        let actual_types = List.map (fun e -> let (t, _) = type_check e env sdef in t) exprs in
        let exprs = List.map (fun e -> let (_, e) = type_check e env sdef in e) exprs in
        let t = Loc(id, 0) in
          let rec zip = (fun l0 l1 -> match (l0, l1) with
            | (x0 :: xs0, x1 :: xs1) -> (x0, x1) :: zip xs0 xs1
            | ([], []) -> []
            | _ -> raise (TypeCheckError "Expressions list size does not fit expected type list size!")
            ) in
            if List.fold_right (fun (e, a) b -> e == a && b) (zip expected_types actual_types) true then
              (t, Annotation((type_check_id, get_type_id t) :: notes, Malloc(id, exprs)))
            else
              raise (TypeCheckError "The initialising expressions do not fit to the data structure!")
  | Mfree(loc) ->
      let (t, loc) = type_check loc env sdef in (match t with
        | Loc(id, 0) -> if TypeEnvironmentMap.exists (fun k _ -> String.equal id k) sdef then
              (Unit, Annotation((type_check_id, get_type_id Unit) :: notes, Mfree(loc)))
            else
              raise (TypeCheckError "The struct type does not exist!")
        | _ -> raise (TypeCheckError "Mfree requires a location!")
        )
  | Mset(loc, expr) ->
      let (t, loc) = type_check loc env sdef in (match t with
        | Loc(id, offset) ->
            let expected_types = TypeEnvironmentMap.find id sdef in
            let expected_type = List.nth expected_types offset in
            let (actual_type, expr) = type_check expr env sdef in
              if expected_type == actual_type then
                (Unit, Annotation((type_check_id, get_type_id Unit) :: notes, Mset(loc, expr)))
              else
                raise (TypeCheckError "Mset needs the correct type, according to the offset!")
        | _ -> raise (TypeCheckError "Mset requires a location!")
        )
  | Mget(loc) ->
      let (t, loc) = type_check loc env sdef in (match t with
        | Loc(id, offset) ->
            let expected_types = TypeEnvironmentMap.find id sdef in
            let t = List.nth expected_types offset in
                (t, Annotation((type_check_id, get_type_id t) :: notes, Mget(loc)))
        | _ -> raise (TypeCheckError "Mset requires a location!")
        )
  | While(cond, body) ->
      let (t, cond) = type_check cond env sdef in
        if t == Bool then
          let (_, body) = type_check body env sdef in
            (Unit, Annotation((type_check_id, get_type_id Unit) :: notes, While(cond, body)))
        else
          raise (TypeCheckError "While requires a bool as condition!")
  | For(id, start, end_, body) ->
      let (t, start) = type_check start env sdef in
        if t == Num then
          let (t, end_) = type_check end_ env sdef in
            if t == Num then
              let env = env |> TypeEnvironmentMap.add id Num in
              let (_, body) = type_check body env sdef in
                (Unit, Annotation((type_check_id, get_type_id Unit) :: notes, For(id, start, end_, body)))
            else
              raise (TypeCheckError "For requires a number as end parameter!")
        else
          raise (TypeCheckError "For requires a number as start parameter!")
  | _ -> raise (TypeCheckError "TODO: implement all cases")
  )
| _ -> raise (TypeCheckError "Expected Annotation node!")

(** Exception used by the annotation preparation *)
exception PrepareAnnotationException of string

(** Wraps every AST node with an Annotation node *)
let rec prepare_annotation (expr: Ast.expression) : Ast.expression = match expr with
| Null -> Annotation([], expr)
| Num(_) -> Annotation([], expr)
| Bool(_) -> Annotation([], expr)
| Unit -> Annotation([], expr)
| Let(id, bound, body) -> Annotation([], Let(id, prepare_annotation bound, prepare_annotation body))
| Id(_) -> Annotation([], expr)
| Cond(cond, then_body, else_body) -> Annotation([], Cond(prepare_annotation cond, prepare_annotation then_body, prepare_annotation else_body))
| BinOp(op, lhs, rhs) -> Annotation([], BinOp(op, prepare_annotation lhs, prepare_annotation rhs))
| Seq(expr0, expr1) -> Annotation([], Seq(prepare_annotation expr0, prepare_annotation expr1))
| Struct(id, types, body) -> Annotation([], Struct(id, types, prepare_annotation body))
| Assert(assertion, command) -> Annotation([], Assert(prepare_annotation assertion, prepare_annotation command))
| Malloc(id, exprs) -> Annotation([], Malloc(id, List.map (fun e -> prepare_annotation e) exprs))
| Mfree(loc) -> Annotation([], Mfree(prepare_annotation loc))
| Mset(loc, expr) -> Annotation([], Mset(prepare_annotation loc, prepare_annotation expr))
| Mget(loc) -> Annotation([], Mget(prepare_annotation loc))
| For(id, start, end_, body) -> Annotation([], For(id, prepare_annotation start, prepare_annotation end_, prepare_annotation body))
| While(cond, body) -> Annotation([], While(prepare_annotation cond, prepare_annotation body))
| Annotation(_, _) -> raise (PrepareAnnotationException "This AST already contains Annotation nodes!")
