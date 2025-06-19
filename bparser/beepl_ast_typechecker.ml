open Beepl_ast

exception TypeError of string

module Env = Map.Make(String)
type tyenv = typ Env.t

let list_to_env (xs : (string * typ) list) : tyenv =
  List.fold_left (fun acc (x, ty) -> Env.add x ty acc) Env.empty xs
let ptype_eq p1 p2 =
  match p1, p2 with
  | Tbool, Tbool -> true
  | Tuint8, Tuint8 -> true
  | Tint8, Tint8 -> true
  | Tuint16, Tuint16 -> true
  | Tint16, Tint16 -> true
  | Tuint32, Tuint32 -> true
  | Tint32, Tint32 -> true
  | Tulong, Tulong -> true
  | Tlong, Tlong -> true
  | _ -> false

let typ_eq t1 t2 =
  match t1, t2 with
  | Utype, Utype -> true
  | Vtype p1, Vtype p2 -> ptype_eq p1 p2
  | _, _ -> false

let rec infer_expr (env : tyenv) (e : expr) : typ =
  match e with
  | Var x ->
      (match Env.find_opt x env with
       | Some ty -> ty
       | None -> raise (TypeError ("Unbound variable: " ^ x)))
  | Const c ->
      (match c with
       | Cunit -> Utype
       | Cbool _ -> Vtype Tbool
       | Cint32 _ -> Vtype Tint32
       | Clong _ -> Vtype Tlong)
  | Let (x, ty_ann, e1, e2) ->
      let ty1 = infer_expr env e1 in
      if not (typ_eq ty1 ty_ann) then
        raise (TypeError ("Let-binding type mismatch for " ^ x));
      let env' = Env.add x ty1 env in
      infer_expr env' e2
  | If (e1, e2, e3) ->
      let t1 = infer_expr env e1 in
      if not (typ_eq t1 (Vtype Tbool)) then
        raise (TypeError "If condition must be bool");
      let t2 = infer_expr env e2 in
      let t3 = infer_expr env e3 in
      if not (typ_eq t2 t3) then
        raise (TypeError "If branches have mismatched types");
      t2

let infer_fundecl (Tfundecl (_name, ret_type, _eff, args, _vars, body)) : (string * typ) list =
  let env =
    List.fold_left (fun acc (x, ty) -> Env.add x ty acc) Env.empty args
  in
  let inferred_type = infer_expr env body in
  if not (typ_eq inferred_type ret_type) then
    raise (TypeError "Return type mismatch");

  Env.bindings env

let infer_program (prog : program) =
  List.iter
    (function
      | Internal f -> ignore (infer_fundecl f)
      | EBPFInternal f -> ignore (infer_fundecl f)
    ) prog
