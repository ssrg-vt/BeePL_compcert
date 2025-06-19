open Beepl_ast
open Beepl_parser
open Beepl_lexer
open Lexing
open Beepl_ast_typechecker

let coq_list (elems : string list) : string =
  match elems with
  | [] -> "nil"
  | _ -> String.concat " :: " elems ^ " :: nil"

  (* Extract all used identifiers from the program *)
let collect_idents (prog : program) : string list =
  let add_var acc (x, _) = if List.mem x acc then acc else x :: acc in
  let rec from_expr acc e =
    match e with
    | Var x -> if List.mem x acc then acc else x :: acc
    | Const _ -> acc
    | Let (x, _, e1, e2) -> from_expr (from_expr (if List.mem x acc then acc else x :: acc) e1) e2
    | If (e1, e2, e3) -> List.fold_left from_expr acc [e1; e2; e3]
  in
  List.fold_left (fun acc top ->
    match top with
    | Internal (Tfundecl (name, _, _, args, _, body))
    | EBPFInternal (Tfundecl (name, _, _, args, _, body)) ->
        let acc = if List.mem name acc then acc else name :: acc in
        let acc = List.fold_left add_var acc args in
        from_expr acc body
  ) [] prog

(* Generate Coq identifier declarations *)
let coq_idents (idents : string list) : string =
  let defs =
    List.map (fun id -> Printf.sprintf "Definition _%s : ident := $\"%s\"." id id) idents
  in
  let table =
    let entries = List.map (fun id -> Printf.sprintf "(_%s, \"%s\")" id id) idents in
    "Definition ident_to_string := " ^ "(" ^ String.concat " :: " entries ^ " :: nil)."
  in
  String.concat "\n" (defs @ [table])

(* Check if any function is EBPF *)
let contains_ebpf prog =
  List.exists (function EBPFInternal _ -> true | _ -> false) prog

(* Final Coq header + idents *)
let generate_coq_prelude prog =
  let header = {|
Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker.
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.
|} in
  let idents = collect_idents prog in
  let defs = coq_idents idents in
  let dattr_def =
    if contains_ebpf prog then
      "Definition dattr := {| attr_volatile := false; attr_alignas := None |}.\n"
    else ""
  in
  header ^ "\n\n" ^ dattr_def ^ defs ^ "\n\n"

let typ_to_coq (t : typ) : string =
  match t with
  | Utype -> "Utype"
  | Vtype Tuint8 -> "Vtype (BeeTypes.Tuint8 Unsigned dattr)"
  | Vtype Tint8 -> "Vtype (BeeTypes.Tint I8 Unsigned dattr)"
  | Vtype Tuint16 -> "Vtype (BeeTypes.Tuint I16 Unsigned dattr)"
  | Vtype Tint16 -> "Vtype (BeeTypes.Tint I16 Unsigned dattr)"
  | Vtype Tuint32 -> "Vtype (BeeTypes.Tuint I32 Unsigned dattr)"
  | Vtype Tint32 -> "Vtype (BeeTypes.Tint I32 Unsigned dattr)"
  | Vtype Tulong -> "Vtype (BeeTypes.Tulong Unsigned dattr)"
  | Vtype Tbool -> "Vtype Tbool"
  | Vtype Tlong -> "Vtype Tlong"

let effect_to_coq (eff : effect) : string =
  match eff with
  | Read s -> Printf.sprintf "Read \"%s\"" s
  | Write s -> Printf.sprintf "Write \"%s\"" s
  | Alloc s -> Printf.sprintf "Alloc \"%s\"" s
  | Io -> "Io"
  | Divergence -> "Divergence"

let rec effect_to_coq_list (effs : effect list) : string =
  match effs with
  | [] -> "nil"
  | eff :: rest ->
    Printf.sprintf "%s :: %s" (effect_to_coq eff) (effect_to_coq_list rest)

let arg_to_coq (id, t) =
  Printf.sprintf "(_%s, %s)" id (typ_to_coq t)

let const_to_coq c =
  match c with
  | Cunit -> "ConsUnit"
  | Cbool b -> Printf.sprintf "(ConsBool %b)" b
  | Cint32 i -> Printf.sprintf "(ConsInt (Int.repr %ld))" i
  | Clong l -> Printf.sprintf "(ConsLong (Int64.repr %Ld))" l

  let rec expr_to_coq (env : (string * typ) list) (e : expr) : string =
    match e with
    | Var id ->
        let ty = List.assoc id env in
        Printf.sprintf "Var _%s (%s)" id (typ_to_coq ty)
    | Const c ->
        let ty = typ_to_coq (infer_expr (list_to_env env) e) in
        Printf.sprintf "Const %s (%s)" (const_to_coq c) ty
    | Let (id, t, e1, e2) ->
        let e1_str = expr_to_coq env e1 in
        let env' = (id, t) :: env in
        let e2_str = expr_to_coq env' e2 in
        let ty2 = typ_to_coq (infer_expr (list_to_env env') e2) in
        Printf.sprintf 
        "Bind _%s (%s)\n                  %s\n                  %s\n                  %s"
          id (typ_to_coq t) e1_str e2_str ty2
    | If (e1, e2, e3) ->
        let ty2 = typ_to_coq (infer_expr (list_to_env env) e2) in
        Printf.sprintf "Cond %s %s %s %s"
          (expr_to_coq env e1)
          (expr_to_coq env e2)
          (expr_to_coq env e3)
          ty2

  
  

let transform_function (Tfundecl (name, ret, eff, args, vars, body)) is_ebpf =
  let env = infer_fundecl (Tfundecl (name, ret, eff, args, vars, body)) in
  let arg_strs = List.map arg_to_coq args in
  let var_strs = List.map arg_to_coq (collect_vars body) in
  let coq_name = "f_" ^ name in
  let body_str = expr_to_coq env body in
  Printf.sprintf
    "Definition %s : BeePL.function := {| \n  fn_return := %s;\n  fn_effect := %s;\n  fn_callconv := cc_default;\n  fn_args := %s;\n  fn_vars := %s;\n  fn_body := %s;\n  is_ebpf := %s\n|}.\n"
    coq_name
    (typ_to_coq ret)
    (effect_to_coq_list eff)
    (coq_list arg_strs)
    (coq_list var_strs)
    body_str
    (if is_ebpf then "true" else "false")

let transform_toplevel = function
  | Internal f -> transform_function f false
  | EBPFInternal f -> transform_function f true

let transform_program (prog : program) =
    let coq_header = generate_coq_prelude prog in
    coq_header ^ String.concat "\n\n" (List.map transform_toplevel prog)

let parse_file (filename : string) : program =
  let ch = open_in filename in
  let lexbuf = from_channel ch in
  try
    let result = prog read_token lexbuf in
    close_in ch;
    result
  with
  | SyntaxError msg ->
    let pos = lexbuf.lex_curr_p in
    Printf.eprintf "%s:%d:%d: %s\n"
      filename pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) msg;
    exit (-1)
  | Beepl_parser.Error ->
    let pos = lexbuf.lex_curr_p in
    Printf.eprintf "%s:%d:%d: Parse error near token '%s'\n"
      filename pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
      (Lexing.lexeme lexbuf);
    exit (-1)

let parse_and_transform_bpl (filename : string) : string =
  let program = parse_file filename in
  transform_program program
