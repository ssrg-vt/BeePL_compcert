open Beepl_ast
open Beepl_parser
open Beepl_lexer
open Lexing
open Beepl_ast_typechecker

let export_coq_list (elems : string list) : string =
  match elems with
  | [] -> "nil"
  | _ -> String.concat " :: " elems ^ " :: nil"

  (* Extract all used identifiers from the program *)
let export_collect_idents (prog : program) : string list =
  let add_var acc (x, _) = if List.mem x acc then acc else x :: acc in
  let rec from_expr acc e =
    match e with
    | Var x -> if List.mem x acc then acc else x :: acc
    | Const _ -> acc
    | App (e1, args) ->
        let acc = from_expr acc e1 in
        List.fold_left from_expr acc args
    | Let (x, _, e1, e2) -> from_expr (from_expr (if List.mem x acc then acc else x :: acc) e1) e2
    | If (e1, e2, e3) -> List.fold_left from_expr acc [e1; e2; e3]
  in
  List.fold_left (fun acc top ->
    match top with
    | Internal (Tfundecl (name, _, _, args, _, body), _)
    | EBPFInternal (Tfundecl (name, _, _, args, _, body), _) ->
        let acc = if List.mem name acc then acc else name :: acc in
        let acc = List.fold_left add_var acc args in
        from_expr acc body
    | StructDecl (sname, fields) ->
        let acc = if List.mem sname acc then acc else sname :: acc in
        List.fold_left add_var acc fields      
  ) [] prog

(* Generate Coq identifier declarations *)
let export_coq_idents (idents : string list) : string =
  let defs =
    List.map (fun id -> Printf.sprintf "Definition _%s : ident := $\"%s\"." id id) idents
  in
  let table =
    let entries = List.map (fun id -> Printf.sprintf "(_%s, \"%s\")" id id) idents in
    "Definition ident_to_string := " ^ "(" ^ String.concat " :: " entries ^ " :: nil)."
  in
  String.concat "\n" (defs @ [table])

(* Check if any function is EBPF *)
let export_contains_ebpf prog =
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
  let idents = export_collect_idents prog in
  let defs = export_coq_idents idents in
  let dattr_def =
    if export_contains_ebpf prog then
      "Definition dattr := {| attr_volatile := false; attr_alignas := None |}.\n"
    else ""
  in
  header ^ "\n\n" ^ dattr_def ^ defs ^ "\n\n"

let rec export_btype_to_coq (bt : btype) : string =
  match bt with
  | Bprim Tbool -> "BeeTypes.Tbool"
  | Bprim Tuint8 -> "BeeTypes.Tuint8 Unsigned dattr"
  | Bprim Tint8 -> "BeeTypes.Tint I8 Unsigned dattr"
  | Bprim Tuint16 -> "BeeTypes.Tuint I16 Unsigned dattr"
  | Bprim Tint16 -> "BeeTypes.Tint I16 Unsigned dattr"
  | Bprim Tuint32 -> "BeeTypes.Tuint I32 Unsigned dattr"
  | Bprim Tint32 -> "BeeTypes.Tint I32 Unsigned dattr"
  | Bprim Tulong -> "BeeTypes.Tulong Unsigned dattr"
  | Bprim Tlong -> "BeeTypes.Tlong"
  | Bstruct name -> Printf.sprintf "(Bstruct _%s noattr)" name
  | Barray (t, n) ->
    Printf.sprintf "Barray (%s) %d" (export_btype_to_coq (Bprim t)) n


let export_effect_to_coq (eff : effect) : string =
  match eff with
  | Read s -> Printf.sprintf "Read \"%s\"" s
  | Write s -> Printf.sprintf "Write \"%s\"" s
  | Alloc s -> Printf.sprintf "Alloc \"%s\"" s
  | Io -> "Io"
  | Divergence -> "Divergence"

let rec export_effect_to_coq_list (effs : effect list) : string =
  match effs with
  | [] -> "nil"
  | eff :: rest ->
    Printf.sprintf "%s :: %s" (export_effect_to_coq eff) (export_effect_to_coq_list rest)
let rec export_typ_to_coq (t : typ) : string =
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
  | Ptr (Reftype (name, btype)) ->
    Printf.sprintf "Ptrtype (Reftype _%s (%s) noattr)" name (export_btype_to_coq btype)
  | Ftype (arg_types, effs, ret_type) ->
    let arg_strs = List.map export_typ_to_coq arg_types in
    let eff_strs = export_effect_to_coq_list effs in
    Printf.sprintf "Ftype (%s) (%s) (%s)"
      (export_coq_list arg_strs)
      eff_strs
      (export_typ_to_coq ret_type)

let export_arg_to_coq (id, t) =
  Printf.sprintf "(_%s, %s)" id (export_typ_to_coq t)

let export_const_to_coq c =
  match c with
  | Cunit -> "ConsUnit"
  | Cbool b -> Printf.sprintf "(ConsBool %b)" b
  | Cint32 i -> Printf.sprintf "(ConsInt (Int.repr %ld))" i
  | Clong l -> Printf.sprintf "(ConsLong (Int64.repr %Ld))" l

  let rec export_expr_to_coq (env : (string * typ) list) (e : expr) : string =
    match e with
    | Var id ->
        let ty = List.assoc id env in
        Printf.sprintf "(Var _%s (%s))" id (export_typ_to_coq ty)
    | Const c ->
        let ty = export_typ_to_coq (infer_expr (list_to_env env) e) in
        Printf.sprintf "(Const %s (%s))" (export_const_to_coq c) ty
    | App (e1, args) ->
        let e1_str = export_expr_to_coq env e1 in
        let args_str = List.map (export_expr_to_coq env) args in
        let ty1 = export_typ_to_coq (infer_expr (list_to_env env) e1) in
        Printf.sprintf 
        "(App (%s)\n                  (%s)\n                  (%s))"
          e1_str
          (export_coq_list args_str)
          ty1
    (* Note: The type of the function is inferred from the environment *)
    | Let (id, t, e1, e2) ->
        let e1_str = export_expr_to_coq env e1 in
        let env' = (id, t) :: env in
        let e2_str = export_expr_to_coq env' e2 in
        let ty2 = export_typ_to_coq (infer_expr (list_to_env env') e2) in
        Printf.sprintf 
        "(Bind _%s (%s)\n                  %s\n                  %s\n             (%s))"
          id (export_typ_to_coq t) e1_str e2_str ty2
    | If (e1, e2, e3) ->
        let ty2 = export_typ_to_coq (infer_expr (list_to_env env) e2) in
        Printf.sprintf 
        "(Cond (%s)\n                       (%s)\n                       (%s)\n                  (%s))"
          (export_expr_to_coq env e1)
          (export_expr_to_coq env e2)
          (export_expr_to_coq env e3)
          ty2

let export_transform_function (Tfundecl (name, ret, eff, args, vars, body)) is_ebpf =
  let env = args @ vars in (* Build (string * typ) list environment *)
  let arg_strs = List.map export_arg_to_coq args in
  let var_strs = List.map export_arg_to_coq (collect_vars body) in
  let coq_name = "f_" ^ name in
  let body_str = export_expr_to_coq env body in
  Printf.sprintf
    "Definition %s : BeePL.function := {| \n  fn_return := %s;\n  fn_effect := %s;\n  fn_callconv := cc_default;\n  fn_args := %s;\n  fn_vars := %s;\n  fn_body := %s;\n  is_ebpf := %s\n|}.\n"
    coq_name
    (export_typ_to_coq ret)
    (export_effect_to_coq_list eff)
    (export_coq_list arg_strs)
    (export_coq_list var_strs)
    body_str
    (if is_ebpf then "true" else "false")
          

let export_transform_struct (name : string) (fields : (string * typ) list) : string =
  let members = List.map (fun (id, t) -> Printf.sprintf "Member_plain _%s (%s)" id (export_typ_to_coq t)) fields in
  Printf.sprintf
    "Definition bcomposites : list bcomposite_definition :=\n(Bcomposite _%s Struct\n   (%s :: nil)\n   noattr :: nil)." name (String.concat " ::\n    " members)

let export_starts_with ~prefix s =
  let plen = String.length prefix in
  String.length s >= plen && String.sub s 0 plen = prefix
    
let export_coq_globals prog =
      let clean_section s =
        let prefix = "#section " in
        if export_starts_with ~prefix s then String.sub s (String.length prefix) (String.length s - String.length prefix)
        else s
      in
      let entries =
        List.filter_map (function
          | Internal (Tfundecl (name, _, _, _, _, _), section)
          | EBPFInternal (Tfundecl (name, _, _, _, _, _), section) ->
              let sec_str = match section with
                | Some s -> Printf.sprintf "Some \"%s\"" (clean_section s)
                | None -> "None"
              in
              Some (Printf.sprintf "(_%s, AST.Gfun (BeePL.Internal f_%s), %s)" name name sec_str)
          | _ -> None
        ) prog
      in
      if entries = [] then ""
      else "Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) :=\n  " ^
            String.concat " ::\n  " entries ^ " :: nil.\n"
    
    
let export_collect_public_idents prog =
  List.filter_map (function
    | Internal (Tfundecl (name, _, _, _, _, _), _)
    | EBPFInternal (Tfundecl (name, _, _, _, _, _), _) ->
        Some ("_" ^ name)
      | _ -> None
  ) prog

  let export_coq_public_idents prog =
    let idents = export_collect_public_idents prog in
    match idents with
    | [] -> ""
    | _ ->
      Printf.sprintf "Definition public_idents : list ident := (%s :: nil).\n"
        (String.concat " :: " idents)
  
let export_find_main_or_fallback prog : string =
  let is_main name = name = "main" in
  let extract_name = function
    | Internal (Tfundecl (name, _, _, _, _, _), _)
    | EBPFInternal (Tfundecl (name, _, _, _, _, _), _) -> Some name
    | _ -> None in
  let names = List.filter_map extract_name prog in
  match List.find_opt is_main names with
    | Some name -> name
    | None ->
  match names with
    | fn :: _ -> fn
    | [] -> failwith "No function declarations found"
        
let export_coq_program_wrapper ?(name="example1") (entry : string) : string =
  Printf.sprintf
    "Definition %s : BeePL.program := @mkbprogram bcomposites\n\
         \                                        global_definitions\n\
         \                                        public_idents\n\
         \                                        _%s\n\
         \                                        bcomposite_correct\n\
         \                                        ident_to_string.\n"
        name entry
                      

let export_transform_toplevel = function
  | Internal(f, sec) -> export_transform_function f false
  | EBPFInternal(f, sec) -> export_transform_function f true
  | StructDecl (name, fields) -> export_transform_struct name fields

let coq_bcomposite_correct_lemma = {|
Lemma bcomposite_correct : wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed. |}
  
let export_transform_program prog =
  let coq_header = generate_coq_prelude prog in
  let defs = List.map export_transform_toplevel prog in
  let globals = export_coq_globals prog in
  let publics = export_coq_public_idents prog in
  let entry = export_find_main_or_fallback prog in
  let wrapper = export_coq_program_wrapper ~name:"bprogram" entry in
  coq_header ^ String.concat "\n\n" defs ^ "\n\n" ^ globals ^ "\n" ^ publics ^ "\n" ^ coq_bcomposite_correct_lemma ^ "\n\n" ^ wrapper
  
  
let export_parse_file (filename : string) : program =
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

let export_parse_and_transform_bpl (filename : string) : string =
  let program = export_parse_file filename in
  export_transform_program program
