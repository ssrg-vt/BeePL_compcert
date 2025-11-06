open Beepl_ast
open Beepl_parser
open Beepl_lexer
open Lexing
open Beepl_ast_typechecker
[@@@ocaml.warning "-32"]

let extern_bindings_of_efenv (ee : Beepl_ast_typechecker.efenv) : (string * typ) list =
  Beepl_ast_typechecker.Env.bindings ee
  |> List.map (fun (name, info) ->
       (name, Ftype (info.formals, info.effects, info.ret)))

(* Build struct environment from the program *)
let build_senv (prog : program) : Beepl_ast_typechecker.Senv.t =
  List.fold_left
    (fun acc -> function
      | StructDecl (name, fields) ->
          Beepl_ast_typechecker.Senv.add name fields acc
      | _ -> acc)
    Beepl_ast_typechecker.Senv.empty
    prog
let export_coq_list (elems : string list) : string =
  match elems with
  | [] -> "nil"
  | _ -> String.concat " :: " elems ^ " :: nil"

let string_constant_counter = ref 0
let string_global_table = Beepl_transformer.string_globals

let string_to_id : (string, string) Hashtbl.t = Hashtbl.create 17

let lift_string_constant (s : string) : string =
  match Hashtbl.find_opt string_to_id s with
  | Some id -> id
  | None ->
      let id = "___stringlit_" ^ string_of_int (Hashtbl.length string_to_id) in
      Hashtbl.add string_to_id s id;
      Hashtbl.add string_global_table id s;   (* keep id -> string for globals emission *)
      id
    
let export_collect_idents (prog : program) : string list  =
let add_var acc (x, _) = if List.mem x acc then acc else x :: acc in
let rec from_expr acc e =
  match e with
  | Var x -> if List.mem x acc then acc else x :: acc
  | Const (Cstring s) ->
      let id = lift_string_constant s in
      if List.mem id acc then acc else id :: acc
  | Const _ -> acc
  | Prim (Uop _, args) ->
      List.fold_left from_expr acc args
  | Prim (Bop _, args) ->
      List.fold_left from_expr acc args
  | Prim (Cast _, args) ->
      List.fold_left from_expr acc args
  | Prim (Ref, args) ->
      List.fold_left from_expr acc args
  | Prim (Deref, args) ->
      List.fold_left from_expr acc args
  | Prim (Massgn, args) ->
      List.fold_left from_expr acc args
  | App (e1, args) ->
      let acc = from_expr acc e1 in
      List.fold_left from_expr acc args
  | Let (x, _, e1, e2) ->
      from_expr (from_expr (if List.mem x acc then acc else x :: acc) e1) e2
  | If (e1, e2, e3) ->
      List.fold_left from_expr acc [e1; e2; e3]
  | For (e1, e2, _, e3) ->
      List.fold_left from_expr acc [e1; e2; e3]
  | Sinit (_, _, args) ->
      List.fold_left from_expr acc args
  | Fget (e, _) ->
      from_expr acc e
  | Ainit (arr, args) ->
    if List.mem arr acc 
    then List.fold_left from_expr acc args
    else arr :: List.fold_left from_expr acc args
  | Aaccess (arr, _) ->
      if List.mem arr acc then acc else arr :: acc
  | Match (e, patterns, exprs) ->
      let acc = from_expr acc e in
      let acc = List.fold_left (fun a p ->
        match p with
        | Psome x -> if List.mem x a then a else x :: a
        | Pnone -> a
        | Pbytes (id, _, fields) ->
            let a = if List.mem id a then a else id :: a in
            List.fold_left add_var a fields
      ) acc patterns in
      List.fold_left from_expr acc exprs
  | Esome e1 ->
      from_expr acc e1
  | Enone t -> acc
in
let idents_from_prog =
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
    | GlobalLet (name, _, body, _) ->
        let acc = if List.mem name acc then acc else name :: acc in
        from_expr acc body     
  ) [] prog
in

(* Add all string global keys *)
let string_idents =
  Hashtbl.fold (fun _ id acc ->
  if List.mem id acc then acc else id :: acc
) Beepl_transformer.string_globals []
in

idents_from_prog @ string_idents
    

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
  | Bprim Tint8 -> "BeeTypes.Tint I8 Signed dattr"
  | Bprim Tuint16 -> "BeeTypes.Tuint I16 Unsigned dattr"
  | Bprim Tint16 -> "BeeTypes.Tint I16 Signed dattr"
  | Bprim Tuint32 -> "BeeTypes.Tuint I32 Unsigned dattr"
  | Bprim Tint32 -> "BeeTypes.Tint I32 Signed dattr"
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
  | Vtype Tint8 -> "Vtype (BeeTypes.Tint I8 Signed dattr)"
  | Vtype Tuint16 -> "Vtype (BeeTypes.Tuint I16 Unsigned dattr)"
  | Vtype Tint16 -> "Vtype (BeeTypes.Tint I16 Signed dattr)"
  | Vtype Tuint32 -> "Vtype (BeeTypes.Tuint I32 Unsigned dattr)"
  | Vtype Tint32 -> "Vtype (BeeTypes.Tint I32 Signed dattr)"
  | Vtype Tulong -> "Vtype (BeeTypes.Tulong Unsigned dattr)"
  | Vtype Tbool -> "Vtype Tbool"
  | Vtype Tlong -> "Vtype Tlong"
  | Ptr (Reftype (name, btype)) ->
    Printf.sprintf "Ptrtype (Reftype _%s (%s) noattr)" name (export_btype_to_coq btype)
  | Ptr (Otype pt) ->
    Printf.sprintf "Ptrtype (Otype (%s))" (export_typ_to_coq (Ptr pt))
  | Stype name -> Printf.sprintf "Stype _%s" name
  | Atype (elem_type, size) ->
    Printf.sprintf "Atype (%s) %d" (export_typ_to_coq elem_type) size
  | Ftype (arg_types, effs, ret_type) ->
    let arg_strs = List.map export_typ_to_coq arg_types in
    let eff_strs = export_effect_to_coq_list effs in
    Printf.sprintf "Ftype (%s) (%s) (%s)"
      (export_coq_list arg_strs)
      eff_strs
      (export_typ_to_coq ret_type)
  | Bytes -> "Bytes"

let export_arg_to_coq (id, t) =
  Printf.sprintf "(_%s, %s)" id (export_typ_to_coq t)

(* Helper to export string literal global definitions *)
let export_stringlit_def (id : string) (s : string) : string =
  let bytes = List.init (String.length s) (String.get s) @ ['\000'] in
  let init_values =
    bytes
    |> List.map (fun c -> Printf.sprintf "Init_int8 (Int.repr %d)" (Char.code c))
    |> String.concat " :: " in
  let length = List.length bytes in
  Printf.sprintf
    "Definition v_%s := {|\n  gvar_info := tbarray tint8s %d noattr;\n  gvar_init := %s :: nil;\n  gvar_readonly := true;\n  gvar_volatile := false\n|}." id length init_values

let export_const_to_coq c =
  match c with
  | Cunit -> "ConsUnit"
  | Cbool b -> Printf.sprintf "(ConsBool %b)" b
  | Cint32 i -> Printf.sprintf "(ConsInt (Int.repr %ld))" i
  | Clong l -> Printf.sprintf "(ConsLong (Int64.repr %Ld))" l
  | Cstring s ->
    let id = lift_string_constant s in
    Printf.sprintf "(ConsPtr _%s)" id

let rec export_expr_to_coq (ee : Beepl_ast_typechecker.efenv) (senv : Beepl_ast_typechecker.Senv.t) (env : (string * typ) list) (e : expr) : string =
  match e with
  | Var id ->
      let ty =
        try List.assoc id env
        with Not_found ->
          failwith ("Identifier not found in environment: " ^ id)
      in 
      Printf.sprintf "(Var _%s (%s))" id (export_typ_to_coq ty)
  | Const c -> (match c with
    | Cstring s ->
      let id = lift_string_constant s in
      (* pass as char* : Ptr(Reftype "h", int8) *)
      Printf.sprintf
      "(Const (ConsPtr _%s) (Ptrtype (Reftype _h (BeeTypes.Tint I8 Signed dattr) noattr)))"
      id
    | _ ->
        let ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
        Printf.sprintf "(Const %s (%s))" (export_const_to_coq c) ty)
  | App (e1, args) ->
      let e1_str = export_expr_to_coq ee senv env e1 in
      let args_str = List.map (export_expr_to_coq ee senv env) args in
      let ty1   = export_typ_to_coq (infer_expr ee senv (list_to_env env) (App (e1, args))) in
      Printf.sprintf 
      "(App (%s)\n                  (%s)\n                  (%s))"
        e1_str
        (export_coq_list args_str)
        ty1
  (* Note: The type of the function is inferred from the environment *)
  | Prim (Uop uop, args) ->
      let args_str = List.map (export_expr_to_coq ee senv env) args in
      let ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
      let uop_str = match uop with
        | Onotbool -> "Onotbool"
        | Onotint -> "Onotint"
        | Oneg -> "Oneg"
        | UOverloadTilde -> "UOverloadTilde"
      in
      Printf.sprintf 
      "(Prim (Uop %s)\n                  (%s)\n                  (%s))"
        uop_str
        (export_coq_list args_str)
        ty
  | Prim (Bop bop, args) ->
      let args_str = List.map (export_expr_to_coq ee senv env) args in
      let ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
      let bop_str = match bop with
        | Oadd -> "Oadd"
        | Osub -> "Osub"
        | Omul -> "Omul"
        | Odiv -> "Odiv"
        | Omod -> "Omod"
        | Oand -> "Oand"
        | Oor -> "Oor"
        | Oxor -> "Oxor"
        | Oshl -> "Oshl"
        | Oshr -> "Oshr"
        | Oeq -> "Oeq"
        | One -> "One"
        | Olt -> "Olt"
        | Ogt -> "Ogt"
        | Ole -> "Ole"
        | Oge -> "Oge"
        (* Add other binary operators here as needed *)
      in
      Printf.sprintf 
      "(Prim (Bop %s)\n                  (%s)\n                  (%s))"
        bop_str
        (export_coq_list args_str)
        ty
  | Prim (Cast t, args) ->
      let args_str = List.map (export_expr_to_coq ee senv env) args in
      let ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
      Printf.sprintf 
      "(Prim (Cast %s)\n                  (%s)\n                  (%s))"
        (export_typ_to_coq t)
        (export_coq_list args_str)
        ty
  | Prim (Ref, args) ->
      let args_str = List.map (export_expr_to_coq ee senv env) args in
      let ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
      Printf.sprintf 
      "(Prim (Ref)\n                  (%s)\n                  (%s))"
        (export_coq_list args_str)
        ty
  | Prim (Deref, args) ->
      let args_str = List.map (export_expr_to_coq ee senv env) args in
      let ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
      Printf.sprintf 
      "(Prim (Deref)\n                  (%s)\n                  (%s))"
        (export_coq_list args_str)
        ty
  | Prim (Massgn, args) ->
      let args_str = List.map (export_expr_to_coq ee senv env) args in
      let ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
      Printf.sprintf 
      "(Prim (Massgn)\n                  (%s)\n                  (%s))"
        (export_coq_list args_str)
        ty
  | Let (id, t, e1, e2) ->
      let e1_str = export_expr_to_coq ee senv env e1 in
      let env' = (id, t) :: env in
      let e2_str = export_expr_to_coq ee senv env' e2 in
      let ty2 = export_typ_to_coq (infer_expr ee senv (list_to_env env') e2) in
      Printf.sprintf 
      "(Bind _%s (%s)\n                  %s\n                  %s\n             (%s))"
        id (export_typ_to_coq t) e1_str e2_str ty2
  | If (e1, e2, e3) ->
      let ty2 = export_typ_to_coq (infer_expr ee senv (list_to_env env) e2) in
      Printf.sprintf 
      "(Cond (%s)\n                       (%s)\n                       (%s)\n                  (%s))"
        (export_expr_to_coq ee senv env e1)
        (export_expr_to_coq ee senv env e2)
        (export_expr_to_coq ee senv env e3)
        ty2
  | For (e1, e2, dir, e3) ->
      let dir_str = match dir with Up -> "Up" | Down -> "Down" in
      let ty3 = export_typ_to_coq (infer_expr ee senv (list_to_env env) e3) in
      Printf.sprintf 
      "(For (%s)\n                  (%s)\n                  %s\n                  (%s)\n                  (%s))"
        (export_expr_to_coq ee senv env e1)
        (export_expr_to_coq ee senv env e2)
        dir_str
        (export_expr_to_coq ee senv env e3)
        ty3
  | Sinit (struct_name, fnames, exprs) ->
      let exprs_str = List.map (export_expr_to_coq ee senv env) exprs in
      let ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
      Printf.sprintf 
      "(Sinit _%s (%s)\n                  (%s)\n                  (%s))"
        struct_name
        (export_coq_list (List.map (fun f -> Printf.sprintf "_%s" f) fnames))
        (export_coq_list exprs_str)
        ty
  | Fget (e, field_name) ->
      let ret_ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
      Printf.sprintf 
      "(Fget (%s)\n                  _%s\n                  (%s))"
        (export_expr_to_coq ee senv env e)
        field_name
        ret_ty
  | Ainit (arr, args) ->
      let args_str = List.map (export_expr_to_coq ee senv env) args in
      let ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
      Printf.sprintf 
      "(Ainit (%s)\n                  _%s\n                  %s\n                  (%s))"
        arr 
        ty
        (export_coq_list args_str)
        ty
  | Aaccess (arr, n) ->
      let ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
      let t = match List.assoc arr env with
              | Atype (elem_type, _) -> elem_type
              | _ -> failwith ("Expected array type for Aaccess, got different type for " ^ arr) in 
      Printf.sprintf 
      "(Aaccess (%s)\n                  _%s\n                  %d\n                  (%s))"
        arr 
        (export_typ_to_coq t)
        n
        ty 
  | Match (e, patterns, exprs) ->
      let patterns_str = List.map (function
        | Psome id -> Printf.sprintf "Psome _%s" id
        | Pnone -> "Pnone"
        | Pbytes (id, t, fields) ->
            let field_strs = List.map (fun (fid, fty) -> Printf.sprintf "(_%s, %s)" fid (export_typ_to_coq fty)) fields in
            Printf.sprintf "Pbytes (_%s) (%s) (%s)" id (export_typ_to_coq t) (export_coq_list field_strs)
      ) patterns in
      let exprs_str = List.map (export_expr_to_coq ee senv env) exprs in
      let ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
      Printf.sprintf 
      "(Match (%s)\n                  (%s)\n                  (%s)\n                  (%s))"
        (export_expr_to_coq ee senv env e)
        (export_coq_list patterns_str)
        (export_coq_list exprs_str)
        ty
  (* e : Beepl_ast.expr is the whole node you’re exporting *)

| Esome e1 ->
  (* 1) infer the child’s type *)
  let child_ty = Beepl_ast_typechecker.infer_expr ee senv (list_to_env env) e1 in
  (* 2) it must be a plain pointer; wrap it into an option-pointer for the node type *)
  (match child_ty with
   | Ptr pt ->
       let opt_ty = Ptr (Otype pt) in
       Printf.sprintf
         "(Esome (%s)\n         (%s))"
         (export_expr_to_coq ee senv env e1)
         (export_typ_to_coq opt_ty)
   | _ ->
       failwith "Esome expects its argument to be a pointer (Ptr _).")

| Enone ty ->
  (match ty with
   | Ptr (Otype _) ->
       Printf.sprintf "(Enone (%s))" (export_typ_to_coq ty)
   | _ ->
       failwith "Enone must have an option-pointer type (Ptr (Otype _)).")

 (* | Esome e1 ->
      let ty = export_typ_to_coq (infer_expr senv (list_to_env env) e) in
      Printf.sprintf 
      "(Esome (%s)\n                  (%s))"
        (export_expr_to_coq senv env e1)
        ty
  | Enone ->
      let ty = export_typ_to_coq (infer_expr senv (list_to_env env) e) in
      Printf.sprintf 
      "(Enone (%s))"
        ty*)

let export_transform_function ee senv globals (Tfundecl (name, ret, eff, args, vars, body)) is_ebpf =
  let env = args @ vars @ globals in (* Build (string * typ) list environment *)
  let arg_strs = List.map export_arg_to_coq args in
  let var_strs = List.map export_arg_to_coq (collect_vars body) in
  let coq_name = "f_" ^ name in
  let body_str = export_expr_to_coq ee senv env body in
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

let export_cc_of_efinfo (variadic : bool) (fixed_arity : int) : string =
  if variadic then
    Printf.sprintf
      "{| cc_vararg := Some (Z.of_nat %d); cc_unproto := false; cc_structret := false |}"
      fixed_arity
  else
    "{| cc_vararg := None; cc_unproto := false; cc_structret := false |}"
  
  let export_bsig_of_external (formals : typ list) (effects : effect list) (ret : typ) (variadic : bool) : string =
    let args = List.map export_typ_to_coq formals |> export_coq_list in
    let res  = export_typ_to_coq ret in
    let ef   = export_effect_to_coq_list effects in
    let cc   = export_cc_of_efinfo variadic (List.length formals) in
    Printf.sprintf
      "{| bsig_args := %s; bsig_ef := %s; bsig_res := %s; bsig_cc := %s |}"
      args ef res cc
  
  (* Produce (Coq definitions, entries to splice into global_definitions) *)
  let export_coq_external_globdefs (ee : Beepl_ast_typechecker.efenv) : string list * string list =
    Beepl_ast_typechecker.Env.bindings ee
    |> List.map (fun (name, info) ->
         let bsig  = export_bsig_of_external info.formals info.effects info.ret info.variadic in
         let coq_name = "ext_" ^ name in
         let def =
           Printf.sprintf
             "Definition %s : AST.globdef BeePL.fundef type :=\n\
              AST.Gfun (BeePL.External (BeePL.EF_external \"%s\" %s)\n\
              \                          (bsig_args %s) (bsig_res %s) (bsig_cc %s))."
             coq_name name bsig coq_name coq_name coq_name
         in
         let entry = Printf.sprintf "(_%s, %s, None)" name coq_name in
         (def, entry))
    |> List.split
  
    
let export_coq_globals prog ext_entries =
  let clean_section s =
    let prefix = "#section " in
    if export_starts_with ~prefix s then
      String.sub s (String.length prefix) (String.length s - String.length prefix)
    else s
  in
  let fun_and_global_entries =
    List.filter_map (function
      | Internal (Tfundecl (name, _, _, _, _, _), section)
      | EBPFInternal (Tfundecl (name, _, _, _, _, _), section) ->
          let sec_str = match section with
            | Some s -> Printf.sprintf "Some \"%s\"" (clean_section s)
            | None -> "None"
          in
          Some (Printf.sprintf "(_%s, AST.Gfun (BeePL.Internal f_%s), %s)" name name sec_str)
      | GlobalLet (name, _, _, section) ->
        let sec_str = match section with
            | Some s -> Printf.sprintf "Some \"%s\"" (clean_section s)
            | None -> "None"
          in
          Some (Printf.sprintf "(_%s, AST.Gvar v_%s, %s)" name name sec_str)
      | _ -> None) prog
  in
  let string_entries =
    Hashtbl.fold (fun id _ acc ->
      let def = Printf.sprintf "(_%s, AST.Gvar v_%s, None)" id id in
      def :: acc) Beepl_transformer.string_globals []
  in
  let entries = ext_entries @ string_entries @ fun_and_global_entries in
  if entries = [] then ""
  else "Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) :=\n  "
        ^ String.concat " ::\n  " entries ^ " :: nil.\n"
    
    
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
                      
let export_transform_toplevel ~ee ~senv ~globals = function
| Internal(f, _) -> export_transform_function ee senv globals f false
| EBPFInternal(f, _) -> export_transform_function ee senv globals f true
| StructDecl (name, fields) -> export_transform_struct name fields
| GlobalLet (name, t, e, _) ->
    let env = globals in
    let body_str = export_expr_to_coq ee senv env e in
    Printf.sprintf
      "Definition v_%s :=\n {| gtype := %s\n; gvalue := %s\n; gattr := noattr |}.\n"
      name (export_typ_to_coq t) body_str
      

let coq_bcomposite_correct_lemma = {|
Lemma bcomposite_correct : wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed. |}
  
let export_collect_globals (prog : program) : (string * typ) list =
  List.filter_map (function
    | GlobalLet (name, t, _, _) -> Some (name, t)
    | _ -> None
  ) prog

  let export_transform_program prog =
    let coq_header = generate_coq_prelude prog in
    let senv       = build_senv prog in
    let ee         = Beepl_ast_typechecker.build_efenv () in
  
    (* extern EF defs + entries *)
    let ext_defs, ext_entries = export_coq_external_globdefs ee in
  
    let externs    = extern_bindings_of_efenv ee in
    let global_env = externs @ export_collect_globals prog in
  
    let defs = List.map (export_transform_toplevel ~ee ~senv ~globals:global_env) prog in
    let stringlit_defs =
      Hashtbl.fold (fun id s acc -> export_stringlit_def id s :: acc) string_global_table [] in
  
    (* include extern DEFs here *)
    let defs = stringlit_defs @ ext_defs @ defs in
  
    (* pass extern ENTRIES to globals table *)
    let globals = export_coq_globals prog ext_entries in
  
    let publics = export_coq_public_idents prog in
    let entry   = export_find_main_or_fallback prog in
    let wrapper = export_coq_program_wrapper ~name:"bprogram" entry in
    coq_header ^ String.concat "\n\n" defs ^ "\n\n" ^ globals ^ "\n" ^ publics
    ^ "\n" ^ coq_bcomposite_correct_lemma ^ "\n\n" ^ wrapper
  
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

