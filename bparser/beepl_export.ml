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

(* Local table: id -> string contents, for Coq/BeePL export only *)
let string_global_table : (string, string) Hashtbl.t = Hashtbl.create 17

(* Map: string contents -> id *)
let string_to_id : (string, string) Hashtbl.t = Hashtbl.create 17

let lift_string_constant (s : string) : string =
  match Hashtbl.find_opt string_to_id s with
  | Some id -> id
  | None ->
      let id = "___stringlit_" ^ string_of_int (Hashtbl.length string_to_id) in
      Hashtbl.add string_to_id s id;
      Hashtbl.add string_global_table id s;   (* id -> contents *)
      id

(* Collect all identifiers from the program *)
(* Collect all identifiers from the program AND from the external efenv *)
let export_collect_idents (prog : program) (ee : Beepl_ast_typechecker.efenv) : string list =
  let add_var acc (x, _) =
    if List.mem x acc then acc else x :: acc
  in

  let rec from_expr acc e =
    match e with
    | Var x ->
        if List.mem x acc then acc else x :: acc

    | Const (Cstring s) ->
        (* Allocate/reuse a stable id for this string *)
        let id = lift_string_constant s in
        if List.mem id acc then acc else id :: acc

    | Const _ ->
        acc

    | Prim (Uop _, args)
    | Prim (Bop _, args)
    | Prim (Cast _, args)
    | Prim (Ref, args)
    | Prim (Deref, args)
    | Prim (Massgn, args) ->
        List.fold_left from_expr acc args

    | App (e1, args) ->
        let acc = from_expr acc e1 in
        List.fold_left from_expr acc args

    | Let (x, _, e1, e2) ->
        let acc = if List.mem x acc then acc else x :: acc in
        let acc = from_expr acc e1 in
        from_expr acc e2

    | If (e1, e2, e3) ->
        List.fold_left from_expr acc [e1; e2; e3]

    | For (e1, e2, _, e3) ->
        List.fold_left from_expr acc [e1; e2; e3]

    | Sinit (_, _, args) ->
        List.fold_left from_expr acc args

    | Fget (e, _) ->
        from_expr acc e

    | Ainit (arr, args) ->
        let acc = if List.mem arr acc then acc else arr :: acc in
        List.fold_left from_expr acc args

    | Aaccess (arr, _) ->
        if List.mem arr acc then acc else arr :: acc

    | Match (scrut, patterns, exprs) ->
        let acc = from_expr acc scrut in
        let acc =
          List.fold_left
            (fun a p ->
               match p with
               | Psome x ->
                   if List.mem x a then a else x :: a
               | Pnone ->
                   a
               | Pbytes (id, _, fields) ->
                   let a = if List.mem id a then id :: a else a in
                   List.fold_left add_var a fields)
            acc patterns
        in
        List.fold_left from_expr acc exprs

    | Esome e1 ->
        from_expr acc e1

    | Enone _ ->
        acc
  in

  (* First, collect from the program as before *)
  let from_prog =
    List.fold_left
      (fun acc top ->
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
             from_expr acc body)
      [] prog
  in

  (* Then, add all external helper names from efenv, e.g. "bpf_get_prandom_u32" *)
  let extern_names =
    Beepl_ast_typechecker.Env.bindings ee
    |> List.map fst
  in

  List.fold_left
    (fun acc nm -> if List.mem nm acc then acc else nm :: acc)
    from_prog
    extern_names


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
let generate_coq_prelude (prog : program) (ee : Beepl_ast_typechecker.efenv) =
  let header = {|
Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker.
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.
|} in

  (* collect program + extern identifiers *)
  let idents = export_collect_idents prog ee in

  (* ensure "h" is always present *)
  let idents =
    if List.mem "h" idents then idents else ("h" :: idents)
  in

  (* generate: Definition _xyz : ident := $"xyz". *)
  let ident_defs =
    List.map
      (fun id -> Printf.sprintf "Definition _%s : ident := $\"%s\"." id id)
      idents
  in

  (* build ident_to_string table including _h *)
  let ident_to_string_entries =
    List.map
      (fun id -> Printf.sprintf "(_%s, \"%s\")" id id)
      idents
  in

  let ident_to_string_def =
    "Definition ident_to_string := (" ^
    (String.concat " :: " ident_to_string_entries) ^
    " :: nil)."
  in

  let dattr_def =
    "Definition dattr := {| attr_volatile := false; attr_alignas := None |}.\n"
  in

  header ^ "\n"
  ^ dattr_def ^ "\n"
  ^ (String.concat "\n" ident_defs) ^ "\n"
  ^ ident_to_string_def ^ "\n\n"


(* Your surface primitive type: Tuint8, Tint8, ... Tlong, Tbool *)
let export_prim_to_coq = function
  | Tbool ->
      "BeeTypes.Tbool"
  | Tuint8 ->
      "BeeTypes.Tint I8 Unsigned dattr"
  | Tint8 ->
      "BeeTypes.Tint I8 Signed dattr"
  | Tuint16 ->
      "BeeTypes.Tint I16 Unsigned dattr"
  | Tint16 ->
      "BeeTypes.Tint I16 Signed dattr"
  | Tuint32 ->
      "BeeTypes.Tint I32 Unsigned dattr"
  | Tint32 ->
      "BeeTypes.Tint I32 Signed dattr"
  | Tulong ->
      "BeeTypes.Tlong Unsigned dattr"
  | Tlong ->
      "BeeTypes.Tlong Signed dattr"

let export_btype_to_coq (bt : btype) : string =
  match bt with
  | Bprim p ->
      Printf.sprintf "Bprim (%s)" (export_prim_to_coq p)
  | Bstruct name ->
      Printf.sprintf "Bstruct _%s noattr" name
  | Barray (p, n) ->
      Printf.sprintf
        "Barray (%s) %d noattr"
        (export_prim_to_coq p) n
      


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
let rec export_effect_to_coq_list (effs : effect list) : string =
match effs with
| [] -> "nil"
| eff :: rest ->
    Printf.sprintf "%s :: %s"
      (export_effect_to_coq eff)
      (export_effect_to_coq_list rest)

let rec export_typ_to_coq (t : typ) : string =
match t with
| Utype ->
    "Utype"

(* Vtype of primitive maps to Vtype (Tint ...) or Vtype (Tlong ...) or Tbool *)
| Vtype p ->
    Printf.sprintf "Vtype (%s)" (export_prim_to_coq p)

(* pointer to basic type: Reftype _id (Bprim ...) noattr *)
| Ptr (Reftype (name, btype)) ->
    Printf.sprintf
      "Ptrtype (Reftype _%s (%s) noattr)"
      name (export_btype_to_coq btype)

(* option pointer *)
| Ptr (Otype pt) ->
    Printf.sprintf
      "Ptrtype (Otype (%s))"
      (export_typ_to_coq (Ptr pt))

(* if you ever use function pointers 
| Ptr (Fptype (args, eff, ret)) ->
    let args_s =
      args |> List.map export_typ_to_coq |> export_coq_list
    in
    let eff_s = export_effect_to_coq_list eff in
    let ret_s = export_typ_to_coq ret in
    Printf.sprintf
      "Ptrtype (Fptype (%s) (%s) (%s))"
      args_s eff_s ret_s *)

(* Stype / Atype now carry attr: use noattr *)
| Stype name ->
    Printf.sprintf "Stype _%s noattr" name

| Atype (elem_type, size) ->
    Printf.sprintf
      "Atype (%s) %d noattr"
      (export_typ_to_coq elem_type) size

| Ftype (arg_types, effs, ret_type) ->
    let arg_strs = List.map export_typ_to_coq arg_types in
    let eff_strs = export_effect_to_coq_list effs in
    Printf.sprintf
      "Ftype (%s) (%s) (%s)"
      (export_coq_list arg_strs)
      eff_strs
      (export_typ_to_coq ret_type)

| Bytes ->
    "Bytes"


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

    let rec take n xs =
      match n, xs with
      | 0, _ | _, [] -> []
      | n, x :: xs -> x :: take (n - 1) xs
    
    let rec drop n xs =
      match n, xs with
      | 0, _ -> xs
      | _, [] -> []
      | n, _::tl -> drop (n-1) tl

let coq_ident_var_of_string (s : string) : string =
  if String.length s > 0 && s.[0] = '_' then "__" ^ String.sub s 1 (String.length s - 1)
  else "_" ^ s
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
          let ty1   = infer_expr ee senv (list_to_env env) (App (e1, args)) in
          let e1_str = export_expr_to_coq ee senv env e1 in
        
          (* detect bpf_printk and cast vararg tail to u64 *)
          let args_str =
            match e1 with
            | Var "bpf_printk" ->
                let fixed = List.map (export_expr_to_coq ee senv env) (take 2 args) in
                let tail  =
                  List.map
                    (fun a ->
                       let a_coq = export_expr_to_coq ee senv env a in
                       (* wrap: (Prim (Cast (Vtype Tulong)) [a]) with its resulting type *)
                       Printf.sprintf
                         "(Prim (Cast %s) (%s :: nil) (%s))"
                         (export_typ_to_coq (Vtype Tulong))
                         a_coq
                         (export_typ_to_coq (Vtype Tulong)))
                    (drop 2 args)
                in
                fixed @ tail
            | _ ->
                List.map (export_expr_to_coq ee senv env) args
          in
        
          let ty1_s = export_typ_to_coq ty1 in
          Printf.sprintf "(App (%s)\n                  (%s)\n                  (%s))"
            e1_str (export_coq_list args_str) ty1_s
  (* Note: The type of the function is inferred from the environment *)
  | Prim (Uop uop, args) ->
      let args_str = List.map (export_expr_to_coq ee senv env) args in
      let ty = export_typ_to_coq (infer_expr ee senv (list_to_env env) e) in
      let uop_str = match uop with
        | Onotbool -> "Cop.Onotbool"
        | Onotint -> "Cop.Onotint"
        | Oneg -> "Cop.Oneg"
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
        | Oadd -> "Cop.Oadd"
        | Osub -> "Cop.Osub"
        | Omul -> "Cop.Omul"
        | Odiv -> "Cop.Odiv"
        | Omod -> "Cop.Omod"
        | Oand -> "Cop.Oand"
        | Oor -> "Cop.Oor"
        | Oxor -> "Cop.Oxor"
        | Oshl -> "Cop.Oshl"
        | Oshr -> "Cop.Oshr"
        | Oeq -> "Cop.Oeq"
        | One -> "Cop.One"
        | Olt -> "Cop.Olt"
        | Ogt -> "Cop.Ogt"
        | Ole -> "Cop.Ole"
        | Oge -> "Cop.Oge"
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
        | Fget (e_base, field_name) ->
          (* 1) print base expression *)
          let e_coq = export_expr_to_coq ee senv env e_base in
      
          (* 2) figure out the struct name from the base’s type *)
          let base_ty = infer_expr ee senv (list_to_env env) e_base in
          let struct_name =
            match base_ty with
            | Stype s -> s
            | Ptr (Reftype (_, Bstruct s)) -> s
            | Ptr (Otype (Reftype (_, Bstruct s))) -> s
            | _ ->
                failwith ("export Fget: base is not a struct or ptr-to-struct (got: "
                          ^ Beepl_ast_typechecker.string_of_typ base_ty ^ ")")
          in
      
          (* 3) look up the FIELD type from the struct env (pretty types) *)
          let field_ty_pretty =
            Beepl_ast_typechecker.Senv.find_field struct_name field_name senv
          in
      
          (* 4) export the field type to Coq *)
          let field_ty_coq = export_typ_to_coq field_ty_pretty in
      
          (* 5) print the Coq ident variable for the FIELD name *)
          let field_ident_var = coq_ident_var_of_string field_name in
      
          (* 6) build Coq term: Sfield expects the FIELD IDENT and the FIELD TYPE *)
          Printf.sprintf
            "(Fget (%s)\n        %s\n        (%s))"
            e_coq
            field_ident_var
            field_ty_coq
      
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
  | Match (scrut, patterns, exprs) ->
    (* 1. Export patterns as before *)
    let patterns_str =
      List.map
        (function
          | Psome id ->
              Printf.sprintf "Psome _%s" id
          | Pnone ->
              "Pnone"
          | Pbytes (id, t, fields) ->
              let field_strs =
                List.map
                  (fun (fid, fty) ->
                      Printf.sprintf "(_%s, %s)" fid (export_typ_to_coq fty))
                  fields
              in
              Printf.sprintf
                "Pbytes (_%s) (%s) (%s)"
                id
                (export_typ_to_coq t)
                (export_coq_list field_strs))
        patterns
    in

    (* 2. For each branch, extend env with the variables bound by that pattern *)
    let exprs_str =
      List.map2
        (fun pat branch ->
            let env' =
              match pat with
              | Psome id ->
                  (* If you don’t care about Psome right now, you can leave it as [env].
                    Here we conservatively bind it with the scrutinee's type. *)
                  let scrut_ty = infer_expr ee senv (list_to_env env) scrut in
                  (id, scrut_ty) :: env
              | Pnone ->
                  env
              | Pbytes (id, t, fields) ->
                  (* bytes-binding id : t, and each (fid, fty) from [fields] *)
                  (id, t) :: (fields @ env)
            in
            export_expr_to_coq ee senv env' branch)
        patterns exprs
    in

    (* 3. Type of the whole match expression, not just the scrutinee *)
    let ty =
      export_typ_to_coq
        (infer_expr ee senv (list_to_env env)
            (Match (scrut, patterns, exprs)))
    in

    Printf.sprintf 
      "(Match (%s)\n                  (%s)\n                  (%s)\n                  (%s))"
      (export_expr_to_coq ee senv env scrut)
      (export_coq_list patterns_str)
      (export_coq_list exprs_str)
      ty


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

let export_transform_function ~ee ~senv ~globals (Tfundecl (name, ret, eff, args, vars, body)) is_ebpf =
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
  let members =
    List.map
      (fun (id, t) ->
          Printf.sprintf "Member_plain _%s (%s)" id (export_typ_to_coq t))
      fields
  in
  Printf.sprintf
    "Bcomposite _%s Struct\n   (%s :: nil)\n   noattr"
    name (String.concat " ::\n    " members)

let export_starts_with ~prefix s =
  let plen = String.length prefix in
  String.length s >= plen && String.sub s 0 plen = prefix

  let export_cc_of_efinfo (_variadic : bool) (_fixed_arity : int) : string =
    "cc_default"
  
  let export_bsig_of_external
      (formals : typ list)
      (effects : effect list)
      (ret : typ)
      (variadic : bool)
    : string =
    let args = formals |> List.map export_typ_to_coq |> export_coq_list in
    let res  = export_typ_to_coq ret in
    let ef   = export_effect_to_coq_list effects in
    let cc   = export_cc_of_efinfo variadic (List.length formals) in
    Printf.sprintf
      "{| bsig_args := %s; bsig_ef := %s; bsig_res := %s; bsig_cc := %s |}"
      args ef res cc
  

(* Produce (Coq definitions, entries to splice into global_definitions) *)
let export_coq_external_globdefs
    (ee : Beepl_ast_typechecker.efenv)
  : string list * string list =
  Beepl_ast_typechecker.Env.bindings ee
  |> List.map (fun (name, info) ->
       (* beesig for EF_external *)
       let bsig =
         export_bsig_of_external
           info.formals info.effects info.ret info.variadic
       in

       (* Coq names *)
       let ef_name   = name ^ "_ef" in          (* e.g. bpf_get_prandom_u32_ef *)
       let glob_name = "ext_" ^ name in        (* e.g. ext_bpf_get_prandom_u32 *)

       (* explicit args / result types for BeePL.External *)
       let args_coq =
         info.formals
         |> List.map export_typ_to_coq
         |> export_coq_list                       (* "nil" or "tint32u :: nil", etc. *)
       in
       let res_coq = export_typ_to_coq info.ret in

       (* 1) external_function descriptor *)
       let ef_def =
         Printf.sprintf
           "Definition %s : BeePL.external_function :=\n\
            \  BeePL.EF_external \"%s\" %s."
           ef_name name bsig
       in

       (* 2) globdef wrapping that external_function *)
       let glob_def =
         Printf.sprintf
           "Definition %s : AST.globdef BeePL.fundef type :=\n\
            \  AST.Gfun (BeePL.External %s\n\
            \                           (%s)\n\
            \                           (%s)\n\
            \                           (cc_default))."
           glob_name ef_name args_coq res_coq
       in

       (* 3) entry for global_definitions *)
       let entry =
         Printf.sprintf "(_%s, %s, None)" name glob_name
       in

       (* we return both Coq defs as a single string; caller just concatenates *)
       (ef_def ^ "\n\n" ^ glob_def, entry))
  |> List.split

let unquote s =
  let s = String.trim s in
  let n = String.length s in
  if n >= 2 && s.[0] = '"' && s.[n-1] = '"' then
    String.sub s 1 (n - 2)
  else s

let assert_unquoted (name : string) : unit =
  if String.contains name '"' then
  failwith ("internal error: quoted section name leaked: " ^ name)
let export_coq_globals prog ext_entries =
  let clean_section s =
    let prefix = "#section " in
    let s' =
      if export_starts_with ~prefix s then
        String.sub s (String.length prefix) (String.length s - String.length prefix)
      else s
    in
    unquote s'
  in
  let fun_and_global_entries =
    List.filter_map (function
      | Internal (Tfundecl (name, _, _, _, _, _), section)
      | EBPFInternal (Tfundecl (name, _, _, _, _, _), section) ->
        let sec_str = match section with
                      | Some s -> let sec = clean_section s in
                                  assert_unquoted sec;
                                  Printf.sprintf "Some \"%s\"" sec
                      | None -> "None"
          in
          Some (Printf.sprintf "(_%s, AST.Gfun (BeePL.Internal f_%s), %s)" name name sec_str)
      | GlobalLet (name, _, _, section) ->
        let sec_str = match section with
                      | Some s -> let sec = clean_section s in
                                  assert_unquoted sec;
                                  Printf.sprintf "Some \"%s\"" sec
                      | None -> "None"
          in
          Some (Printf.sprintf "(_%s, AST.Gvar v_%s, %s)" name name sec_str)
      | _ -> None) prog
  in
  let string_entries =
    Hashtbl.fold
      (fun id _ acc ->
         let def =
           Printf.sprintf "(_%s, AST.Gvar v_%s, None)" id id
         in
         def :: acc)
      string_global_table
      []
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
| Internal(f, _) -> export_transform_function ~ee ~senv ~globals f false
| EBPFInternal(f, _) -> export_transform_function ~ee ~senv ~globals f true
| StructDecl (name, fields) -> ""
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
    (* reset string globals per compilation unit *)
    Hashtbl.reset string_global_table;
    Hashtbl.reset string_to_id;
    (* then proceed *)
    let coq_header = generate_coq_prelude prog in
    let senv       = build_senv prog in
    let ee         = Beepl_ast_typechecker.build_efenv () in
  
    (* extern EF defs + entries *)
    let ext_defs, ext_entries = export_coq_external_globdefs ee in
  
    let externs    = extern_bindings_of_efenv ee in
    let global_env = externs @ export_collect_globals prog in
  
    (* Split structs vs other toplevels *)
  let struct_frags =
    List.filter_map
      (function
        | StructDecl (name, fields) -> Some (export_transform_struct name fields)
        | _ -> None)
      prog
  in
  let other_defs =
    List.map
      (export_transform_toplevel ~ee ~senv ~globals:global_env)
      prog
  in

  (* Single bcomposites definition containing all structs *)
  let bcomposites_def =
    match struct_frags with
    | [] ->
        "Definition bcomposites : list bcomposite_definition := nil.\n"
    | _ ->
        "Definition bcomposites : list bcomposite_definition :=\n(" ^
        String.concat " ::\n" struct_frags ^
        " :: nil).\n"
  in
  let stringlit_defs =
    Hashtbl.fold (fun id s acc -> export_stringlit_def id s :: acc) string_global_table [] in

  (* include extern DEFs here *)
  let defs = stringlit_defs @ ext_defs @ other_defs in

  (* pass extern ENTRIES to globals table *)
  let globals = export_coq_globals prog ext_entries in

  let publics = export_coq_public_idents prog in
  let entry   = export_find_main_or_fallback prog in
  let wrapper = export_coq_program_wrapper ~name:"bprogram" entry in
  coq_header ee
  ^ "\n\n"
  ^ bcomposites_def
  ^ "\n\n"
  ^ String.concat "\n\n" defs
  ^ "\n\n"
  ^ globals
  ^ "\n"
  ^ publics
  ^ "\n"
  ^ coq_bcomposite_correct_lemma
  ^ "\n\n"
  ^ wrapper

  
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

