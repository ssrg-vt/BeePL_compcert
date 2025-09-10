(* Transforms the BeePL (pretty language) to BeePL ast*)
open Beepl_lexer
open Beepl_ast
open Lexing
open BeePL_values
open BinNums

let string_globals : (string, string) Hashtbl.t = Hashtbl.create 17

let gensym_string_literal s =
  let id = "__stringlit_" ^ string_of_int (Hashtbl.length string_globals) in
  id
let string_to_char_list s =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (s.[i] :: acc)
  in
  aux (String.length s - 1) []
let coqint_of_camlint32 (i : int32) : BinNums.coq_Z =
    Camlcoq.coqint_of_camlint i
let rec int_to_positive = function
  | 1 -> Coq_xH
  | n when n mod 2 = 0 -> Coq_xO (int_to_positive (n / 2))
  | n -> Coq_xI (int_to_positive (n / 2))

let int_to_coq_z n =
  if n = 0 then Z0
  else if n > 0 then Zpos (int_to_positive n)
  else Zneg (int_to_positive (-n))

  let collect_global_env (prog : Beepl_ast.program) : Beepl_ast_typechecker.tyenv =
  
    let env_with_externals =
      List.fold_left (fun acc (id, t) -> Beepl_ast_typechecker.Env.add id t acc)
        Beepl_ast_typechecker.Env.empty Beepl_ast_typechecker.predefined_externals
    in
  
    let ftype_of_decl (Beepl_ast.Tfundecl (name, ret, eff, args, _, _)) =
      (name, Ftype (List.map snd args, eff, ret))
    in
    let bindings =
      List.filter_map (function
        | Beepl_ast.Internal (f, _) | Beepl_ast.EBPFInternal (f, _) -> Some (ftype_of_decl f)
        | Beepl_ast.StructDecl _ -> None
        | Beepl_ast.GlobalLet (x, t, _) -> Some (x, t)
      ) prog
    in
  
    List.fold_left (fun acc (id, t) -> Beepl_ast_typechecker.Env.add id t acc)
      env_with_externals bindings
  

let collect_idents (prog : Beepl_ast.program) : string list =
  let idents = ref [] in
  let add_ident x =
    if not (String.length x >= 13 && String.sub x 0 13 = "___stringlit_") &&
       not (List.mem x !idents)
    then idents := x :: !idents
  in
  let add_var (x, _) = add_ident x in
  let rec from_expr e =
    match e with
    | Beepl_ast.Var x -> add_ident x
    | Beepl_ast.Const _ -> ()
    | Beepl_ast.App (e1, args) ->
        from_expr e1;
        List.iter from_expr args
    | Beepl_ast.Prim (_, args) -> List.iter from_expr args
    | Beepl_ast.Let (x, _, e1, e2) -> add_ident x; from_expr e1; from_expr e2
    | Beepl_ast.If (e1, e2, e3) -> from_expr e1; from_expr e2; from_expr e3
  in
  let from_effect = function
    | Beepl_ast.Read s | Beepl_ast.Write s | Beepl_ast.Alloc s -> add_ident s
    | Beepl_ast.Io | Beepl_ast.Divergence -> ()
  in
  List.iter (fun top ->
    match top with
    | Beepl_ast.Internal (Beepl_ast.Tfundecl (name, _, effs, args, _, body), _)
    | Beepl_ast.EBPFInternal (Beepl_ast.Tfundecl (name, _, effs, args, _, body), _) ->
        add_ident name;
        List.iter from_effect effs;
        List.iter add_var args;
        from_expr body
    | Beepl_ast.StructDecl (sname, fields) ->
        add_ident sname;
        List.iter add_var fields
    | Beepl_ast.GlobalLet (x, _, e) ->
        add_ident x;
        from_expr e
  ) prog;
  List.rev !idents

let transform_primitive_type (pt : Beepl_ast.ptype) : BeeTypes.primitive_type =
  match pt with
  | Beepl_ast.Tbool -> BeeTypes.Tbool
  | Beepl_ast.Tint8 -> BeeTypes.Tint (Ctypes.I8, Ctypes.Signed, Ctypes.noattr)
  | Beepl_ast.Tint16 -> BeeTypes.Tint (Ctypes.I16, Ctypes.Signed, Ctypes.noattr)
  | Beepl_ast.Tint32 -> BeeTypes.Tint (Ctypes.I32, Ctypes.Signed, Ctypes.noattr)
  | Beepl_ast.Tuint8 -> BeeTypes.Tint (Ctypes.I8, Ctypes.Unsigned, Ctypes.noattr)
  | Beepl_ast.Tuint16 -> BeeTypes.Tint (Ctypes.I16, Ctypes.Unsigned, Ctypes.noattr)
  | Beepl_ast.Tuint32 -> BeeTypes.Tint (Ctypes.I32, Ctypes.Unsigned, Ctypes.noattr)
  | Beepl_ast.Tulong -> BeeTypes.Tlong (Ctypes.Unsigned, Ctypes.noattr)
  | Beepl_ast.Tlong -> BeeTypes.Tlong (Ctypes.Signed, Ctypes.noattr)

let transform_basic_type (bt : Beepl_ast.btype) : BeeTypes.basic_type =
  match bt with
  | Beepl_ast.Bprim pt -> BeeTypes.Bprim (transform_primitive_type pt)
  | Beepl_ast.Bstruct name -> BeeTypes.Bstruct (Camlcoq.intern_string name, Ctypes.noattr)
  | Beepl_ast.Barray (pt, n) -> BeeTypes.Barray (transform_primitive_type pt, int_to_coq_z n, Ctypes.noattr)

let transform_effect (eff : Beepl_ast.effect) : BeeTypes.effect_label =
    match eff with
    | Beepl_ast.Read s -> BeeTypes.Read (Camlcoq.intern_string s)
    | Beepl_ast.Write s -> BeeTypes.Write (Camlcoq.intern_string s)
    | Beepl_ast.Alloc s -> BeeTypes.Alloc (Camlcoq.intern_string s)
    | Beepl_ast.Io -> BeeTypes.Io
    | Beepl_ast.Divergence -> BeeTypes.Divergence

let transform_effect_list effs = List.map (transform_effect) effs

let rec transform_ptr_type (pt : Beepl_ast.ptrtype) : BeeTypes.ptr_type =
  match pt with
  | Beepl_ast.Reftype (name, bt) ->
      BeeTypes.Reftype (Camlcoq.intern_string name, transform_basic_type bt, Ctypes.noattr)
  | Beepl_ast.Otype inner_pt ->
      BeeTypes.Otype (transform_ptr_type inner_pt)

let rec transform_typ (t : Beepl_ast.typ) : BeeTypes.coq_type =
  match t with
  | Beepl_ast.Utype -> BeeTypes.Utype
  | Beepl_ast.Vtype pt -> BeeTypes.Vtype (transform_primitive_type pt)
  | Beepl_ast.Ptr pt ->
      BeeTypes.Ptrtype (transform_ptr_type pt)
  | Beepl_ast.Stype name ->
      BeeTypes.Stype (Camlcoq.intern_string name, Ctypes.noattr)
  | Beepl_ast.Atype (elem_t, size) ->
      let elem_t' = transform_typ elem_t in
      BeeTypes.Atype (elem_t', int_to_coq_z size, Ctypes.noattr)
  | Beepl_ast.Ftype (args, effs, ret) -> 
      let args' = List.map (fun t -> (transform_typ t)) args in
      let effs' = transform_effect_list effs in
      let ret' = transform_typ ret in
      BeeTypes.Ftype (args', effs', ret')
let transform_constant (c : Beepl_ast.const) (typ : Beepl_ast.typ) : BeePL_values.constant =
  match typ, c with
  | Beepl_ast.Vtype Beepl_ast.Tint32, Beepl_ast.Cint32 i ->
      ConsInt (Integers.Int.repr (int_to_coq_z (Int32.to_int i)))
  | Beepl_ast.Vtype Beepl_ast.Tlong, Beepl_ast.Clong l ->
      ConsLong (Integers.Int64.repr (int_to_coq_z (Int64.to_int l)))
  | Beepl_ast.Vtype Beepl_ast.Tbool, Beepl_ast.Cbool b ->
      ConsBool b
  | Beepl_ast.Utype, Beepl_ast.Cunit -> ConsUnit
  | _, _ ->
      failwith "Constant type mismatch or unsupported constant"
      
let transform_uop (uop : Beepl_ast.uop) : Cop.unary_operation =
  match uop with
  | Onotbool -> Cop.Onotbool
  | Onotint -> Cop.Onotint
  | Oneg -> Cop.Oneg
  | UOverloadTilde -> failwith "UOverloadTilde should be resolved before transformation"

let transform_bop (bop : Beepl_ast.bop) : Cop.binary_operation =
  match bop with
  | Oadd -> Cop.Oadd
  | Osub -> Cop.Osub
  | Omul -> Cop.Omul
  | Odiv -> Cop.Odiv
  | Omod -> Cop.Omod
  | Oand -> Cop.Oand
  | Oor -> Cop.Oor
  | Oxor -> Cop.Oxor
  | Oshl -> Cop.Oshl
  | Oshr -> Cop.Oshr
  | Oeq -> Cop.Oeq
  | One -> Cop.One
  | Olt -> Cop.Olt
  | Ogt -> Cop.Ogt
  | Ole -> Cop.Ole
  | Oge -> Cop.Oge
  (* Add other binary operations as needed *)

let transform_builtin (b : Beepl_ast.builtin) : BeePL.builtin =
  match b with
  | Beepl_ast.Uop uop -> BeePL.Uop (transform_uop uop)
  | Beepl_ast.Bop bop -> BeePL.Bop (transform_bop bop)
  | Beepl_ast.Cast t ->
      let t' = transform_typ t in
      BeePL.Cast t'
  | Beepl_ast.Ref -> BeePL.Ref
  | Beepl_ast.Deref -> BeePL.Deref
  | Beepl_ast.Massgn -> BeePL.Massgn

let rec resolve_overloaded_op (e : expr) (typ : typ) : expr =
  match e with
  | Prim (Uop UOverloadTilde, [arg]) ->
      begin match typ with
      | Vtype Tbool -> Prim (Uop Onotbool, [resolve_overloaded_op arg (Vtype Tbool)])
      | Vtype Tint32 -> Prim (Uop Onotint, [resolve_overloaded_op arg (Vtype Tint32)])
      | Vtype Tlong -> Prim (Uop Onotint, [resolve_overloaded_op arg (Vtype Tlong)])
      | _ -> failwith "Unsupported type for overloaded tilde"
      end
  | Prim (Cast t, args) ->
        Prim (Cast t, List.map (fun a -> resolve_overloaded_op a typ) args)
  | Prim (op, args) ->
      Prim (op, List.map (fun a -> resolve_overloaded_op a typ) args)
  | App (f, args) ->
      App (resolve_overloaded_op f typ, List.map (fun a -> resolve_overloaded_op a typ) args)
  | Let (x, ty, e1, e2) ->
      Let (x, ty, resolve_overloaded_op e1 ty, resolve_overloaded_op e2 typ)
  | If (e1, e2, e3) ->
      If (resolve_overloaded_op e1 (Vtype Tbool), resolve_overloaded_op e2 typ, resolve_overloaded_op e3 typ)
  | _ -> e

let rec transform_expr (env : Beepl_ast_typechecker.tyenv) (e : Beepl_ast.expr) : BeePL.expr =
  let typ = Beepl_ast_typechecker.infer_expr env e in
  let e' = resolve_overloaded_op e typ in
  let t' = transform_typ typ in
  match e' with
  | Beepl_ast.Var x ->
      BeePL.Var (Camlcoq.intern_string x, t')
      | Beepl_ast.Const c ->
        (match c with
         | Cstring s ->
            let id_str = gensym_string_literal s in
            Hashtbl.replace string_globals id_str s;
            let id = Camlcoq.intern_string id_str in
            let h_id = Camlcoq.intern_string "h" in
            BeePL.Var (
              id,
              BeeTypes.Ptrtype (
                BeeTypes.Reftype (
                  h_id,
                  BeeTypes.Bprim (BeeTypes.Tint (Ctypes.I8, Ctypes.Signed, Ctypes.noattr)),  (* Must match global var type *)
                  Ctypes.noattr
                )
              )
            )
         | _ -> BeePL.Const (transform_constant c typ, t'))
    
    
  | Beepl_ast.App (e1, args) ->
      let e1' = transform_expr env e1 in
      let args' = List.map (transform_expr env) args in
      BeePL.App (e1', args', t')
  | Beepl_ast.Prim (Uop uop, args) ->
    let args' = List.map (transform_expr env) args in
    BeePL.Prim (transform_builtin (Beepl_ast.Uop uop), args', t')
  | Beepl_ast.Prim (Bop bop, args) ->
    let args' = List.map (transform_expr env) args in
    BeePL.Prim (transform_builtin (Beepl_ast.Bop bop), args', t')
  | Beepl_ast.Prim (Cast t, args) ->
      let args' = List.map (transform_expr env) args in
      let t'' = transform_typ t in
      BeePL.Prim (BeePL.Cast t'', args', t')
  | Beepl_ast.Prim (Ref, args) ->
      let args' = List.map (transform_expr env) args in
      BeePL.Prim (BeePL.Ref, args', t')
  | Beepl_ast.Prim (Deref, args) ->
      let args' = List.map (transform_expr env) args in
      BeePL.Prim (BeePL.Deref, args', t')
  | Beepl_ast.Prim (Massgn, args) ->
      let args' = List.map (transform_expr env) args in
      BeePL.Prim (BeePL.Massgn, args', t')
  | Beepl_ast.Let (x, t, e1, e2) ->
      let e1' = transform_expr env e1 in
      let env' = Beepl_ast_typechecker.Env.add x t env in
      let e2' = transform_expr env' e2 in
      BeePL.Bind (Camlcoq.intern_string x, transform_typ t, e1', e2', t')
  | Beepl_ast.If (e1, e2, e3) ->
      let e1' = transform_expr env e1 in
      let e2' = transform_expr env e2 in
      let e3' = transform_expr env e3 in
      BeePL.Cond (e1', e2', e3', t')
      

let rec collect_vars (e : Beepl_ast.expr) : (string * Beepl_ast.typ) list =
  let unique_vars vars =
    List.fold_left (fun acc (x, t) ->
      if List.exists (fun (y, _) -> x = y) acc then acc else (x, t) :: acc
    ) [] vars
  in
  match e with
  | Beepl_ast.Var _ | Beepl_ast.Const _ -> []
  | Beepl_ast.Prim (_, args) ->
      unique_vars (List.flatten (List.map collect_vars args))
  | Beepl_ast.Let (x, t, e1, e2) ->
    let rest = collect_vars e1 @ collect_vars e2 in
    if String.equal x "_" || t = Beepl_ast.Utype then
      unique_vars rest
    else
      unique_vars ((x, t) :: rest)
  | Beepl_ast.App (e1, args) ->
      unique_vars (collect_vars e1 @ List.flatten (List.map collect_vars args))
  | Beepl_ast.If (e1, e2, e3) ->
      unique_vars (collect_vars e1 @ collect_vars e2 @ collect_vars e3)

let transform_function fdecl is_ebpf global_env =
  let Tfundecl (name, ret, eff, args, _, body) = fdecl in
  let local_env = List.fold_left (fun acc (x, t) -> Beepl_ast_typechecker.Env.add x t acc) global_env args in
  let fn_args = List.map (fun (id, t) -> (Camlcoq.intern_string id, transform_typ t)) args in
  let fn_vars = List.map (fun (id, t) -> (Camlcoq.intern_string id, transform_typ t)) (collect_vars body) in
  let fn_body = transform_expr local_env body in
  {
    BeePL.fn_return = transform_typ ret;
    BeePL.fn_effect = transform_effect_list eff;
    BeePL.fn_callconv = AST.cc_default;
    BeePL.fn_args = fn_args;
    BeePL.fn_vars = fn_vars;
    BeePL.fn_body = fn_body;
    BeePL.is_ebpf = is_ebpf;
  }
      

let transform_struct (name : string) (fields : (string * Beepl_ast.typ) list) : BeeTypes.bcomposite_definition =
  let members = List.map (fun (id, t) ->
      BeeTypes.Member_plain (Camlcoq.intern_string id, transform_typ t)
    ) fields in
  BeeTypes.Bcomposite (Camlcoq.intern_string name, Ctypes.Struct, members, Ctypes.noattr)

let get_fun_name (Tfundecl (name, _, _, _, _, _)) = name

let transform_toplevel global_env = function
| Internal(f, sec) ->
    let id = Camlcoq.intern_string (get_fun_name f) in
    `Fun (id, transform_function f false global_env, sec)
| EBPFInternal(f, sec) ->
    let id = Camlcoq.intern_string (get_fun_name f) in
    `Fun (id, transform_function f true global_env, sec)
| StructDecl (name, fields) ->
    let id = Camlcoq.intern_string name in
    `Struct (id, transform_struct name fields)
| GlobalLet (name, typ, expr) ->
    let id = Camlcoq.intern_string name in
    let t' = transform_typ typ in
    `Global (id, t', expr)
      
let find_main_or_fallback prog : string =
  let names =
    List.fold_left (fun acc top ->
    match top with
      | Beepl_ast.Internal (Beepl_ast.Tfundecl (name, _, _, _, _, _), _)
      | Beepl_ast.EBPFInternal (Beepl_ast.Tfundecl (name, _, _, _, _, _), _) ->
          name :: acc
        | _ -> acc
          ) [] prog in
      match List.find_opt (fun name -> name = "main") names with
      | Some name -> name
      | None ->
    match List.rev names with
      | fn :: _ -> fn
      | [] -> failwith "No function declarations found in the program"

(*The reorder_program function ensures that the fun main declaration appears first in the AST. So:
  "main" is the first identifier seen by create_ident_map.
  Therefore, it’s guaranteed to get Coq_xH, the correct value required by the CompCert linker. *)   
let reorder_program (prog : Beepl_ast.program) : Beepl_ast.program =
  let is_main = function
    | Beepl_ast.Internal (Beepl_ast.Tfundecl ("main", _, _, _, _, _), _)
    | Beepl_ast.EBPFInternal (Beepl_ast.Tfundecl ("main", _, _, _, _, _), _) -> true
    | _ -> false
  in
  let main_fun = List.filter is_main prog in
  let rest = List.filter (fun d -> not (is_main d)) prog in
  main_fun @ rest

let eval_const_expr (e : Beepl_ast.expr) : AST.init_data list =
  match e with
  | Beepl_ast.Const (Beepl_ast.Cint32 i) ->
    [AST.Init_int32 (Integers.Int.repr (coqint_of_camlint32 i))]
  | Beepl_ast.Const (Beepl_ast.Clong l) ->
    [AST.Init_int64 (Integers.Int64.repr (Camlcoq.coqint_of_camlint64 l))]
  | Beepl_ast.Const (Beepl_ast.Cbool b) ->
    let v = if b then 1l else 0l in
    [AST.Init_int8 (Integers.Int.repr (coqint_of_camlint32 v))]
  | Beepl_ast.Const (Beepl_ast.Cstring s) ->
    let chars = List.init (String.length s + 1) (fun i ->
      let code = if i < String.length s then Char.code s.[i] else 0 in
      AST.Init_int8 (Integers.Int.repr (coqint_of_camlint32 (Int32.of_int code)))
    ) in
    chars
  | _ -> []
 
let init_data_of_string (s : string) : AST.init_data list =
  let chars = List.init (String.length s) (String.get s) in
  let char_init = List.map (fun c ->
    AST.Init_int8 (Integers.Int.repr (int_to_coq_z (Char.code c)))
  ) chars in
  let null_term = AST.Init_int8 (Integers.Int.repr Z0) in
  char_init @ [null_term]
   

  let transform_program (prog : Beepl_ast.program) : BeePL.program =
    let prog = reorder_program prog in  
    let idents = collect_idents prog in
  
    let get_id = Camlcoq.intern_string in
  
    let prog_ident_to_string =
      List.map (fun s -> (get_id s, string_to_char_list s)) idents in
  
    let global_env = collect_global_env prog in
    let transformed_decls =
        List.map (transform_toplevel global_env) prog in
  
    let prog_types =
      List.filter_map (function `Struct (_, s) -> Some s | _ -> None) transformed_decls in
  
    let fun_defs =
      List.filter_map (function `Fun (id, f, sec) -> Some (id, f, sec) | _ -> None) transformed_decls in
    
    let external_globals =
      List.map (fun (id, typ) ->
        let coq_id = Camlcoq.intern_string id in
        match typ with
        | Ftype (args, effs, ret) ->
            let coq_args = List.map transform_typ args in
            let coq_ret = transform_typ ret in
            let coq_eff = transform_effect_list effs in
            let signature = {
              BeePL.bsig_args = coq_args;
              BeePL.bsig_ef = coq_eff;
              BeePL.bsig_res = coq_ret;
              bsig_cc = { AST.cc_vararg = Some (coqint_of_camlint32 1l); cc_unproto = false; cc_structret = false };
            } in
            let ef = AST.Gfun (BeePL.External (
              BeePL.EF_external (string_to_char_list id, signature),
              coq_args,
              coq_ret,
              { AST.cc_vararg = Some (coqint_of_camlint32 1l); cc_unproto = false; cc_structret = false }
            )) in
            ((coq_id, ef), None)
        | _ -> failwith ("Expected function type for external: " ^ id)
      ) Beepl_ast_typechecker.predefined_externals in 
  
    let globals_from_strings =
      Hashtbl.fold (fun id s acc ->
        let id' = Camlcoq.intern_string id in
        let gvar = AST.Gvar {
          AST.gvar_info = BeeTypes.Atype (
            BeeTypes.Vtype (BeeTypes.Tint (Ctypes.I8, Ctypes.Signed, Ctypes.noattr)),
            int_to_coq_z (String.length s + 1),
            Ctypes.noattr
          );
          AST.gvar_init = init_data_of_string s;
          AST.gvar_readonly = true;
          AST.gvar_volatile = false;
        } in
        ((id', gvar), None) :: acc
      ) string_globals [] in         
  
    let prog_defs =
      let defs =
        List.filter_map (function
          | `Fun (id, f, section) ->
              let sec =
                match section with
                | Some s when String.length s > 8 && String.sub s 0 8 = "#section" ->
                    let raw = String.trim (String.sub s 8 (String.length s - 8)) in
                    Some (string_to_char_list ("\"" ^ raw ^ "\""))
                | Some s -> Some (string_to_char_list ("\"" ^ s ^ "\""))
                | None -> None
              in
              Some ((id, AST.Gfun (BeePL.Internal f)), sec)
  
          | `Global (id, t, v) ->
              Some ((id, AST.Gvar {
                AST.gvar_info = t;
                AST.gvar_init = eval_const_expr v;
                AST.gvar_readonly = false;
                AST.gvar_volatile = false;
              }), None)
  
          | _ -> None
        ) transformed_decls
      in
      external_globals @ defs @ globals_from_strings in 
    let is_not_stringlit id =
      let name = Camlcoq.extern_atom id in
      not (String.length name >= 13 && String.sub name 0 13 = "___stringlit_")
    in
      
    let fun_ids = List.filter is_not_stringlit (List.map (fun (id, _, _) -> id) fun_defs) in
  
    let prog_comp_env = BeeTypes.build_bcomposite_env' prog_types in
    let prog_main = get_id (find_main_or_fallback prog) in
    let external_ids = List.map (fun (name, _) -> Camlcoq.intern_string name) Beepl_ast_typechecker.predefined_externals in
  
    (* Remove __stringlit_* from prog_public but keep in prog_ident_to_string *)
    (* Exclude any ident that corresponds to a string literal *)
    let is_stringlit_id id =
      let name = Camlcoq.extern_atom id in
      String.length name >= 13 && String.sub name 0 13 = "__stringlit_"
    in

    let filtered_fun_ids = List.filter (fun id -> not (is_stringlit_id id)) fun_ids in

    let prog_public =
      if List.mem prog_main filtered_fun_ids then
        filtered_fun_ids @ external_ids
      else
        prog_main :: filtered_fun_ids @ external_ids
    in

    {
      BeePL.prog_defs = prog_defs;
      BeePL.prog_public = prog_public;
      BeePL.prog_main = prog_main;
      BeePL.prog_types = prog_types;
      BeePL.prog_comp_env = prog_comp_env;
      BeePL.prog_ident_to_string = prog_ident_to_string;
    }
  

let parse_file (filename : string) : Beepl_ast.program =
  let ch = open_in filename in
  let lexbuf = from_channel ch in
  try
    let result = Beepl_parser.prog Beepl_lexer.read_token lexbuf in
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

let parse_and_transform_bpl (filename : string) : BeePL.program =
  let program = parse_file filename in
  transform_program program
