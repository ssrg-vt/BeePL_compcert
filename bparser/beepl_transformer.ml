(* Transforms the BeePL (pretty language) to BeePL ast*)
open Beepl_lexer
open Beepl_ast
open Lexing
open BeePL_values
open BinNums

let string_globals : (string, string) Hashtbl.t = Hashtbl.create 17

(*let dbg s = Printf.eprintf "Debug message %s\n%!" s*)

let gensym_string_literal s =
  let id = "__stringlit_" ^ string_of_int (Hashtbl.length string_globals) in
  id

(* --- Section name normalization helpers --- *)
let unquote (s : string) : string =
  let s = String.trim s in
  let n = String.length s in
  if n >= 2 && s.[0] = '"' && s.[n-1] = '"' then
  String.sub s 1 (n - 2)
  else s
  
let normalize_section (s : string) : string =
  (* Accept "#section foo", "#section \"foo\"", or just "foo" *)
 let s' = if String.length s >= 8 && String.sub s 0 8 = "#section" then
        String.trim (String.sub s 8 (String.length s - 8))
        else s
 in unquote s'

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

let rec int_to_coq_nat (n : int) : Datatypes.nat =
    if n <= 0 then Datatypes.O else Datatypes.S (int_to_coq_nat (n - 1))

(* Build a struct environment (senv) from top-level struct declarations *)
let build_senv (prog : Beepl_ast.program) : Beepl_ast_typechecker.Senv.t =
  List.fold_left
    (fun acc -> function
      | Beepl_ast.StructDecl (name, fields) ->
          Beepl_ast_typechecker.Senv.add name fields acc
      | _ -> acc)
    Beepl_ast_typechecker.Senv.empty
    prog

(* externs -> [(name, Ftype (...))] *)
let extern_bindings_of_efenv (ee : Beepl_ast_typechecker.efenv) : (string * Beepl_ast.typ) list =
  Beepl_ast_typechecker.Env.bindings ee
  |> List.map (fun (name, info) ->
      ( name
      , Beepl_ast.Ftype (info.Beepl_ast_typechecker.formals, 
                         info.Beepl_ast_typechecker.effects, 
                         info.Beepl_ast_typechecker.ret)
      ))

let collect_global_env
    (ee   : Beepl_ast_typechecker.efenv)
    (prog : Beepl_ast.program)
  : Beepl_ast_typechecker.tyenv =
  let externs = extern_bindings_of_efenv ee in
  let ftype_of_decl (Beepl_ast.Tfundecl (name, ret, eff, args, _, _)) =
    (name, Beepl_ast.Ftype (List.map snd args, eff, ret))
  in
  let bindings =
    List.filter_map (function
      | Beepl_ast.Internal (f, _) | Beepl_ast.EBPFInternal (f, _) -> Some (ftype_of_decl f)
      | Beepl_ast.StructDecl _ -> None
      | Beepl_ast.GlobalLet (x, t, _, _) -> Some (x, t)
    ) prog
  in
  List.fold_left
    (fun acc (id, t) -> Beepl_ast_typechecker.Env.add id t acc)
    (List.fold_left
       (fun acc (id, t) -> Beepl_ast_typechecker.Env.add id t acc)
       Beepl_ast_typechecker.Env.empty
       externs)
    bindings
  

let collect_idents (prog : Beepl_ast.program) : string list =
  let idents = ref [] in
  let add_ident x =
    if not (String.length x >= 12 && String.sub x 0 12 = "__stringlit_") &&
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
    | Beepl_ast.For (e1, e2, _, e3) -> from_expr e1; from_expr e2; from_expr e3
    | Beepl_ast.Sinit (s, fields, exprs) ->
        List.iter from_expr exprs
    | Beepl_ast.Fget (e, _) -> from_expr e
    | Beepl_ast.Ainit (arr, exprs) -> add_ident arr; List.iter from_expr exprs
    | Beepl_ast.Aaccess (s, _) -> add_ident s
    | Beepl_ast.Match (e, patterns, exprs) ->
        from_expr e;
        List.iter (function
          | Beepl_ast.Psome x -> add_ident x
          | Beepl_ast.Pnone -> ()
          | Beepl_ast.Pbytes (s, _, fields) ->
              add_ident s;
              List.iter add_var fields
        ) patterns;
        List.iter from_expr exprs
    | Beepl_ast.Esome e1 -> from_expr e1
    | Beepl_ast.Enone t -> ()

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
    | Beepl_ast.GlobalLet (x, _, e, _) ->
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
  | Beepl_ast.Bytes -> BeeTypes.Bytes
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

let transform_pattern (p : Beepl_ast.pattern) : BeePL.pattern =
  match p with
  | Beepl_ast.Psome x -> BeePL.Psome (Camlcoq.intern_string x)
  | Beepl_ast.Pnone -> BeePL.Pnone
  | Beepl_ast.Pbytes (s, t, fields) ->
      let fields' = List.map (fun (id, t) -> (Camlcoq.intern_string id, transform_typ t)) fields in
      BeePL.Pbytes (Camlcoq.intern_string s, transform_typ t, fields')
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
  | For (e1, e2, d, e3) ->
      For (resolve_overloaded_op e1 typ, resolve_overloaded_op e2 typ, d, resolve_overloaded_op e3 typ)
  | Sinit (s, fields, exprs) ->
      Sinit (s, fields, List.map (fun a -> resolve_overloaded_op a typ) exprs)
  | Fget (e, field) ->
      Fget (resolve_overloaded_op e typ, field)
  | Ainit (arr, exprs) ->
      Ainit (arr, List.map (fun a -> resolve_overloaded_op a typ) exprs)
  | Aaccess (s, n) ->
      Aaccess (s, n)
  | Match (e, patterns, exprs) ->
      Match (resolve_overloaded_op e typ, patterns, List.map (fun a -> resolve_overloaded_op a typ) exprs)
  | Esome e1 ->
      Esome (resolve_overloaded_op e1 typ)
  | Enone t -> Enone t
  | _ -> e

let transform_dir (d : Beepl_ast.dir) : BeePL_values.dir =
  match d with
  | Beepl_ast.Up -> BeePL_values.Up
  | Beepl_ast.Down -> BeePL_values.Down

let rec transform_expr (ee: Beepl_ast_typechecker.efenv) (senv : Beepl_ast_typechecker.Senv.t) (env : Beepl_ast_typechecker.tyenv) (e : Beepl_ast.expr) : BeePL.expr =
  (*dbg "Enter expr transformation";*)
  let typ = Beepl_ast_typechecker.infer_expr ee senv env e in
  (*dbg "Exit type inference\n%!";*)
  let e' = resolve_overloaded_op e typ in
  let t' = transform_typ typ in
  match e' with
  | Beepl_ast.Var x ->
      BeePL.Var (Camlcoq.intern_string x, t')
      | Beepl_ast.Const c ->
        (match c with
         (*| Cstring s ->
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
            )*)
            | Cstring s ->
              let id_str = gensym_string_literal s in
              Hashtbl.replace string_globals id_str s;
              let id = Camlcoq.intern_string id_str in
              let arr_t =
                BeeTypes.Atype (
                  BeeTypes.Vtype (BeeTypes.Tint (Ctypes.I8, Ctypes.Signed, Ctypes.noattr)),
                  int_to_coq_z (String.length s + 1),
                  Ctypes.noattr)
              in
              BeePL.Var (id, arr_t)
         | _ -> BeePL.Const (transform_constant c typ, t'))
    
    
  | Beepl_ast.App (e1, args) ->
      let e1' = transform_expr ee senv env e1 in
      let args' = List.map (transform_expr ee senv env) args in
      BeePL.App (e1', args', t')
  | Beepl_ast.Prim (Uop uop, args) ->
    let args' = List.map (transform_expr ee senv env) args in
    BeePL.Prim (transform_builtin (Beepl_ast.Uop uop), args', t')
  | Beepl_ast.Prim (Bop bop, args) ->
    let args' = List.map (transform_expr ee senv env) args in
    BeePL.Prim (transform_builtin (Beepl_ast.Bop bop), args', t')
  | Beepl_ast.Prim (Cast t, args) ->
      let args' = List.map (transform_expr ee senv env) args in
      let t'' = transform_typ t in
      BeePL.Prim (BeePL.Cast t'', args', t')
  | Beepl_ast.Prim (Ref, args) ->
      let args' = List.map (transform_expr ee senv env) args in
      BeePL.Prim (BeePL.Ref, args', t')
  | Beepl_ast.Prim (Deref, args) ->
      let args' = List.map (transform_expr ee senv env) args in
      BeePL.Prim (BeePL.Deref, args', t')
  | Beepl_ast.Prim (Massgn, args) ->
      let args' = List.map (transform_expr ee senv env) args in
      BeePL.Prim (BeePL.Massgn, args', t')
  | Beepl_ast.Let (x, t, e1, e2) ->
      let e1' = transform_expr ee senv env e1 in
      let env' = Beepl_ast_typechecker.Env.add x t env in
      let e2' = transform_expr ee senv env' e2 in
      BeePL.Bind (Camlcoq.intern_string x, transform_typ t, e1', e2', t')
  | Beepl_ast.If (e1, e2, e3) ->
      let e1' = transform_expr ee senv env e1 in
      let e2' = transform_expr ee senv env e2 in
      let e3' = transform_expr ee senv env e3 in
      BeePL.Cond (e1', e2', e3', t')
  | Beepl_ast.For (e1, e2, d, e3) ->
      let e1' = transform_expr ee senv env e1 in
      let e2' = transform_expr ee senv env e2 in
      let e3' = transform_expr ee senv env e3 in
      BeePL.For (e1', e2', transform_dir d, e3', t')
  | Beepl_ast.Sinit (s, fnames, exprs) ->
      let exprs' = List.map (transform_expr ee senv env) exprs in
      let fnames' = List.map Camlcoq.intern_string fnames in
      BeePL.Sinit (Camlcoq.intern_string s, fnames', exprs', t')
  | Beepl_ast.Fget (e, field) ->
      let e' = transform_expr ee senv env e in
      BeePL.Sfield (e', Camlcoq.intern_string field, t')
  | Beepl_ast.Ainit (arr, exprs) ->
      let exprs' = List.map (transform_expr ee senv env) exprs in
      BeePL.Ainit (Camlcoq.intern_string arr, t', exprs', t')
  | Beepl_ast.Aaccess (arr, index) ->
      begin match Beepl_ast_typechecker.Env.find_opt arr env with 
      | Some (Atype (elem_ty, size)) -> BeePL.Aaccess (Camlcoq.intern_string arr, (transform_typ ((Atype (elem_ty, size)))), int_to_coq_nat index, t')
      | Some _ -> failwith "Aaccess can only be applied to array types"
      | _ -> failwith ("Array "^arr^" not found in environment")
      end
  | Beepl_ast.Match (scrut, pats, bodies) ->
    (* type of scrutinee (under the current env) *)
    let scrut_ty = Beepl_ast_typechecker.infer_expr ee senv env scrut in
    (* scrutinee must be option pointer; compute the inner pointer type we bind in 'some x' *)
    let inner_ptr_ty =
      match scrut_ty with
      | Ptr (Otype pt) -> Ptr pt
      | Bytes -> Bytes
      | _ -> failwith "Match scrutinee must be an option pointer (Ptr (Otype _))"
    in
    let scrut' = transform_expr ee senv env scrut in
    let pats'  = List.map transform_pattern pats in

    (* transform each branch body with its own extended env *)
    let transform_branch p b =
      let env' =
        match p with
        | Beepl_ast.Pnone      -> env
        | Beepl_ast.Psome x    -> Beepl_ast_typechecker.Env.add x inner_ptr_ty env
        | Beepl_ast.Pbytes (s, t, fields) ->
          let env1 = Beepl_ast_typechecker.Env.add s t env in
          List.fold_left (fun acc (id, t) -> Beepl_ast_typechecker.Env.add id t acc) env1 fields
      in
      transform_expr ee senv env' b
    in
    let bodies' =
      try List.map2 transform_branch pats bodies with
      | Invalid_argument _ -> failwith "Match: branches/patterns arity mismatch"
    in
    BeePL.Match (scrut', pats', bodies', t')
  | Beepl_ast.Esome e1 ->
    let child_ty = Beepl_ast_typechecker.infer_expr ee senv env e1 in
    (match child_ty with
      | Ptr pt ->
          let node_ty = Ptr (Otype pt) in
          (BeePL.Esome (transform_expr ee senv env e1, transform_typ node_ty)) 
      | _ -> failwith "Esome expects a pointer child")
  | Beepl_ast.Enone t ->
      (* rely on the inferred type at this site; it must be Ptr (Otype _) *)
      (match t with
       | Ptr (Otype _) -> BeePL.Enone (transform_typ t)
       | _ -> failwith "Enone must be an option-pointer here")
  
let rec collect_vars (ee : Beepl_ast_typechecker.efenv) (senv : Beepl_ast_typechecker.Senv.t) (env : Beepl_ast_typechecker.tyenv) (e : Beepl_ast.expr) : (string * Beepl_ast.typ) list =
  let unique_vars vars =
    List.fold_left (fun acc (x, t) ->
      if List.exists (fun (y, _) -> x = y) acc then acc else (x, t) :: acc
    ) [] vars
  in
  match e with
  | Beepl_ast.Var _ | Beepl_ast.Const _ -> []
  | Beepl_ast.Prim (_, args) ->
      unique_vars (List.flatten (List.map (collect_vars ee senv env) args))
  | Beepl_ast.Let (x, t, e1, e2) ->
    let v1   = collect_vars ee senv env e1 in
    let env' = Beepl_ast_typechecker.Env.add x t env in   (* <-- extend env! *)
    let v2   = collect_vars ee senv env' e2 in
    let base = unique_vars (v1 @ v2) in
    if String.equal x "_" || t = Beepl_ast.Utype then base
    else unique_vars ((x, t) :: base)
  | Beepl_ast.App (e1, args) ->
      unique_vars (collect_vars ee senv env e1 @ List.flatten (List.map (collect_vars ee senv env) args))
  | Beepl_ast.If (e1, e2, e3) ->
      unique_vars (collect_vars ee senv env e1 @ collect_vars ee senv env e2 @ collect_vars ee senv env e3)
  | Beepl_ast.For (e1, e2, _, e3) ->
      unique_vars (collect_vars ee senv env e1 @ collect_vars ee senv env e2 @ collect_vars ee senv env e3)
  | Beepl_ast.Sinit (s, fields, exprs) ->
      unique_vars (List.flatten (List.map (collect_vars ee senv env) exprs)) 
  | Beepl_ast.Fget (e, _) ->
      collect_vars ee senv env e 
  | Beepl_ast.Ainit (arr, exprs) ->
      unique_vars (List.flatten (List.map (collect_vars ee senv env) exprs))
  | Beepl_ast.Aaccess (s, n) ->
      []   
  | Beepl_ast.Match (scrut, patterns, bodies) ->
      (* infer ONLY the scrutinee type to know what the pattern binds *)
      let scrut_ty = Beepl_ast_typechecker.infer_expr ee senv env scrut in
      let inner_pt_opt =
        match scrut_ty with
        | Beepl_ast.Ptr (Beepl_ast.Otype pt) -> Some pt
        | Beepl_ast.Bytes -> None
        | _ -> None
      in
      let pat_bindings pat : (string * Beepl_ast.typ) list =
        match pat, inner_pt_opt with
        | Beepl_ast.Pnone, _ -> []
        | Beepl_ast.Psome x, Some pt -> [ (x, Beepl_ast.Ptr pt) ]  (* so !x typechecks *)
        | Beepl_ast.Psome _, None -> []                            (* non-option scrut: ignore *)
        | Beepl_ast.Pbytes (s, t, fields), _ -> (s, t) :: fields
      in
      let extend env binds =
        List.fold_left (fun acc (x,t) -> Beepl_ast_typechecker.Env.add x t acc) env binds
      in
      let scrut_vars = collect_vars ee senv env scrut in
      let bound_vars = List.flatten (List.map pat_bindings patterns) in
      let body_vars =
        List.flatten
          (List.map2
             (fun pat body ->
               let env' = extend env (pat_bindings pat) in
               collect_vars ee senv env' body)
             patterns bodies)
      in
      unique_vars (scrut_vars @ bound_vars @ body_vars)
  | Beepl_ast.Esome e1 ->
      collect_vars ee senv env e1
  | Beepl_ast.Enone t ->
      [] 

let transform_function fdecl is_ebpf ee senv global_env =
  let Tfundecl (name, ret, eff, args, _, body) = fdecl in
  let local_env = List.fold_left (fun acc (x, t) -> Beepl_ast_typechecker.Env.add x t acc) global_env args in
  let fn_args = List.map (fun (id, t) -> (Camlcoq.intern_string id, transform_typ t)) args in
  let fn_vars = List.map (fun (id, t) -> (Camlcoq.intern_string id, transform_typ t)) (collect_vars ee senv local_env body) in
  let fn_body = transform_expr ee senv local_env body in
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

let transform_toplevel ee senv global_env = function
| Internal(f, sec) ->
    let id = Camlcoq.intern_string (get_fun_name f) in
    `Fun (id, transform_function f false ee senv global_env, sec)
| EBPFInternal(f, sec) ->
    let id = Camlcoq.intern_string (get_fun_name f) in
    `Fun (id, transform_function f true ee senv global_env, sec)
| StructDecl (name, fields) ->
    let id = Camlcoq.intern_string name in
    `Struct (id, transform_struct name fields)
| GlobalLet (name, typ, expr, sec) ->
    let id = Camlcoq.intern_string name in
    let t' = transform_typ typ in
    `Global (id, t', expr, sec)
      
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
    (*dbg "start";*)
    let prog = reorder_program prog in
    (*dbg "reorder_program done";*)
  
    let idents = collect_idents prog in
    (*dbg (Printf.sprintf "collect_idents done (n=%d)" (List.length idents));*)
  
    let get_id = Camlcoq.intern_string in
    let prog_ident_to_string =
      List.map (fun s -> (get_id s, string_to_char_list s)) idents in
    (*dbg "ident_to_string built";*)
  
    let senv = build_senv prog in
    (*dbg "build_senv done";*)
    let ee   = Beepl_ast_typechecker.build_efenv () in

    let global_env = collect_global_env ee prog in
    (*dbg "collect_global_env done";*)
  
    let transformed_decls = List.map (transform_toplevel ee senv global_env) prog in
    (*dbg "transform_toplevel done";*)
  
    let prog_types =
      List.filter_map (function `Struct (_, s) -> Some s | _ -> None) transformed_decls in
    (*dbg (Printf.sprintf "prog_types done (n=%d)" (List.length prog_types));*)
  
    let fun_defs =
      List.filter_map (function `Fun (id, f, sec) -> Some (id, f, sec) | _ -> None) transformed_decls in
    (*dbg (Printf.sprintf "fun_defs done (n=%d)" (List.length fun_defs));*)
  
    (* Build extern decls from efenv *)
  let external_globals =
    Beepl_ast_typechecker.Env.bindings ee
    |> List.map (fun (name, info) ->
         let coq_id  = Camlcoq.intern_string name in
         let coq_args = List.map transform_typ info.Beepl_ast_typechecker.formals in
         let coq_ret  = transform_typ info.Beepl_ast_typechecker.ret in
         let coq_eff  = transform_effect_list info.Beepl_ast_typechecker.effects in
         let cc =
           { AST.cc_vararg  = (if info.Beepl_ast_typechecker.variadic then Some (coqint_of_camlint32 1l) else None);
             cc_unproto     = false;
             cc_structret   = false }
         in
         let signature =
           { BeePL.bsig_args = coq_args;
             BeePL.bsig_ef   = coq_eff;
             BeePL.bsig_res  = coq_ret;
             bsig_cc         = cc }
         in
         let ef =
           AST.Gfun (BeePL.External (
             BeePL.EF_external (string_to_char_list name, signature),
             coq_args, coq_ret, cc))
         in
         ((coq_id, ef), None))
  in
  
    let globals_from_strings =
      Hashtbl.fold (fun id s acc ->
        let id'  = Camlcoq.intern_string id in
        let gvar = AST.Gvar {
          AST.gvar_info = BeeTypes.Atype (
            BeeTypes.Vtype (BeeTypes.Tint (Ctypes.I8, Ctypes.Signed, Ctypes.noattr)),
            int_to_coq_z (String.length s + 1), Ctypes.noattr);
          AST.gvar_init = init_data_of_string s;
          AST.gvar_readonly = true; AST.gvar_volatile = false;
        } in ((id', gvar), None) :: acc
      ) string_globals [] in
    (*dbg (Printf.sprintf "globals_from_strings done (n=%d)" (List.length globals_from_strings));*)
  
    let defs =
      List.filter_map (function
        | `Fun (id, f, section) -> 
          let sec =
            match section with
                      | Some s ->let sec = normalize_section s in
                                 Some (string_to_char_list sec)   (* bare: no extra quotes *)
                      | None -> None
            in Some ((id, AST.Gfun (BeePL.Internal f)), sec)
        | `Global (id, t, v, section) ->
          let sec =
            match section with
            | Some s -> let sec = normalize_section s in
                        Some (string_to_char_list sec)     (* bare: no extra quotes *)
            | None -> None
            in Some ((id, AST.Gvar {
              AST.gvar_info = t; AST.gvar_init = eval_const_expr v;
              AST.gvar_readonly = false; AST.gvar_volatile = false }), sec)
        | _ -> None
      ) transformed_decls in
    (*dbg "defs done";*)
  
    let prog_defs = external_globals @ defs @ globals_from_strings in
    (*dbg (Printf.sprintf "prog_defs concat done (n=%d)" (List.length prog_defs));*)
  
    let is_stringlit_id id =
      let name = Camlcoq.extern_atom id in
      String.length name >= 12 && String.sub name 0 12 = "__stringlit_"
    in
    let is_not_stringlit id = not (is_stringlit_id id) in
  
    let fun_ids = List.filter is_not_stringlit (List.map (fun (id,_,_) -> id) fun_defs) in
    (*dbg (Printf.sprintf "fun_ids filtered (n=%d)" (List.length fun_ids));*)
  
    let prog_comp_env = BeeTypes.build_bcomposite_env' prog_types in
    (*dbg "build_bcomposite_env' done";*)
  
    let get_id = Camlcoq.intern_string in
    let prog_main = get_id (find_main_or_fallback prog) in
    (*dbg "prog_main set";*)
  
    (* extern names from efenv *)
    let external_ids =
      Beepl_ast_typechecker.Env.bindings ee
      |> List.map (fun (name, _) -> Camlcoq.intern_string name)
    in
  
    let filtered_fun_ids = List.filter (fun id -> not (is_stringlit_id id)) fun_ids in
    let prog_public =
      if List.mem prog_main filtered_fun_ids
      then filtered_fun_ids @ external_ids
      else prog_main :: filtered_fun_ids @ external_ids
    in
    (*dbg (Printf.sprintf "prog_public built (n=%d)" (List.length prog_public));*)
  
    {
      BeePL.prog_defs = prog_defs;
      BeePL.prog_public = prog_public;
      BeePL.prog_main = prog_main;
      BeePL.prog_types = prog_types;
      BeePL.prog_comp_env = prog_comp_env;
      BeePL.prog_ident_to_string = prog_ident_to_string;
    } 
    (*dbg "OK TRANSFORMED PROGRAM";*)
  
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