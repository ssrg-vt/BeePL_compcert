(*open Beepl_parser*)
open Beepl_lexer
open Lexing
(*open Beepl_ast_typechecker*)
open Ctypes
open BeePL_values
open BinNums
open AST

let string_to_char_list s =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (s.[i] :: acc)
  in
  aux (String.length s - 1) []

let rec int_to_positive = function
  | 1 -> Coq_xH
  | n when n mod 2 = 0 -> Coq_xO (int_to_positive (n / 2))
  | n -> Coq_xI (int_to_positive (n / 2))

let int_to_coq_z n =
  if n = 0 then Z0
  else if n > 0 then Zpos (int_to_positive n)
  else Zneg (int_to_positive (-n))

let collect_idents (prog : Beepl_ast.program) : string list =
  let idents = ref [] in
  let add_ident x = if not (List.mem x !idents) then idents := x :: !idents in
  let add_var (x, _) = add_ident x in
  let rec from_expr e =
    match e with
    | Beepl_ast.Var x -> add_ident x
    | Beepl_ast.Const _ -> ()
    | Beepl_ast.App (e1, args) ->
        from_expr e1;
        List.iter from_expr args
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
  ) prog;
  List.rev !idents


let create_ident_map (idents : string list) : (string -> positive) * (positive * string) list =
  let counter = ref 1 in
  let map = ref [] in
  let get_ident s =
    try List.assoc s !map
    with Not_found ->
      let pos =
        if s = "main" then Camlcoq.intern_string "main" (* crucial! *)
        else
          let n = !counter in
          counter := n + 1;
          let rec int_to_pos = function
            | 1 -> Coq_xH
            | n when n mod 2 = 0 -> Coq_xO (int_to_pos (n / 2))
            | n -> Coq_xI (int_to_pos (n / 2))
          in
          int_to_pos n
      in
      map := (s, pos) :: !map;
      pos in 
  List.iter (fun id -> ignore (get_ident id)) idents;
  (get_ident, List.map (fun (s, p) -> (p, s)) !map)

let transform_primitive_type (pt : Beepl_ast.ptype) : BeeTypes.primitive_type =
  match pt with
  | Beepl_ast.Tbool -> BeeTypes.Tbool
  | Beepl_ast.Tint8 -> BeeTypes.Tint (I8, Signed, noattr)
  | Beepl_ast.Tint16 -> BeeTypes.Tint (I16, Signed, noattr)
  | Beepl_ast.Tint32 -> BeeTypes.Tint (I32, Signed, noattr)
  | Beepl_ast.Tuint8 -> BeeTypes.Tint (I8, Unsigned, noattr)
  | Beepl_ast.Tuint16 -> BeeTypes.Tint (I16, Unsigned, noattr)
  | Beepl_ast.Tuint32 -> BeeTypes.Tint (I32, Unsigned, noattr)
  | Beepl_ast.Tulong -> BeeTypes.Tlong (Unsigned, noattr)
  | Beepl_ast.Tlong -> BeeTypes.Tlong (Signed, noattr)

let transform_basic_type (get_id : string -> positive) (bt : Beepl_ast.btype) : BeeTypes.basic_type =
  match bt with
  | Beepl_ast.Bprim pt -> BeeTypes.Bprim (transform_primitive_type pt)
  | Beepl_ast.Bstruct name -> BeeTypes.Bstruct (get_id name, noattr)
  | Beepl_ast.Barray (pt, n) -> BeeTypes.Barray (transform_primitive_type pt, int_to_coq_z n, noattr)

let transform_effect (get_id : string -> positive) (eff : Beepl_ast.effect) : BeeTypes.effect_label =
    match eff with
    | Beepl_ast.Read s -> BeeTypes.Read (get_id s)
    | Beepl_ast.Write s -> BeeTypes.Write (get_id s)
    | Beepl_ast.Alloc s -> BeeTypes.Alloc (get_id s)
    | Beepl_ast.Io -> BeeTypes.Io
    | Beepl_ast.Divergence -> BeeTypes.Divergence

let transform_effect_list get_id effs = List.map (transform_effect get_id) effs

let rec transform_typ (get_id : string -> positive) (t : Beepl_ast.typ) : BeeTypes.coq_type =
  match t with
  | Beepl_ast.Utype -> BeeTypes.Utype
  | Beepl_ast.Vtype pt -> BeeTypes.Vtype (transform_primitive_type pt)
  | Beepl_ast.Ptr (Beepl_ast.Reftype (name, bt)) ->
      BeeTypes.Ptrtype (BeeTypes.Reftype (get_id name, transform_basic_type get_id bt, noattr))
  | Beepl_ast.Ftype (args, effs, ret) -> 
      let args' = List.map (fun t -> (transform_typ get_id t)) args in
      let effs' = transform_effect_list get_id effs in
      let ret' = transform_typ get_id ret in
      BeeTypes.Ftype (args', effs', ret')
let transform_constant (c : Beepl_ast.const) (typ : Beepl_ast.typ) : BeePL_values.constant =
  match typ, c with
  | Beepl_ast.Vtype Beepl_ast.Tint32, Beepl_ast.Cint32 i ->
      ConsInt (Integers.Int.repr (int_to_coq_z (Int32.to_int i)))
  | Beepl_ast.Vtype Beepl_ast.Tlong, Beepl_ast.Clong l ->
      ConsLong (Integers.Int64.repr (int_to_coq_z (Int64.to_int l)))
  | Beepl_ast.Vtype Beepl_ast.Tbool, Beepl_ast.Cbool b ->
      ConsBool b
  | Beepl_ast.Utype, Beepl_ast.Cunit ->
      ConsUnit
  | _, _ ->
      failwith "Constant type mismatch or unsupported constant"
      

let rec transform_expr (get_id : string -> positive) (env : (string * Beepl_ast.typ) list) (e : Beepl_ast.expr) : BeePL.expr =
  let typ = Beepl_ast_typechecker.infer_expr (Beepl_ast_typechecker.list_to_env env) e in
  let t' = transform_typ get_id typ in
  match e with
  | Beepl_ast.Var x -> BeePL.Var (get_id x, t')
  | Beepl_ast.Const c -> 
    BeePL.Const (transform_constant c typ, t')
  | Beepl_ast.App (e1, args) ->
      let e1' = transform_expr get_id env e1 in
      let args' = List.map (transform_expr get_id env) args in
      BeePL.App (e1', args', t')
  | Beepl_ast.Let (x, t, e1, e2) ->
      let e1' = transform_expr get_id env e1 in
      let env' = (x, t) :: env in
      let e2' = transform_expr get_id env' e2 in
      BeePL.Bind (get_id x, transform_typ get_id t, e1', e2', t')
  | Beepl_ast.If (e1, e2, e3) ->
      let e1' = transform_expr get_id env e1 in
      let e2' = transform_expr get_id env e2 in
      let e3' = transform_expr get_id env e3 in
      BeePL.Cond (e1', e2', e3', t')

let rec collect_vars (e : Beepl_ast.expr) : (string * Beepl_ast.typ) list =
  let unique_vars vars =
    List.fold_left (fun acc (x, t) ->
      if List.exists (fun (y, _) -> x = y) acc then acc else (x, t) :: acc
    ) [] vars
  in
  match e with
  | Beepl_ast.Var _ | Beepl_ast.Const _ -> []
  | Beepl_ast.Let (x, t, e1, e2) ->
      unique_vars ((x, t) :: collect_vars e1 @ collect_vars e2)
  | Beepl_ast.App (e1, args) ->
      unique_vars (collect_vars e1 @ List.flatten (List.map collect_vars args))
  | Beepl_ast.If (e1, e2, e3) ->
      unique_vars (collect_vars e1 @ collect_vars e2 @ collect_vars e3)

let transform_function (get_id : string -> positive) (Beepl_ast.Tfundecl (name, ret, eff, args, _, body) as fdecl) is_ebpf =
  let env = Beepl_ast_typechecker.infer_fundecl fdecl in
  let fn_args = List.map (fun (id, t) -> (get_id id, transform_typ get_id t)) args in
  let fn_vars = List.map (fun (id, t) -> (get_id id, transform_typ get_id t)) (collect_vars body) in
  let fn_body = transform_expr get_id env body in
  {
    BeePL.fn_return = transform_typ get_id ret;
    BeePL.fn_effect = transform_effect_list get_id eff;
    BeePL.fn_callconv = cc_default;
    BeePL.fn_args = fn_args;
    BeePL.fn_vars = fn_vars;
    BeePL.fn_body = fn_body;
    BeePL.is_ebpf = is_ebpf;
  }

let transform_struct (get_id : string -> positive) (name : string) (fields : (string * Beepl_ast.typ) list) : BeeTypes.bcomposite_definition =
  let members = List.map (fun (id, t) ->
      BeeTypes.Member_plain (get_id id, transform_typ get_id t)
    ) fields in
  BeeTypes.Bcomposite (get_id name, Struct, members, noattr)

let transform_toplevel (get_id : string -> positive) top =
  match top with
  | Beepl_ast.Internal ((Beepl_ast.Tfundecl (name, _, _, _, _, _) as f), section) ->
      `Fun (get_id name, BeePL.Internal (transform_function get_id f false), section)
  | Beepl_ast.EBPFInternal ((Beepl_ast.Tfundecl (name, _, _, _, _, _) as f), section) ->
      `Fun (get_id name, BeePL.Internal (transform_function get_id f true), section)
  | Beepl_ast.StructDecl (name, fields) ->
      `Struct (transform_struct get_id name fields)
      
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
      
let transform_program prog : BeePL.program =
let prog = reorder_program prog in  
let idents = collect_idents prog in
let get_id, ident_to_string_list = create_ident_map idents in
let prog_ident_to_string = List.map (fun (p, s) -> (p, string_to_char_list s)) ident_to_string_list in

let transformed_decls = List.map (transform_toplevel get_id) prog in

let prog_types =
    List.filter_map (function `Struct s -> Some s | `Fun _ -> None) transformed_decls in

let fun_defs =
    List.filter_map (function `Fun (id, f, sec) -> Some (id, f, sec) | `Struct _ -> None) transformed_decls in

let prog_defs =
    List.map (fun (id, f, section) ->
    let sec =
      match section with
      | Some s when String.length s > 8 && String.sub s 0 8 = "#section" ->
          (* extract and quote the name *)
          let raw = String.trim (String.sub s 8 (String.length s - 8)) in
          Some (string_to_char_list ("\"" ^ raw ^ "\""))
      | Some s -> Some (string_to_char_list ("\"" ^ s ^ "\""))
      | None -> None
    in
    ((id, Gfun f), sec)) fun_defs in

let prog_comp_env = BeeTypes.build_bcomposite_env' prog_types in
let prog_main = get_id (find_main_or_fallback prog) in
let prog_public =
let ids = List.map (fun (id, _, _) -> id) fun_defs in
    if List.mem prog_main ids then ids else prog_main :: ids in 

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
