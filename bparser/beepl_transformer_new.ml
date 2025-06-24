open Beepl_ast
open Beepl_parser
open Beepl_lexer
open Lexing
open Beepl_ast_typechecker
open Ctypes
open BeePL
open BeeTypes
open BinNums
open Integers
open Z


let string_to_char_list s =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (s.[i] :: acc)
  in
  aux (String.length s - 1) []


let collect_idents (prog : program) : string list =
  let idents = ref [] in
  let add_ident x = if not (List.mem x !idents) then idents := x :: !idents in
  let add_var (x, _) = add_ident x in
  let rec from_expr e =
    match e with
    | Var x -> add_ident x
    | Const _ -> ()
    | Let (x, _, e1, e2) -> add_ident x; from_expr e1; from_expr e2
    | If (e1, e2, e3) -> from_expr e1; from_expr e2; from_expr e3
  in
  let from_effect = function
    | Read s | Write s | Alloc s -> add_ident s
    | Io | Divergence -> ()
  in
  List.iter (fun top ->
    match top with
    | Internal (Tfundecl (name, _, effs, args, _, body), _)
    | EBPFInternal (Tfundecl (name, _, effs, args, _, body), _) ->
        add_ident name;
        List.iter from_effect effs;
        List.iter add_var args;
        from_expr body
    | StructDecl (sname, fields) ->
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
      let n = !counter in
      counter := n + 1;
      let rec int_to_pos = function
        | 1 -> Coq_xH
        | n when n mod 2 = 0 -> Coq_xO (int_to_pos (n / 2))
        | n -> Coq_xI (int_to_pos (n / 2))
        | _ -> failwith "int_to_pos: positive integers only"
      in
      let pos = int_to_pos n in
      map := (s, pos) :: !map;
      pos
  in
  List.iter (fun id -> ignore (get_ident id)) idents;
  (get_ident, List.map (fun (s, p) -> (p, s)) !map)

let rec transform_primitive_type (pt : Beepl_ast.primitive_type) : BeeTypes.primitive_type =
  match pt with
  | Tbool -> Tbool
  | Tint8 -> Tint (I8, Signed, noattr)
  | Tint16 -> Tint (I16, Signed, noattr)
  | Tint32 -> Tint (I32, Signed, noattr)
  | Tuint8 -> Tint (I8, Unsigned, noattr)
  | Tuint16 -> Tint (I16, Unsigned, noattr)
  | Tuint32 -> Tint (I32, Unsigned, noattr)
  | Tulong -> Tlong (Unsigned, noattr)
  | Tlong -> Tlong (Signed, noattr)

let rec transform_basic_type (get_id : string -> positive) (bt : btype) : BeeTypes.basic_type =
  match bt with
  | Bprim pt -> Bprim (transform_primitive_type pt)
  | Bstruct name -> Bstruct (get_id name, noattr)
  | Barray (pt, n) -> Barray (transform_primitive_type pt, Z.of_int n, noattr)

let rec transform_typ (get_id : string -> positive) (t : typ) : BeeTypes.coq_type =
  match t with
  | Utype -> Utype
  | Vtype pt -> Vtype (transform_primitive_type pt)
  | Ptr (Reftype (name, bt)) ->
      Ptrtype (Reftype (get_id name, transform_basic_type get_id bt, noattr))

let transform_effect (get_id : string -> positive) (eff : effect) : BeeTypes.effect_label =
  match eff with
  | Read s -> Read (get_id s)
  | Write s -> Write (get_id s)
  | Alloc s -> Alloc (get_id s)
  | Io -> Io
  | Divergence -> Divergence

let transform_effect_list get_id effs = List.map (transform_effect get_id) effs

let transform_constant (c : Beepl_ast.constant) : BeePL.constant =
  match c with
  | Cunit -> ConsUnit
  | Cbool b -> ConsBool b
  | Cint32 i -> ConsInt (Int.repr (Z.of_int32 i))
  | Clong l -> ConsLong (Int64.repr (Z.of_int64 l))

let rec transform_expr (get_id : string -> positive) (env : (string * typ) list) (e : expr) : BeePL.expr =
  let typ = infer_expr (list_to_env env) e in
  let t' = transform_typ get_id typ in
  match e with
  | Var x -> Var (get_id x, t')
  | Const c -> Const (transform_constant c, t')
  | Let (x, t, e1, e2) ->
      let e1' = transform_expr get_id env e1 in
      let env' = (x, t) :: env in
      let e2' = transform_expr get_id env' e2 in
      Bind (get_id x, transform_typ get_id t, e1', e2', t')
  | If (e1, e2, e3) ->
      let e1' = transform_expr get_id env e1 in
      let e2' = transform_expr get_id env e2 in
      let e3' = transform_expr get_id env e3 in
      Cond (e1', e2', e3', t')

let rec collect_vars (e : expr) : (string * typ) list =
  let unique_vars vars =
    List.fold_left (fun acc (x, t) ->
      if List.exists (fun (y, _) -> x = y) acc then acc else (x, t) :: acc
    ) [] vars
  in
  match e with
  | Var _ | Const _ -> []
  | Let (x, t, e1, e2) ->
      unique_vars ((x, t) :: collect_vars e1 @ collect_vars e2)
  | If (e1, e2, e3) ->
      unique_vars (collect_vars e1 @ collect_vars e2 @ collect_vars e3)

let transform_function (get_id : string -> positive) (Tfundecl (name, ret, eff, args, _, body) as fdecl) is_ebpf =
  let env = infer_fundecl fdecl in
  let fn_args = List.map (fun (id, t) -> (get_id id, transform_typ get_id t)) args in
  let fn_vars = List.map (fun (id, t) -> (get_id id, transform_typ get_id t)) (collect_vars body) in
  let fn_body = transform_expr get_id env body in
  {
    fn_return = transform_typ get_id ret;
    fn_effect = transform_effect_list get_id eff;
    fn_callconv = cc_default;
    fn_args;
    fn_vars;
    fn_body;
    is_ebpf;
  }

let transform_struct (get_id : string -> positive) (name : string) (fields : (string * typ) list) : bcomposite_definition =
  let members = List.map (fun (id, t) ->
      Member_plain (get_id id, transform_typ get_id t)
    ) fields in
  Bcomposite (get_id name, Struct, members, noattr)

let transform_toplevel (get_id : string -> positive) top =
  match top with
  | Internal ((Tfundecl (name, _, _, _, _, _) as f), section) ->
      `Fun (get_id name, Internal (transform_function get_id f false), section)
  | EBPFInternal ((Tfundecl (name, _, _, _, _, _) as f), section) ->
      `Fun (get_id name, Internal (transform_function get_id f true), section)
  | StructDecl (name, fields) ->
      `Struct (transform_struct get_id name fields)

let find_main_or_fallback prog : string =
  let is_main name = name = "main" in
  let extract_name = function
    | Internal (Tfundecl (name, _, _, _, _, _), _)
    | EBPFInternal (Tfundecl (name, _, _, _, _, _), _) -> Some name
    | _ -> None in
  let names = List.filter_map extract_name prog in
  match List.find_opt is_main names with
    | Some name -> name
    | None ->
      (match names with
        | fn :: _ -> fn
        | [] -> failwith "No function declarations found in the program")

let transform_program prog : BeePL.program =
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
      ((id, Gfun f), Option.map string_to_char_list section)
    ) fun_defs in

  let prog_public = List.map (fun (id, _, _) -> id) fun_defs in
  let prog_comp_env = build_bcomposite_env' prog_types in
  let prog_main = get_id (find_main_or_fallback prog) in

  {
    prog_defs;
    prog_public;
    prog_main;
    prog_types;
    prog_comp_env;
    prog_ident_to_string;
  }

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

let parse_and_transform_bpl (filename : string) : BeePL.program =
  let program = parse_file filename in
  transform_program program
