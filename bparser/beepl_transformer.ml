open Lexing
open Beepl_ast

(* Function to parse input file *)
let parse_file filename =
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try
    let ast = Beepl_parser.program Beepl_lexer.read lexbuf in
    close_in ic;
    ast
  with
  | Beepl_lexer.SyntaxError msg ->
    Printf.fprintf stderr "Syntax error: %s\n" msg;
    close_in ic;
    exit 1
  | Beepl_parser.Error ->
    let pos = lexbuf.lex_curr_p in
    Printf.fprintf stderr "Parse error at line %d, column %d\n"
      pos.pos_lnum (pos.pos_cnum - pos.pos_bol);
    close_in ic;
    exit 1

(* Create a hashtable to store variable declarations *)
let var_table = Hashtbl.create 100

(* Convert type to string for pretty printing
let rec string_of_type = function
  | TName s -> s
  | TRef t -> string_of_type t ^ " ref"
  | TArrow (args, ret) ->
    let args_str = String.concat " -> " (List.map string_of_type args) in
    args_str ^ " -> " ^ string_of_type ret
*)

(* Extract variable name and type from a pattern *)
let rec extract_vars_from_pattern pattern typ_opt location =
  match pattern with
  | PWildcard -> ()
  | PUnit -> ()
  | PIdent id ->
      if id <> "_" && id <> "" then
        Hashtbl.replace var_table id (id, typ_opt, location)
  | PAnnot (p, t) ->
      (* Pattern annotation overrides any external type annotation *)
      extract_vars_from_pattern p (Some t) location

(* Process top-level declarations *)
let rec process_toplevel tl =
  match tl with
  | TLLet (pattern, typ_opt, expr) ->
      extract_vars_from_pattern pattern typ_opt "top-level let";
      process_expr expr "top-level let"
  | TLFunc (name, params, ret_type, body) ->
      (* Create function type *)
      let func_type =
        match ret_type with
        | Some ret ->
            let param_types = List.map (fun (param_name, param_type) ->
              match param_name with
              | "" -> TName "unit"
              | _ -> (match param_type with
                      | Some t -> t
                      | None -> TName "unknown")
            ) params in
            Some (TArrow (param_types, ret))
        | None -> None
      in

      (* Add function to variable table *)
      Hashtbl.replace var_table name (name, func_type, "function declaration");

      (* Add function parameters *)
      List.iter (fun (param_name, param_type) ->
        if param_name <> "_" && param_name <> "" then
          Hashtbl.replace var_table param_name (param_name, param_type, "function parameter of " ^ name)
      ) params;

      (* Process function body *)
      process_expr body ("function " ^ name)
  | TLExpr expr ->
      process_expr expr "top-level expression"

(* Recursively process expressions to find variable declarations *)
and process_expr expr location =
  match expr with
  | EUnit | EInt32 _ | EVar _ -> ()
  | EApply (func, args) ->
      process_expr func location;
      List.iter (fun arg -> process_expr arg location) args
  | ELet (pattern, typ_opt, e1, e2) ->
      extract_vars_from_pattern pattern typ_opt ("let binding in " ^ location);
      process_expr e1 location;
      process_expr e2 location
  | ERef e | EDeref e ->
      process_expr e location
  | EAssign (e1, e2) ->
      process_expr e1 location;
      process_expr e2 location
  | EBlock exprs ->
      List.iter (fun e -> process_expr e location) exprs

let rec transform_type = function
  | TName "int32s" -> "tint32s"
  | TName "int32u" -> "tint32u"
  | TName "unit" -> "tunit"
  | TRef t ->
      (match t with
       | TName s -> "tr" ^ s
       | _ -> "tr" ^ transform_type t)
  | TArrow (_, _) -> "tfunc"
  | t -> transform_type t

let rec transform_expr ?(expected_type=None) expr var_table =
  match expr with
  | EUnit -> "tunit"
  | EInt32 n ->
      (* Use expected type if available, otherwise default to tint32s *)
      let typ = match expected_type with
                | Some t -> t
                | None -> "tint32s" in
      Printf.sprintf "(cint (Int.repr %s) %s)" n typ
  | EVar id ->
      let typ = try
        let (_, typ_opt, _) = Hashtbl.find var_table id in
        match typ_opt with
        | Some t -> transform_type t
        | None -> "tint32s"
      with Not_found -> "tint32s" in
      Printf.sprintf "(Var %s %s)" id typ
  | EApply (func, args) ->
      let func_str = transform_expr func var_table in
      let args_str = String.concat " :: " (List.map (fun arg -> transform_expr arg var_table) args) ^ " :: nil" in
      let ret_type_str = match expected_type with Some t -> t | None -> "tint32s" in (* Use expected type if available *)
      Printf.sprintf "(App %s (%s) %s)" func_str args_str ret_type_str
  | ELet (pattern, typ_opt, e1, e2) ->
      let var_name = match pattern with
                    | PIdent id -> id
                    | PAnnot (p, _) ->
                        (match p with
                          | PIdent id -> id
                          | _ -> "_")
                    | PWildcard -> "_"
                    | _ -> "_" in
      let var_type =
        try
          let (_, typ_opt_in_table, _) = Hashtbl.find var_table var_name in
          match typ_opt_in_table with
          | Some t -> transform_type t
          | None -> "tint32s"
        with Not_found -> "tint32s" in
      (* Pass the variable's type as expected_type when transforming e1 *)
      let val_expr = transform_expr ~expected_type:(Some var_type) e1 var_table in
      let body_expr = transform_expr e2 var_table in
      (* Use var_type instead of hardcoded tint32s *)
      Printf.sprintf "(Bind %s %s\n%s\n%s %s)" var_name var_type val_expr body_expr var_type
  | ERef e ->
      let expr_str = transform_expr e var_table in
      Printf.sprintf "(Prim Ref (%s :: nil) trint32s)" expr_str
  | EDeref e ->
      let expr_str = transform_expr e var_table in
      Printf.sprintf "(Prim Deref (%s :: nil) tint32s)" expr_str
  | EAssign (e1, e2) ->
      let lhs = transform_expr e1 var_table in
      let rhs = transform_expr e2 var_table in
      Printf.sprintf "(Prim Massgn (%s :: %s :: nil) tunit)" lhs rhs
  | EBlock exprs ->
      let exprs_str = List.map (fun e -> transform_expr e var_table) exprs in
      String.concat ";\n" exprs_str

let transform_function name params ret_type body var_table =
  (* Get the actual return type instead of hardcoding tint32s *)
  let return_type = match ret_type with
                    | Some t -> transform_type t
                    | None -> "tint32s" in
  let transformed_body = transform_expr body var_table in

  Printf.sprintf "Definition %s : BeePL.function := {|\n" name ^
  Printf.sprintf "                                   fn_return := %s;\n" return_type ^
  "                                   fn_effect := (Alloc mem_ident :: Read mem_ident :: Write mem_ident :: Read mem_ident :: nil);\n" ^
  "                                   fn_callconv := cc_default;\n" ^
  "                                   fn_args := nil;\n" ^
  "                                   fn_vars := ((_x, trint32s) :: nil);\n" ^
  "                                   fn_body := " ^ transformed_body ^ ";\n" ^
  "                                   is_ebpf := false|}."

let transform_program ast var_table =
  let result = ref [] in

  List.iter (fun toplevel ->
    match toplevel with
    | TLFunc (name, params, ret_type, body) ->
        (* Transform the function name by prepending "f_" *)
        let transformed_name = "f_" ^ name in
        let transformed = transform_function transformed_name params ret_type body var_table in
        result := transformed :: !result
    | _ -> () (* Skip other toplevel declarations *)
  ) ast;

  String.concat "\n\n" (List.rev !result)

(* Print the contents of the variable table
let print_var_table () =
  Printf.printf "Variable Declarations:\n";
  Printf.printf "=====================\n";
  let entries = Hashtbl.fold (fun _ entry acc -> entry :: acc) var_table [] in
  let sorted_entries = List.sort (fun (name1, _, _) (name2, _, _) -> String.compare name1 name2) entries in
  List.iter (fun (name, typ_opt, location) ->
    let type_str = match typ_opt with
      | Some t -> string_of_type t
      | None -> "unknown"
    in
    Printf.printf "Variable: %s\nType: %s\nDeclared in: %s\n\n"
      name type_str location
  ) sorted_entries
*)

let transform_input filename =
  let ast = parse_file filename in
  List.iter process_toplevel ast;
  transform_program ast var_table
