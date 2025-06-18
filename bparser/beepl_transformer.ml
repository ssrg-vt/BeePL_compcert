open Beepl_ast
open Beepl_parser
open Beepl_lexer
open Lexing

let typ_to_coq (t : typ) : string =
  match t with
  | Utype -> "Utype"
  | Vtype Tint32 -> "Vtype Tint32"
  | Vtype Tbool -> "Vtype Tbool"
  | Vtype Tlong -> "Vtype Tlong"

let effect_to_coq (eff : effect) : string =
  match eff with
  | Read s -> Printf.sprintf "Read \"%s\"" s
  | Write s -> Printf.sprintf "Write \"%s\"" s
  | Alloc s -> Printf.sprintf "Alloc \"%s\"" s
  | Io -> "Io"

let arg_to_coq (id, t) =
  Printf.sprintf "(\"_%s\", %s)" id (typ_to_coq t)

let rec expr_to_coq (e : expr) : string =
  match e with
  | Var id -> Printf.sprintf "Var \"%s\"" id
  | Const c ->
      (match c with
       | Cunit -> "Const Cunit"
       | Cbool b -> Printf.sprintf "Const (Cbool %b)" b
       | Cint32 i -> Printf.sprintf "Const (Cint32 %ld)" i
       | Clong l -> Printf.sprintf "Const (Clong %Ld)" l)
  | Let (id, t, e1, e2) ->
      Printf.sprintf "Bind (\"_%s\", %s, %s, %s)"
        id (typ_to_coq t) (expr_to_coq e1) (expr_to_coq e2)
  | If (e1, e2, e3) ->
      Printf.sprintf "Cond (%s, %s, %s)"
        (expr_to_coq e1) (expr_to_coq e2) (expr_to_coq e3)

let transform_function (Tfundecl (name, ret, eff, args, vars, body, is_ebpf)) =
  let arg_strs = List.map arg_to_coq args in
  let var_strs = List.map arg_to_coq vars in
  let coq_name = "f_" ^ name in
  Printf.sprintf
    "Definition %s : BeePL.function := {| \n  fn_return := %s;\n  fn_effect := %s;\n  fn_callconv := cc_default;\n  fn_args := %s;\n  fn_vars := %s;\n  fn_body := %s;\n  is_ebpf := %s\n|}.\n"
    coq_name
    (typ_to_coq ret)
    (effect_to_coq eff)
    (String.concat " :: " arg_strs ^ " :: nil")
    (String.concat " :: " var_strs ^ " :: nil")
    (expr_to_coq body)
    (if is_ebpf then "true" else "false")

let transform_program (prog : program) =
  List.map (function Internal f -> transform_function f) prog
  |> String.concat "\n\n"

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

let () =
  if Array.length Sys.argv < 2 then
    Printf.eprintf "Usage: %s <file.bpl>\n" Sys.argv.(0)
  else
    let program = parse_file Sys.argv.(1) in
    let output = transform_program program in
    print_endline "(* Generated BeePL Coq Function *)\n";
    print_endline output

let parse_and_transform_bpl (filename : string) : string =
      let program = parse_file filename in
      transform_program program
