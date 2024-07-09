(*open Format*)
open Printf
open! Camlcoq
open AST
open PrintAST
open CminorSel 
open PrintOp

let rec list_of_list = function
  | Enil -> []
  | Econs(e,l) -> e::(list_of_list l)

let ident_name id = "'" ^ Camlcoq.extern_atom id ^ "'"


let rec expr n p = function
  | Evar id -> fprintf p "%s" (ident_name id)
  | Eop(op, l) -> print_operation (expr n) p (op,(list_of_list l))
  | Eload(chunk,a,l) -> fprintf p "%s[%a]" (name_of_chunk chunk) (print_addressing (expr n))  (a,(list_of_list l))
  | Econdition(ce,e1,e2) -> fprintf p "%a?%a:%a" (condexpr n) ce (expr n) e1 (expr n) e2
  | Elet(e1,e2) -> fprintf p "let $%i=%a in %a" n (expr n) e1 (expr (n+1)) e2
  | Eletvar n ->  fprintf  p "%i" (Nat.to_int n)
  | Ebuiltin(ef,l) -> ()
  | Eexternal(id,s,l) -> ()
and condexpr n p = function
  | CEcond(c,l) -> print_condition (expr n) p  (c,list_of_list l)
  | CEcondition(c1,c2,c3) -> fprintf p "%a?%a:%a" (condexpr n) c1 (condexpr n) c2  (condexpr n) c3
  | CElet(e,ce) -> fprintf p "let $%i = %a in %a" n (expr n) e (condexpr (n+1)) ce



let rec stmt p = function
  | Sskip -> fprintf p "/*skip*/"
  | Sassign(id,e) -> fprintf p "%s = %a" (ident_name id) (expr 0) e
  | Sstore(m,a,l,e) -> fprintf p "%s[%a] = %a" (name_of_chunk m) (print_addressing (expr 0)) (a,list_of_list l) (expr 0) e
  | Scall(o,s,a,args) -> ()
  | Stailcall(s,ei,args) -> ()
  | Sbuiltin(br,ef,args) -> ()
  | Sseq(s1,s2) -> fprintf p "%a;\n%a" stmt s1 stmt s2
  | Sifthenelse(c,s1,s2) -> fprintf p "if (%a) {%a}{%a}" (condexpr 0) c stmt s1 stmt s2
  | Sloop s -> fprintf p "loop{ %a }" stmt s
  | Sblock s -> fprintf p "{{ %a }}" stmt s
  | Sexit n ->  fprintf p "exit %d;" (Nat.to_int n)
  | Sswitch e -> ()
  | Sreturn None -> fprintf p "return;"
  | Sreturn (Some e) ->
      fprintf p "return %a;" (expr 0) e
  | Slabel(lbl, s1) ->
      fprintf p "%s:@ %a" (ident_name lbl) stmt s1  
  | Sgoto lbl ->
      fprintf p "goto %s;" (ident_name lbl)         

let rec print_varlist p (vars, first) =
  match vars with
  | [] -> ()
  | v1 :: vl ->
      if not first then fprintf p ", ";
      fprintf p "%s" (ident_name v1);
      print_varlist p (vl, false)

let print_sig p sg =
  List.iter
    (fun t -> fprintf p "%s -> " (name_of_type t))
    sg.sig_args;
  fprintf p "%s" (name_of_rettype sg.sig_res)

let print_function p id f =
  fprintf p "\"%s\"(%a) : %a "
            (extern_atom id)
            print_varlist (f.fn_params, true)
            print_sig f.fn_sig;
  fprintf p "{ ";
  let stksz = Z.to_int32 f.fn_stackspace in
  if stksz <> 0l then
    fprintf p "stack %ld;@ " stksz;
  if f.fn_vars <> [] then
    fprintf p "var %a; " print_varlist (f.fn_vars, true);
  stmt p f.fn_body;
  fprintf p "} "


let print_init_data p = function
  | Init_int8 i -> fprintf p "int8 %ld" (camlint_of_coqint i)
  | Init_int16 i -> fprintf p "int16 %ld" (camlint_of_coqint i)
  | Init_int32 i -> fprintf p "%ld" (camlint_of_coqint i)
  | Init_int64 i -> fprintf p "%LdLL" (camlint64_of_coqint i)
  | Init_float32 f -> fprintf p "float32 %.15F" (camlfloat_of_coqfloat f)
  | Init_float64 f -> fprintf p "%.15F" (camlfloat_of_coqfloat f)
  | Init_space i -> fprintf p "[%s]" (Z.to_string i)
  | Init_addrof(id,off) -> fprintf p "%ld(\"%s\")" (camlint_of_coqint off) (extern_atom id)

let rec print_init_data_list p = function
  | [] -> ()
  | [item] -> print_init_data p item
  | item::rest ->
      (print_init_data p item;
       fprintf p ",";
       print_init_data_list p rest)


let print_globvar p gv =
  if (gv.gvar_readonly) then
    fprintf p "readonly ";
  if (gv.gvar_volatile) then
    fprintf p "volatile ";
  fprintf p "{";
  print_init_data_list p gv.gvar_init;
  fprintf p "}"


let print_extfun p id ef =
  fprintf p "extern \"%s\" = %s : %a\n"
    (extern_atom id) (name_of_external ef) print_sig (ef_sig ef)

let print_globdef p (id, gd) =
  match gd with
  | Gfun(External ef) ->
      print_extfun p id ef
  | Gfun(Internal f) ->
      print_function p id f
  | Gvar gv ->
     fprintf p "var \"%s\" %a\n" (extern_atom id) print_globvar gv



let print_program p prog =
  fprintf p "@[<v 0>";
  if extern_atom prog.prog_main <> "main" then
    fprintf p "= \"%s\"\n" (extern_atom prog.prog_main);
  List.iter (print_globdef p) prog.prog_defs;
  fprintf p "@]@."


let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program  oc prog;
      close_out oc


