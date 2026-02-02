(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Printf
open Commandline
open Clflags
open CommonOptions
open Timing
open Driveraux
open Frontend
open Assembler
open Linker
open Diagnostics

(* Debug: dump Csyntax program to a .debug.compcert.c file *)
(*let debug_dump_csyntax_public (p : Csyntax.program) =
  prerr_endline "[DEBUG] Public idents in Csyntax.prog_public:";
  List.iter
    (fun id ->
       let name =
         try Hashtbl.find Camlcoq.string_of_atom id
         with Not_found ->
           Printf.sprintf "<atom %d>" (Camlcoq.P.to_int id)
       in
       prerr_endline ("  " ^ name))
    p.Ctypes.prog_public;
  prerr_endline "[DEBUG] End public idents.";
  flush stderr

let debug_dump_csyntax_to_file sourcename (p : Csyntax.program) =
  let debug_name = output_filename sourcename ~suffix:".debug.compcert.c" in
  let oc = open_out debug_name in
  let fmt = Format.formatter_of_out_channel oc in
  PrintCsyntax.print_program fmt p;
  Format.pp_print_flush fmt ();
  close_out oc;
  prerr_endline ("[DEBUG] Wrote Csyntax dump to: " ^ debug_name);
  flush stderr

(* Debug: print list of globals with their string names *)
let debug_dump_csyntax_globals (p : Csyntax.program) =
  prerr_endline "[DEBUG] Globals in Csyntax.prog_defs:";
  List.iter
    (fun (id, gd) ->
       let name =
         try Hashtbl.find Camlcoq.string_of_atom id
         with Not_found ->
           Printf.sprintf "<atom %d>" (Camlcoq.P.to_int id)
       in
       let kind =
         match gd with
         | AST.Gfun _ -> "fun"
         | AST.Gvar _ -> "var"
       in
       prerr_endline (Printf.sprintf "  %s %s" kind name))
    p.Ctypes.prog_defs;
  prerr_endline "[DEBUG] End of globals.";
  flush stderr

let debug_find_missing_public (p : Csyntax.program) =
  let defs_tbl = Hashtbl.create 251 in
  List.iter (fun (id, _gd) -> Hashtbl.replace defs_tbl id true) p.Ctypes.prog_defs;

  let missing =
    List.filter (fun id -> not (Hashtbl.mem defs_tbl id)) p.Ctypes.prog_public
  in

  if missing <> [] then begin
    prerr_endline "[DEBUG] prog_public contains ids not present in prog_defs:";
    List.iter (fun id ->
      let name =
        try Hashtbl.find Camlcoq.string_of_atom id
        with Not_found -> Printf.sprintf "<atom %d>" (Camlcoq.P.to_int id)
      in
      prerr_endline ("  " ^ name)
    ) missing;
    prerr_endline "[DEBUG] end missing-public list.";
    flush stderr
  end else begin
    prerr_endline "[DEBUG] All prog_public ids exist in prog_defs.";
    flush stderr
  end

let defs_id_set (p : Csyntax.program) =
  let tbl = Hashtbl.create 251 in
  List.iter (fun (id, _gd) -> Hashtbl.replace tbl id true) p.Ctypes.prog_defs;
  tbl

(* Collect locals (params + locals) so we can distinguish locals from globals. *)
let locals_of_function fn =
  let tbl = Hashtbl.create 97 in
  List.iter (fun (id, _ty) -> Hashtbl.replace tbl id ()) fn.Csyntax.fn_params;
  List.iter (fun (id, _ty) -> Hashtbl.replace tbl id ()) fn.Csyntax.fn_vars;
  tbl

let rec collect_expr_global_refs (acc : AST.ident list ref) (locals : (AST.ident, unit) Hashtbl.t) (e : Csyntax.expr) =
  match e with
  | Csyntax.Eval _ -> ()
  | Csyntax.Evar (id, _t) ->
      (* Only treat it as a global ref if it is NOT a local. *)
      if not (Hashtbl.mem locals id) then acc := id :: !acc
  | Csyntax.Efield (a1, _f, _t) -> collect_expr_global_refs acc locals a1
  | Csyntax.Evalof (l, _t) -> collect_expr_global_refs acc locals l
  | Csyntax.Ederef (a1, _t) -> collect_expr_global_refs acc locals a1
  | Csyntax.Eaddrof (a1, _t) -> collect_expr_global_refs acc locals a1
  | Csyntax.Eunop (_op, a1, _t) -> collect_expr_global_refs acc locals a1
  | Csyntax.Ebinop (_op, a1, a2, _t) ->
      collect_expr_global_refs acc locals a1;
      collect_expr_global_refs acc locals a2
  | Csyntax.Ecast (a1, _t) -> collect_expr_global_refs acc locals a1
  | Csyntax.Eseqand (a1, a2, _t)
  | Csyntax.Eseqor (a1, a2, _t)
  | Csyntax.Ecomma (a1, a2, _t) ->
      collect_expr_global_refs acc locals a1;
      collect_expr_global_refs acc locals a2
  | Csyntax.Econdition (a1, a2, a3, _t) ->
      collect_expr_global_refs acc locals a1;
      collect_expr_global_refs acc locals a2;
      collect_expr_global_refs acc locals a3
  | Csyntax.Esizeof _ -> ()
  | Csyntax.Ealignof _ -> ()
  | Csyntax.Eassign (l, r, _t) -> 
      collect_expr_global_refs acc locals l;
      collect_expr_global_refs acc locals r
  | Csyntax.Eassignop (_op, l, r, _t', _t) ->
      collect_expr_global_refs acc locals l;
      collect_expr_global_refs acc locals r
  | Csyntax.Epostincr (_id, l, _t) ->
      collect_expr_global_refs acc locals l
  | Csyntax.Ecall (r1, rargs, _t) ->
      collect_expr_global_refs acc locals r1;
      collect_exprlist_global_refs acc locals rargs
  | Csyntax.Ebuiltin (_ef, _tyargs, rargs, _t) ->
      collect_exprlist_global_refs acc locals rargs
  | Csyntax.Eloc _ -> ()
  | Csyntax.Eparen (r, _t', _t) -> collect_expr_global_refs acc locals r

and collect_exprlist_global_refs (acc : AST.ident list ref) (locals : (AST.ident, unit) Hashtbl.t) (el : Csyntax.exprlist) =
  match el with
  | Csyntax.Enil -> ()
  | Csyntax.Econs (r1, rl) ->
      collect_expr_global_refs acc locals r1;
      collect_exprlist_global_refs acc locals rl

let rec collect_stmt_global_refs (acc : AST.ident list ref) (locals : (AST.ident, unit) Hashtbl.t) (s : Csyntax.statement) =
  match s with
  | Csyntax.Sskip -> ()
  | Csyntax.Sdo e -> collect_expr_global_refs acc locals e
  | Csyntax.Ssequence (s1, s2) ->
      collect_stmt_global_refs acc locals s1;
      collect_stmt_global_refs acc locals s2
  | Csyntax.Sifthenelse (e, s1, s2) ->
      collect_expr_global_refs acc locals e;
      collect_stmt_global_refs acc locals s1;
      collect_stmt_global_refs acc locals s2
  | Csyntax.Swhile (e, s1)
  | Csyntax.Sdowhile (e, s1) ->
      collect_expr_global_refs acc locals e;
      collect_stmt_global_refs acc locals s1
  | Csyntax.Sfor (s1, e, s2, s3) ->
      collect_stmt_global_refs acc locals s1;
      collect_expr_global_refs acc locals e;
      collect_stmt_global_refs acc locals s2;
      collect_stmt_global_refs acc locals s3
  | Csyntax.Sbreak -> ()
  | Csyntax.Scontinue -> ()
  | Csyntax.Sreturn None -> ()
  | Csyntax.Sreturn (Some e) -> collect_expr_global_refs acc locals e
  | Csyntax.Sswitch (e, cases) ->
      collect_expr_global_refs acc locals e;
      collect_lblstmt_global_refs acc locals cases
  | Csyntax.Slabel (_lbl, s1) -> collect_stmt_global_refs acc locals s1
  | Csyntax.Sgoto _ -> ()

and collect_lblstmt_global_refs (acc : AST.ident list ref) (locals : (AST.ident, unit) Hashtbl.t) (ls : Csyntax.labeled_statements) =
  match ls with
  | Csyntax.LSnil -> ()
  | Csyntax.LScons (_lbl, s, rest) ->
      collect_stmt_global_refs acc locals s;
      collect_lblstmt_global_refs acc locals rest

let debug_find_undefined_references (p : Csyntax.program) =
  let defs_tbl = Hashtbl.create 251 in
  List.iter (fun (id, _gd) -> Hashtbl.replace defs_tbl id true) p.Ctypes.prog_defs;

  let refs = ref [] in

  List.iter
  (fun (_id, gd) ->
    match gd with
    | AST.Gfun (Ctypes.Internal f) ->
        let locals = locals_of_function f in
        collect_stmt_global_refs refs locals f.Csyntax.fn_body
    | _ -> ())
  p.Ctypes.prog_defs;

  (* uniq *)
  let seen = Hashtbl.create 251 in
  let uniq =
    List.filter
      (fun id ->
        if Hashtbl.mem seen id then false else (Hashtbl.add seen id true; true))
      !refs
  in

  let missing = List.filter (fun id -> not (Hashtbl.mem defs_tbl id)) uniq in

  if missing = [] then
    prerr_endline "[DEBUG] No undefined Evar references found in function bodies."
  else begin
    prerr_endline "[DEBUG] Undefined Evar references found:";
    List.iter
      (fun id ->
        let name =
          try Hashtbl.find Camlcoq.string_of_atom id
          with Not_found -> Printf.sprintf "<atom %d>" (Camlcoq.P.to_int id)
        in
        prerr_endline ("  " ^ name))
      missing;
    prerr_endline "[DEBUG] End undefined references."
  end;
  flush stderr

let show_atom (id : AST.ident) =
  try Hashtbl.find Camlcoq.string_of_atom id
  with Not_found -> Printf.sprintf "<atom %d>" (Camlcoq.P.to_int id)

let ptree_iter (f : Maps.PTree.elt -> 'a -> unit) (t : 'a Maps.PTree.t) : unit =
  ignore (Maps.PTree.fold (fun acc k v -> f k v; acc) t ())

let rec string_of_type (t : Ctypes.coq_type) : string =
  match t with
  | Ctypes.Tvoid -> "void"

  | Ctypes.Tint (sz, sg, _attr) ->
      let szs =
        match sz with
        | Ctypes.I8 -> "i8"
        | Ctypes.I16 -> "i16"
        | Ctypes.I32 -> "i32"
        | Ctypes.IBool -> "bool"
      in
      let sgs = match sg with Ctypes.Signed -> "s" | Ctypes.Unsigned -> "u" in
      sgs ^ szs

  | Ctypes.Tlong (sg, _attr) ->
      (match sg with Ctypes.Signed -> "slong" | Ctypes.Unsigned -> "ulong")

  | Ctypes.Tfloat (fsz, _attr) ->
      (match fsz with Ctypes.F32 -> "f32" | Ctypes.F64 -> "f64")

  | Ctypes.Tpointer (t1, _attr) ->
      (string_of_type t1) ^ "*"

  | Ctypes.Tarray (t1, sz, _attr) ->
      Printf.sprintf "%s[%s]" (string_of_type t1) (Camlcoq.Z.to_string sz)

  | Ctypes.Tfunction (_args, _res, _cc) ->
      "fn(...)"

  | Ctypes.Tstruct (id, _attr) ->
      "struct " ^ show_atom id

  | Ctypes.Tunion (id, _attr) ->
      "union " ^ show_atom id


let pp_typ (t : Ctypes.coq_type) =
  Format.asprintf "%s" (string_of_type t)

let show_atom (id : AST.ident) =
  try Hashtbl.find Camlcoq.string_of_atom id
  with Not_found -> Printf.sprintf "<atom %d>" (Camlcoq.P.to_int id)

let show_su = function
  | Ctypes.Struct -> "struct"
  | Ctypes.Union  -> "union"

let show_intsize = function
  | Ctypes.I8  -> "I8"
  | Ctypes.I16 -> "I16"
  | Ctypes.I32 -> "I32"
  | Ctypes.IBool -> "IBool"

let show_signedness = function
  | Ctypes.Signed   -> "signed"
  | Ctypes.Unsigned -> "unsigned"

let debug_dump_composites (p : Csyntax.program) =
  prerr_endline "[DEBUG] Composites in prog_types:";
  List.iter
    (fun (co : Ctypes.composite_definition) ->
      match co with
      | Ctypes.Composite (cid, su, members, _attr) ->
          let su_str =
            match su with Ctypes.Struct -> "struct" | Ctypes.Union -> "union"
          in
          prerr_endline (Printf.sprintf "  %s %s {" su_str (show_atom cid));
          List.iter
            (fun (m : Ctypes.member) ->
              match m with
              | Ctypes.Member_plain (fid, _ty) ->
                  prerr_endline (Printf.sprintf "    field %s" (show_atom fid))
              | Ctypes.Member_bitfield (fid, sz, sg, _a, width, padding) ->
                  prerr_endline
                    (Printf.sprintf
                       "    bitfield %s sz=%s sg=%s width=%s padding=%b"
                       (show_atom fid)
                       (show_intsize sz)
                       (show_signedness sg)
                       (Camlcoq.Z.to_string width)
                       padding))
            members;
          prerr_endline "  }"
    )
    p.Ctypes.prog_types;
  prerr_endline "[DEBUG] End composites.";
  flush stderr

let show_id id =
  let name =
    try Hashtbl.find Camlcoq.string_of_atom id
    with Not_found -> "<no-name>"
  in
  Printf.sprintf "%s (atom=%d)" name (Camlcoq.P.to_int id)

let debug_dump_function_locals (p : Csyntax.program) =
  prerr_endline "[DEBUG] Function params/locals:";
  List.iter
    (fun (gid, gd) ->
      match gd with
      | AST.Gfun (Ctypes.Internal f) ->
          prerr_endline ("  function " ^ show_id gid);
          prerr_endline "    params:";
          List.iter (fun (id, _ty) -> prerr_endline ("      " ^ show_id id))
            f.Csyntax.fn_params;
          prerr_endline "    locals:";
          List.iter (fun (id, _ty) -> prerr_endline ("      " ^ show_id id))
            f.Csyntax.fn_vars;
      | _ -> ())
    p.Ctypes.prog_defs;
  flush stderr *)

(* Name used for version string etc. *)
let tool_name = "C verified compiler"

(* Optional sdump suffix *)
let sdump_suffix = ref ".json"

let num_bpl_files = ref 0

let nolink () =
  !option_c || !option_S || !option_E || !option_interp || not Configuration.has_linking_step

let object_filename sourcename =
  if nolink () then
    output_filename ~final:(!option_c || not Configuration.has_linking_step) sourcename ~suffix:".o"
  else
    tmp_file ".o"

(* Helper to apply BPF mapping *)
let apply_bpf_map_replacements asm_filename =
  (* Resolve path relative to the ccomp executable location *)
  let bin_dir = Filename.dirname Sys.executable_name in
  let map_file = Filename.concat (Filename.concat bin_dir "ebpf") "bpfHelperMap.json" in

  if Sys.file_exists map_file then begin
    try
      (* 1. Read the Map File *)
      let ic = open_in map_file in
      let content = really_input_string ic (in_channel_length ic) in
      close_in ic;

      (* 2. Parse JSON (Simple Regex approach for flat { "key": int } structure) 
         Matches: "key" : value *)
      let regex = Str.regexp "\"\\([^\"]+\\)\"[ \t\n\r]*:[ \t\n\r]*\\([0-9]+\\)" in
      let rec parse_mappings pos acc =
        try
          let _ = Str.search_forward regex content pos in
          let key = Str.matched_group 1 content in
          let value = Str.matched_group 2 content in
          parse_mappings (Str.match_end()) ((key, value) :: acc)
        with Not_found -> acc
      in
      let mappings = parse_mappings 0 [] in

      (* 3. Read the ASM File *)
      let ic_asm = open_in asm_filename in
      let lines = ref [] in
      try
        while true do lines := input_line ic_asm :: !lines done
      with End_of_file -> close_in ic_asm;
      let asm_lines = List.rev !lines in

      (* 4. Replace and Write back *)
      let oc_asm = open_out asm_filename in
      List.iter (fun line ->
        let new_line = List.fold_left (fun l (k, v) ->
          (* Use Str.regexp_string to treat key as literal text, not regex
          Str.global_replace (Str.regexp_string k) v l *)
          let pattern = Str.regexp ("call[ \t]+bpf_" ^ Str.quote k) in
          Str.global_replace pattern ("call " ^ v) l
        ) line mappings in
        output_string oc_asm (new_line ^ "\n")
      ) asm_lines;
      close_out oc_asm;

      ()
    with e ->
      Printf.eprintf "Error processing -bpfmap: %s\n" (Printexc.to_string e)
  end else begin
    Printf.eprintf "Warning: -bpfmap specified but '%s' not found.\n" map_file
  end


(* From CompCert C AST to asm *)

let compile_c_file sourcename ifile ofile =
  (* Prepare to dump Clight, RTL, etc, if requested *)
  let set_dest dst opt ext =
    dst := if !opt then Some (output_filename sourcename ~suffix:ext)
      else None in
  set_dest Cprint.destination option_dparse ".parsed.c";
  set_dest PrintCsyntax.destination option_dcmedium ".compcert.c";
  set_dest PrintClight.destination option_dclight ".light.c";
  set_dest PrintCminor.destination option_dcminor ".cm";
  set_dest PrintCminorSel.destination option_dcminorsel ".cms";
  set_dest PrintRTL.destination option_drtl ".rtl";
  set_dest Regalloc.destination_alloctrace option_dalloctrace ".alloctrace";
  set_dest PrintLTL.destination option_dltl ".ltl";
  set_dest PrintMach.destination option_dmach ".mach";
  set_dest AsmToJSON.destination option_sdump !sdump_suffix;
  (* Parse C file *)
  let csyntax = parse_c_file sourcename ifile in

  (* Convert to Asm *)
  (*let asm =
    match Compiler.apply_partial
               (Compiler.transf_c_program csyntax)
               Asmexpand.expand_program with
    | Errors.OK asm ->
        asm
    | Errors.Error msg ->
        let loc = file_loc sourcename in
        fatal_error loc "error during transf_c_program: %a"  print_error msg in
  (* Dump Asm in binary and JSON format *)
  AsmToJSON.print_if asm sourcename;
  (* Print Asm in text form *)
  let oc = open_out ofile in
  PrintAsm.print_program oc asm;
  close_out oc*)

  let asm =
    match Compiler.apply_partial
            (Compiler.transf_c_program csyntax)
            Asmexpand.expand_program with
    | Errors.OK asm -> asm
    | Errors.Error msg ->
        let loc = file_loc sourcename in
        fatal_error loc
          "error during transf_c_program: %a"
          print_error msg
  in

  AsmToJSON.print_if asm sourcename;
  let oc = open_out ofile in
  PrintAsm.print_program oc asm;
  close_out oc;
  if !option_bpfmap then apply_bpf_map_replacements ofile

(* The BeePL compiler returns information on which identifiers should be placed
   in specific sections of the binary ELF file. CompCert requires that information
   be placed in decl_atom *)
let populate_decl_atom (section_info : (AST.ident * BeePL_Csyntax.csyntax_atom_info) list) =
    List.iter (fun (id, info) ->

    let storage : C.storage = 
      match info.BeePL_Csyntax.a_storage with
      | BeePL_Csyntax.Storage_default -> C.Storage_default
      | BeePL_Csyntax.Storage_extern -> C.Storage_extern
      | BeePL_Csyntax.Storage_static -> C.Storage_static
      | BeePL_Csyntax.Storage_auto -> C.Storage_auto
      | BeePL_Csyntax.Storage_register -> C.Storage_register
    in

    let defined : bool = 
     info.BeePL_Csyntax.a_defined
    in  

    let size : int64 option =
      match info.BeePL_Csyntax.a_size with
      | Some i -> Some (Camlcoq.camlint64_of_coqint i)
      | None -> None
    in

    let alignment : int option =
      match info.BeePL_Csyntax.a_alignment with
      | Some i -> Some (Camlcoq.Z.to_int i)
      | None -> None
    in

    let sec_list : Sections.section_name list =
      List.map
        (fun (sec : BeePL_Csyntax.section_name) ->
           match sec with
           | BeePL_Csyntax.Section_literal i ->
               Sections.Section_literal (Camlcoq.Z.to_int i)
           | BeePL_Csyntax.Section_user (name, writable, executable) ->
               Sections.Section_user
                 (Camlcoq.camlstring_of_coqstring name, writable, executable)
           | BeePL_Csyntax.Section_jumptable ->
               Sections.Section_jumptable)
        info.BeePL_Csyntax.a_section
    in

    let access : Sections.access_mode =
      match info.BeePL_Csyntax.a_access with
      | BeePL_Csyntax.Access_default -> Sections.Access_default
      | BeePL_Csyntax.Access_near -> Sections.Access_near
      | BeePL_Csyntax.Access_far -> Sections.Access_far
    in

    let inline : C2C.inline_status =
      match info.BeePL_Csyntax.a_inline with
      | BeePL_Csyntax.No_specifier -> C2C.No_specifier
      | BeePL_Csyntax.Noinline -> C2C.Noinline
      | BeePL_Csyntax.Inline -> C2C.Inline
    in

    let loc : C.location =
      let (filename, line_number) = info.BeePL_Csyntax.a_loc in
      (Camlcoq.camlstring_of_coqstring filename, Camlcoq.Z.to_int line_number)
    in

    Hashtbl.add C2C.decl_atom id { 
      C2C.a_storage = storage;
      C2C.a_defined = defined;
      C2C.a_size = size;
      C2C.a_alignment = alignment;
      C2C.a_sections = sec_list;
      C2C.a_access = access;
      C2C.a_inline = inline;
      C2C.a_loc = loc 
    }
  ) section_info

  let compile_bpl_file sourcename ofile beepl_program =
    (* Prepare to dump Clight, RTL, etc, if requested *)
    let set_dest dst opt ext =
      dst := if !opt then Some (output_filename sourcename ~suffix:ext)
        else None in
    set_dest Cprint.destination option_dparse ".parsed.c";
    set_dest PrintCsyntax.destination option_dcmedium ".compcert.c";
    set_dest PrintClight.destination option_dclight ".light.c";
    set_dest PrintCminor.destination option_dcminor ".cm";
    set_dest PrintCminorSel.destination option_dcminorsel ".cms";
    set_dest PrintRTL.destination option_drtl ".rtl";
    set_dest Regalloc.destination_alloctrace option_dalloctrace ".alloctrace";
    set_dest PrintLTL.destination option_dltl ".ltl";
    set_dest PrintMach.destination option_dmach ".mach";
    set_dest AsmToJSON.destination option_sdump !sdump_suffix;
  
    (* Typecheck BeePL program *)
    if !option_typecheck then begin
      let typecheck_result = BeePL_typechecker.type_check_program beepl_program in
      match typecheck_result with
      | Errors.OK s ->
          let str = Camlcoq.camlstring_of_coqstring s in
          Printf.printf "Typecheck result: %s\n" str
      | Errors.Error msg ->
          let loc = file_loc sourcename in
          fatal_error loc
            "error during BeePL_typechecker.type_check_program: %a"
            print_error msg
    end;
  
    (* BeePL -> Csyntax *)
    let beepl = Compiler.transf_beepl_program_csyntax beepl_program in
    let (csyntax, ident_to_string, section_info) =
      match beepl with
      | Errors.OK ((csyntax, ident_to_string), section_info) ->
          (csyntax, ident_to_string, section_info)
      | Errors.Error msg ->
          let loc = file_loc sourcename in
          fatal_error loc
            "error during transf_beepl_program_csyntax: %a"
            print_error msg
    in
    (*prerr_endline "===== [DEBUG] After BeePL -> Csyntax =====";
    debug_dump_csyntax_globals csyntax;
    debug_dump_csyntax_public csyntax;
    debug_dump_composites csyntax;
    debug_find_undefined_references csyntax;
    debug_dump_function_locals csyntax;
    flush stderr;
    
    (* Register atoms: numeric ids <-> names *)
    List.iter
      (fun (id, charlist) ->
         let s : string = String.concat "" (List.map (String.make 1) charlist) in
         Hashtbl.add Camlcoq.string_of_atom id s;
         Hashtbl.add Camlcoq.atom_of_string s id)
      ident_to_string;
    let show_atom id =
      try Hashtbl.find Camlcoq.string_of_atom id
      with Not_found -> Printf.sprintf "<atom %d>" (Camlcoq.P.to_int id)
      in
      prerr_endline ("[DEBUG] prog_main atom = " ^ show_atom csyntax.Ctypes.prog_main);
      flush stderr;*)
  
    (* Section / storage info for globals *)
    populate_decl_atom section_info;
  
    (* The BeePL compiler does not add CompCert's helper functions so that must be done here *)
    let gl = C2C.add_helper_functions csyntax.Ctypes.prog_defs in
    let updated_csyntax =
      { csyntax with
        Ctypes.prog_defs   = gl;
        Ctypes.prog_public = (*main_id ::*) C2C.public_globals gl }
    in
    (*prerr_endline "===== [DEBUG] After add_helper_functions / public_globals =====";
    debug_dump_composites updated_csyntax;
    debug_dump_csyntax_globals updated_csyntax;
    debug_dump_csyntax_public updated_csyntax;
    debug_find_undefined_references csyntax;
    debug_dump_function_locals csyntax;
    prerr_endline ("[DEBUG] updated prog_main atom = " ^ show_atom updated_csyntax.Ctypes.prog_main);
    flush stderr;*)
  
    PrintCsyntax.print_if updated_csyntax;
  
    (* Convert to Asm 
    let asm =
      match Compiler.apply_partial
              (Compiler.transf_c_program updated_csyntax)
              Asmexpand.expand_program with
      | Errors.OK asm -> asm
      | Errors.Error msg ->
          (*prerr_endline "[DEBUG] error during transf_c_program; dumping Csyntax...";
          flush stderr;
          debug_dump_composites updated_csyntax;
          debug_dump_csyntax_globals updated_csyntax;
          debug_dump_csyntax_public updated_csyntax;
          debug_find_undefined_references updated_csyntax;
          debug_dump_csyntax_to_file sourcename updated_csyntax;*)
  
          let loc = file_loc sourcename in
          fatal_error loc
            "error during transf_c_program: %a"
            print_error msg
  
    in*)
    let asm =
      match Compiler.apply_partial
              (Compiler.transf_c_program updated_csyntax)
              Asmexpand.expand_program with
      | Errors.OK asm -> asm
      | Errors.Error msg ->
        (*prerr_endline "[DEBUG] transf_c_program failed; checking prog_public vs prog_defs...";
        debug_find_missing_public updated_csyntax;
        prerr_endline "[DEBUG] Full error message:";
        prerr_endline (Format.asprintf "%a" print_error msg);
        flush stderr;*)
        let loc = file_loc sourcename in
        fatal_error loc "error during transf_c_program: %a" print_error msg
        in
  
    AsmToJSON.print_if asm sourcename;
    let oc = open_out ofile in
    PrintAsm.print_program oc asm;
    close_out oc;
    if !option_bpfmap then apply_bpf_map_replacements ofile 

  let compile_b_file sourcename ofile =
      (* Prepare to dump Clight, RTL, etc, if requested *)
      let set_dest dst opt ext =
        dst := if !opt then Some (output_filename sourcename ~suffix:ext)
          else None in
      set_dest Cprint.destination option_dparse ".parsed.c";
      set_dest PrintCsyntax.destination option_dcmedium ".compcert.c";
      set_dest PrintClight.destination option_dclight ".light.c";
      set_dest PrintCminor.destination option_dcminor ".cm";
      set_dest PrintCminorSel.destination option_dcminorsel ".cms";
      set_dest PrintRTL.destination option_drtl ".rtl";
      set_dest Regalloc.destination_alloctrace option_dalloctrace ".alloctrace";
      set_dest PrintLTL.destination option_dltl ".ltl";
      set_dest PrintMach.destination option_dmach ".mach";
      set_dest AsmToJSON.destination option_sdump !sdump_suffix;
    
      (* Typecheck BeePL program *)
      if !option_typecheck then begin
        let typecheck_result =
          BeePL_typechecker.type_check_program BeePL_progs.example1 in
        match typecheck_result with
        | Errors.OK s ->
            let str = Camlcoq.camlstring_of_coqstring s in
            Printf.printf "Typecheck result: %s\n" str
        | Errors.Error msg ->
            let loc = file_loc sourcename in
            fatal_error loc
              "error during BeePL_typechecker.type_check_program: %a"
              print_error msg
      end;
    
      (* BeePL -> Csyntax *)
      let beepl = Compiler.transf_beepl_program_csyntax BeePL_progs.example1 in
      let (csyntax, ident_to_string, section_info) =
        match beepl with
        | Errors.OK ((csyntax, ident_to_string), section_info) ->
            (csyntax, ident_to_string, section_info)
        | Errors.Error msg ->
            let loc = file_loc sourcename in
            fatal_error loc
              "error during transf_beepl_program_csyntax: %a"
              print_error msg
      in
    
      (* Register atoms *)
      List.iter
        (fun (id, charlist) ->
           let s : string = String.concat "" (List.map (String.make 1) charlist) in
           Hashtbl.add Camlcoq.string_of_atom id s;
           Hashtbl.add Camlcoq.atom_of_string s id)
        ident_to_string;
    
      (* Section info *)
      populate_decl_atom section_info;
    
      (* Add helper functions *)
      let gl = C2C.add_helper_functions csyntax.Ctypes.prog_defs in
      let updated_csyntax =
        { csyntax with
          Ctypes.prog_defs   = gl;
          Ctypes.prog_public = C2C.public_globals gl }
      in
      PrintCsyntax.print_if updated_csyntax;
    
      (* Convert to Asm *)
      let asm =
        match Compiler.apply_partial
                (Compiler.transf_c_program updated_csyntax)
                Asmexpand.expand_program with
        | Errors.OK asm -> asm
        | Errors.Error msg ->
            let loc = file_loc sourcename in
            fatal_error loc
              "error during transf_c_program: %a"
              print_error msg
      in 

    (* Convert to Asm 
    let asm =
      match Compiler.apply_partial
              (Compiler.transf_c_program updated_csyntax)
              Asmexpand.expand_program with
      | Errors.OK asm -> asm
      | Errors.Error msg ->
          let loc = file_loc sourcename in
  
          (* DEBUG: dump globals and full Csyntax program *)
          prerr_endline "[DEBUG] error during transf_c_program; dumping Csyntax...";
          flush stderr;
          debug_dump_csyntax_globals updated_csyntax;
          flush stderr;
          debug_dump_csyntax_to_file sourcename updated_csyntax;
          debug_dump_function_locals update_csyntax;
          flush stderr;
  
          fatal_error loc
            "error during transf_c_program: %a"
            print_error msg
    in*)
  

    
      AsmToJSON.print_if asm sourcename;
      let oc = open_out ofile in
      PrintAsm.print_program oc asm;
      close_out oc;
      if !option_bpfmap then apply_bpf_map_replacements ofile
    
(* From C source to asm *)

let compile_i_file sourcename preproname =
  if !option_interp then begin
    Machine.config := Machine.compcert_interpreter !Machine.config;
    let csyntax = parse_c_file sourcename preproname in
    Interp.execute csyntax;
        ""
  end else if !option_S then begin
    compile_c_file sourcename preproname
      (output_filename ~final:true sourcename ~suffix:".s");
    ""
  end else begin
    let asmname =
      if !option_dasm
      then output_filename sourcename ~suffix:".s"
      else tmp_file ".s" in
    compile_c_file sourcename preproname asmname;
    let objname = object_filename sourcename  in
    assemble asmname objname;
    objname
  end

(* Processing of a .c file *)

let process_c_file sourcename =
  ensure_inputfile_exists sourcename;
  if !option_E then begin
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    let preproname = if !option_dprepro then
      output_filename sourcename ~suffix:".i"
    else
      tmp_file ".i" in
    preprocess sourcename preproname;
    compile_i_file sourcename preproname
  end

(* Processing of a .i / .p file (preprocessed C) *)

let process_i_file sourcename =
  ensure_inputfile_exists sourcename;
  compile_i_file sourcename sourcename

(* Processing of .S and .s files *)

let process_s_file sourcename =
  ensure_inputfile_exists sourcename;
  let objname = object_filename sourcename in
  assemble sourcename objname;
  objname

let process_S_file sourcename =
  ensure_inputfile_exists sourcename;
  if !option_E then begin
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    let preproname = tmp_file ".s" in
    preprocess sourcename preproname;
    let objname = object_filename sourcename in
    assemble preproname objname;
    objname
  end

(* Processing of .h files *)

let process_h_file sourcename =
  if !option_E then begin
    ensure_inputfile_exists sourcename;
    preprocess sourcename (output_filename_default "-");
    ""
  end else
    fatal_error no_loc "input file %s ignored (not in -E mode)\n" sourcename

let process_bpl_file sourcename =
  if !option_beepl then begin
    let transformed = Beepl_export.export_parse_and_transform_bpl sourcename in
    (* Save transformed string to .v file *)
    let output_name = output_filename sourcename ~suffix:".v" in
    let oc = open_out output_name in
    output_string oc transformed;
    close_out oc;
    exit 0
  end else
    let beepl_program = Beepl_transformer.parse_and_transform_bpl sourcename in

    if !option_S then begin
      let asmname = output_filename ~final:true sourcename ~suffix:".s" in
      compile_bpl_file sourcename asmname beepl_program;
      ""
    end else begin
      let asmname =
        if !option_dasm
        then output_filename sourcename ~suffix:".s"
        else tmp_file ".s" in
      compile_bpl_file sourcename asmname beepl_program;
      let objname = object_filename sourcename in
      assemble asmname objname;
      objname
    end

let process_b_file sourcename =
  if !option_S then begin
    let asmname = output_filename ~final:true sourcename ~suffix:".s" in
    compile_b_file sourcename asmname;
    ""
  end else begin
    let asmname =
      if !option_dasm
      then output_filename sourcename ~suffix:".s"
      else tmp_file ".s" in
    compile_b_file sourcename asmname;
    let objname = object_filename sourcename in
    assemble asmname objname;
    objname
  end

let target_help =
  if Configuration.arch = "arm" && Configuration.model <> "armv6" then
{|Target processor options:
  -mthumb        Use Thumb2 instruction encoding
  -marm          Use classic ARM instruction encoding
|}
else
  ""

let toolchain_help =
  if not Configuration.gnu_toolchain then begin
{|Toolchain options:
  -t tof:env     Select target processor for the diab toolchain
|} end else
    ""

let usage_string =
  version_string tool_name ^
  {|Usage: ccomp [options] <source files>
Recognized source files:
  .c             C source file
  .i or .p       C source file that should not be preprocessed
  .s             Assembly file
  .S or .sx      Assembly file that must be preprocessed
  .o             Object file
  .a             Library file
Processing options:
  -c             Compile to object file only (no linking), result in <file>.o
  -E             Preprocess only, send result to standard output
  -S             Compile to assembler only, save result in <file>.s
  -o <file>      Generate output in <file>
|} ^
  prepro_help ^
  language_support_help ^
 DebugInit.debugging_help ^
{|Optimization options: (use -fno-<opt> to turn off -f<opt>)
  -O             Optimize the compiled code [on by default]
  -O0            Do not optimize the compiled code
  -O1 -O2 -O3    Synonymous for -O
  -Os            Optimize for code size in preference to code speed
  -Obranchless   Optimize to generate fewer conditional branches; try to produce
                 branch-free instruction sequences as much as possible
  -ftailcalls    Optimize function calls in tail position [on]
  -fconst-prop   Perform global constant propagation  [on]
  -ffloat-const-prop <n>  Control constant propagation of floats
                   (<n>=0: none, <n>=1: limited, <n>=2: full; default is full)
  -fcse          Perform common subexpression elimination [on]
  -fredundancy   Perform redundancy elimination [on]
  -finline       Perform inlining of functions [on]
  -finline-functions-called-once Integrate functions only required by their
                 single caller [on]
  -fif-conversion Perform if-conversion (generation of conditional moves) [on]
  -fjump-tables  Use jump tables for lowering switches [on]
Code generation options: (use -fno-<opt> to turn off -f<opt>)
  -ffpu          Use FP registers for some integer operations [on]
  -fsmall-data <n>  Set maximal size <n> for allocation in small data area
  -fsmall-const <n>  Set maximal size <n> for allocation in small constant area
  -falign-functions <n>  Set alignment (in bytes) of function entry points
  -falign-branch-targets <n>  Set alignment (in bytes) of branch targets
  -falign-cond-branches <n>  Set alignment (in bytes) of conditional branches
  -fcommon       Put uninitialized globals in the common section [on].
|} ^
 target_help ^
 toolchain_help ^
 assembler_help ^
 linker_help ^
{|Tracing options:
  -dprepro       Save C file after preprocessing in <file>.i
  -dparse        Save C file after parsing and elaboration in <file>.parsed.c
  -dc            Save generated Compcert C in <file>.compcert.c
  -dclight       Save generated Clight in <file>.light.c
  -dcminor       Save generated Cminor in <file>.cm
  -drtl          Save RTL at various optimization points in <file>.rtl.<n>
  -dltl          Save LTL after register allocation in <file>.ltl
  -dmach         Save generated Mach code in <file>.mach
  -dasm          Save generated assembly in <file>.s
  -dall          Save all generated intermediate files in <file>.<ext>
  -sdump         Save info for post-linking validation in <file>.json
|} ^
  general_help ^
  warning_help ^
  {|Interpreter mode:
  -interp        Execute given .c files using the reference interpreter
  -quiet         Suppress diagnostic messages for the interpreter
  -trace         Have the interpreter produce a detailed trace of reductions
  -random        Randomize execution order
  -all           Simulate all possible execution orders
  -main <name>   Start executing at function <name> instead of main()
|}

let print_usage_and_exit () =
  printf "%s" usage_string; exit 0

let dump_mnemonics destfile =
  let oc = open_out_bin destfile in
  let pp = Format.formatter_of_out_channel oc in
  AsmToJSON.pp_mnemonics pp;
  Format.pp_print_flush pp ();
  close_out oc;
  exit 0

let optimization_options = [
  option_ftailcalls; option_fifconversion; option_fconstprop; option_fcse;
  option_fredundancy; option_finline; option_finline_functions_called_once;option_jump_tables
]

let set_all opts () = List.iter (fun r -> r := true) opts
let unset_all opts () = List.iter (fun r -> r := false) opts

let num_source_files = ref 0

let num_input_files = ref 0

let cmdline_actions =
  let f_opt name ref =
    [Exact("-f" ^ name), Set ref; Exact("-fno-" ^ name), Unset ref] in
  let check_align n =
    if n <= 0 || ((n land (n - 1)) <> 0) then
      error no_loc "requested alignment %d is not a power of 2" n
    in
  [
(* Getting help *)
  Exact "-help", Unit print_usage_and_exit;
  Exact "--help", Unit print_usage_and_exit;]
(* Getting version info *)
  @ version_options tool_name @
(* Enforcing CompCert build numbers for QSKs and mnemonics dump *)
  (if Version.buildnr <> "" then
     [Exact "-dump-mnemonics", String  dump_mnemonics;]
   else []) @
(* Processing options *)
 [ Exact "-c", Set option_c;
  Exact "-E", Set option_E;
  Exact "-S", Set option_S;
  Exact "-o", String(fun s -> option_o := Some s);
  Prefix "-o", Self (fun s -> let s = String.sub s 2 ((String.length s) - 2) in
                              option_o := Some s);]
  (* Preprocessing options *)
    @ prepro_actions @
  (* Language support options *)
    language_support_options
  (* Debugging options *)
    @ DebugInit.debugging_actions @
(* Code generation options -- more below *)
 [
  Exact "-beepl", Set option_beepl;
  Exact "-bpfmap", Set option_bpfmap;
  Exact "-typecheck", Set option_typecheck;
  Exact "-O0", Unit (unset_all optimization_options);
  Exact "-O", Unit (set_all optimization_options);
  _Regexp "-O[123]$", Unit (set_all optimization_options);
  Exact "-Os", Set option_Osize;
  Exact "-Obranchless", Set option_Obranchless;
  Exact "-fsmall-data", Integer(fun n -> option_small_data := n);
  Exact "-fsmall-const", Integer(fun n -> option_small_const := n);
  Exact "-ffloat-const-prop", Integer(fun n -> option_ffloatconstprop := n); 
  Exact "-falign-functions", Integer(fun n -> check_align n; option_falignfunctions := Some n);
  Exact "-falign-branch-targets", Integer(fun n -> check_align n; option_falignbranchtargets := n);
  Exact "-falign-cond-branches", Integer(fun n -> check_align n; option_faligncondbranchs := n);] @
      f_opt "common" option_fcommon @
(* Target processor options *)
  (if Configuration.arch = "arm" then
    if Configuration.model = "armv6" then
      [ Exact "-marm", Ignore ] (* Thumb needs ARMv6T2 or ARMv7 *)
    else
      [ Exact "-mthumb", Set option_mthumb;
        Exact "-marm", Unset option_mthumb; ]
   else []) @
(* Toolchain options *)
    (if not Configuration.gnu_toolchain then
       [Exact "-t", String (fun arg -> push_linker_arg "-t"; push_linker_arg arg;
                             prepro_options := arg :: "-t" :: !prepro_options;
                             assembler_options := arg :: "-t" :: !assembler_options;)]
     else
       []) @
(* Assembling options *)
  assembler_actions @
(* Linking options *)
  linker_actions @
(* Tracing options *)
 [ Exact "-dprepro", Set option_dprepro;
  Exact "-dparse", Set option_dparse;
  Exact "-dc", Set option_dcmedium;
  Exact "-dclight", Set option_dclight;
  Exact "-dcminor", Set option_dcminor;
  Exact "-drtl", Set option_drtl;
  Exact "-dltl", Set option_dltl;
  Exact "-dalloctrace", Set option_dalloctrace;
  Exact "-dmach", Set option_dmach;
  Exact "-dasm", Set option_dasm;
  Exact "-dall", Self (fun _ ->
    option_dprepro := true;
    option_dparse := true;
    option_dcmedium := true;
    option_dclight := true;
    option_dcminor := true;
    option_dcminorsel := true;
    option_drtl := true;
    option_dltl := true;
    option_dalloctrace := true;
    option_dmach := true;
    option_dasm := true);
  Exact "-sdump", Set option_sdump;
  Exact "-sdump-suffix", String (fun s -> option_sdump := true; sdump_suffix:= s);
  Exact "-sdump-folder", String (fun s -> AsmToJSON.sdump_folder := s);] @
(* General options *)
   general_options @
(* Diagnostic options *)
  warning_options @
(* Interpreter mode *)
 [ Exact "-interp", Set option_interp;
  Exact "-quiet", Unit (fun () -> Interp.trace := 0);
  Exact "-trace", Unit (fun () -> Interp.trace := 2);
  Exact "-random", Unit (fun () -> Interp.mode := Interp.Random);
  Exact "-all", Unit (fun () -> Interp.mode := Interp.All);
  Exact "-main", String (fun s -> main_function_name := s)
 ]
(* Optimization options *)
(* -f options: come in -f and -fno- variants *)
  @ f_opt "tailcalls" option_ftailcalls
  @ f_opt "if-conversion" option_fifconversion
  @ f_opt "const-prop" option_fconstprop
  @ f_opt "cse" option_fcse
  @ f_opt "redundancy" option_fredundancy
  @ f_opt "inline" option_finline
  @ f_opt "inline-functions-called-once" option_finline_functions_called_once
  @ f_opt "jump-tables" option_jump_tables
(* Code generation options *)
  @ f_opt "fpu" option_ffpu
  @ f_opt "sse" option_ffpu (* backward compatibility *)
  @ [
(* Catch options that are not handled *)
  Prefix "-", Self (fun s ->
      fatal_error no_loc "Unknown option `%s'" s);
(* File arguments *)
  Suffix ".b", Self (fun s ->
    push_action process_b_file s; incr num_source_files; incr num_input_files);
  Suffix ".bpl", Self (fun s ->
    push_action process_bpl_file s; incr num_source_files; incr num_input_files; incr num_bpl_files);
  Suffix ".c", Self (fun s ->
      push_action process_c_file s; incr num_source_files; incr num_input_files);
  Suffix ".i", Self (fun s ->
      push_action process_i_file s; incr num_source_files; incr num_input_files);
  Suffix ".p", Self (fun s ->
      push_action process_i_file s; incr num_source_files; incr num_input_files);
  Suffix ".s", Self (fun s ->
      push_action process_s_file s; incr num_source_files; incr num_input_files);
  Suffix ".S", Self (fun s ->
      push_action process_S_file s; incr num_source_files; incr num_input_files);
  Suffix ".sx", Self (fun s ->
      push_action process_S_file s; incr num_source_files; incr num_input_files);
  Suffix ".o", Self (fun s -> push_linker_arg s; incr num_input_files);
  Suffix ".a", Self (fun s -> push_linker_arg s; incr num_input_files);
  (* GCC compatibility: .o.ext files and .so files are also object files *)
  _Regexp ".*\\.o\\.", Self (fun s -> push_linker_arg s; incr num_input_files);
  Suffix ".so", Self (fun s -> push_linker_arg s; incr num_input_files);
  (* GCC compatibility: .h files can be preprocessed with -E *)
  Suffix ".h", Self (fun s ->
      push_action process_h_file s; incr num_source_files; incr num_input_files);
  ]

let _ =
  try
    Gc.set { (Gc.get()) with
                Gc.minor_heap_size = 524288; (* 512k *)
                Gc.major_heap_increment = 4194304 (* 4M *)
           };
    Printexc.record_backtrace true;
    Frontend.init ();
    parse_cmdline cmdline_actions;
    DebugInit.init (); (* Initialize the debug functions *)
    if nolink () && !option_o <> None && !num_source_files >= 2 then
      fatal_error no_loc "ambiguous '-o' option (multiple source files)";
    if !num_input_files = 0 then
      fatal_error no_loc "no input file";
    if not !option_interp && !main_function_name <> "main" then
      fatal_error no_loc "option '-main' requires option '-interp'";
    let linker_args = time "Total compilation time" perform_actions () in
    if not (nolink ()) && linker_args <> [] then begin
      linker (output_filename_default "a.out") linker_args
    end;
    check_errors ()
  with
  | Sys_error msg
  | CmdError msg -> error no_loc "%s" msg; exit 2
  | Abort -> error_summary (); exit 2
  | e -> crash e
