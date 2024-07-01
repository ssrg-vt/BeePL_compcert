(* *********************************************************i************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

(* Printing eBPF assembly code in asm syntax *)

open Printf
open Camlcoq
open Ctypes
open Sections
open Asm
open PrintAsmaux
open Fileinfo

(* Module containing the printing functions *)

module Target : TARGET =
  struct

    (* Basic printing functions *)

    let comment = "#"

    let symbol        = elf_symbol
    let label         = elf_label


    let print_sum  (f1:out_channel -> 'a -> unit) (f2:out_channel -> 'b -> unit) (oc: out_channel) = function
      | Datatypes.Coq_inl a -> f1 oc a
      | Datatypes.Coq_inr a -> f2 oc a

    
    let  print_label oc lbl = label oc (transl_label lbl)

    let use_abi_name = false

    let int_reg_num_name = function _ -> "reg"

    let int_reg_abi_name = function _ -> "abi"

    let float_reg_num_name = function _ -> "float_reg"

    let float_reg_abi_name = function _ -> "float_abi"

    let int_reg_name   = if use_abi_name then int_reg_abi_name   else int_reg_num_name
    let float_reg_name = if use_abi_name then float_reg_abi_name else float_reg_num_name

    let _ = int_reg_name;;
    let _ = float_reg_name;;

    let sizeOp oc mem =
      let sizeOp_name = function
        | Byte -> "u8"
        | HalfWord -> "u16"
        | Word -> "u32"
        | WordAny -> "u32"
        | SignedWord -> "s32"
        | DBWord     -> "u64"
        | DBWordAny  -> "u64"
      in output_string oc (sizeOp_name mem)

    let operator oc op =
      let operator_name = function
        | ADD -> " += " | SUB -> " -= " | MUL -> " *= " | DIV -> " /= "
        | OR -> " |= " | AND -> " &= " | LSH -> " <<= " | RSH -> " >>= "
        | NEG -> " -" | MOD -> " %= " | XOR -> " ^= " | MOV -> " = " | ARSH -> " s>>= "
      in output_string oc (operator_name op)

    let register_name = function
      | R0 -> "r0" | R1 -> "r1" | R2 -> "r2" | R3 -> "r3" | R4 -> "r4" | R5 -> "r5"
      | R6 -> "r6" | R7 -> "r7" | R8 -> "r8" | R9 -> "r9" | R10 -> "r10"(*| RA -> "ra"*)
        
    let register32_name = function
      | R0 -> "w0" | R1 -> "w1" | R2 -> "w2" | R3 -> "w3" | R4 -> "w4" | R5 -> "w5"
      | R6 -> "w6" | R7 -> "w7" | R8 -> "w8" | R9 -> "w9" | R10 -> "w10"(*| RA -> "wa"*)

    let register w oc ireg =
      output_string oc ((match w with
                         | W32 -> register32_name
                         | W64 -> register_name) ireg)

        
    let immediate oc i =
      match i with
      | Imm32 i -> coqint oc i
      | Imm64 i -> coqint64 oc i

    let ptrofs w oc ofs =
      match w with
      | W32 -> coqint oc ofs
      | W64 -> fprintf oc "%a ll" coqint ofs
    
    let register_or_immediate w oc = function
      | Datatypes.Coq_inl reg ->
         register w oc reg
      | Datatypes.Coq_inr imm -> immediate oc imm

    let immediate_ll oc i =
      match i with
      | Imm32 i -> coqint oc i
      | Imm64 i -> Printf.fprintf oc "%a ll" coqint64 i

    
    let register_or_immediate_ll w oc = function
      | Datatypes.Coq_inl reg ->
         register w oc reg
      | Datatypes.Coq_inr imm -> immediate_ll oc imm

    
    let rec cmpOp = function
      | EQ -> "=="
      | NE -> "!="
      | SET -> "&="
      | GT Signed -> "s>"
      | GT Unsigned -> ">"
      | GE Signed -> "s>="
      | GE Unsigned -> ">="
      | LT Signed -> "s<"
      | LT Unsigned -> "<"
      | LE Signed -> "s<="
      | LE Unsigned -> "<="

    and print_cmp oc op reg w regimm =
      fprintf oc "	%a (%s)= %a\n" (register w) reg (cmpOp op) (register_or_immediate w) regimm

    and print_jump_cmp oc op w reg regimm label =
      fprintf oc "	if %a %s %a goto %a\n" (register w)  reg (cmpOp op) (register_or_immediate w) regimm
        print_label label

(* Names of sections *)

    let name_of_section = function
      | Section_text         -> ".text"
      | Section_data i | Section_small_data i ->
          variable_section ~sec:".data" ~bss:".bss" i
      | Section_const i | Section_small_const i ->
          variable_section ~sec:".section	.rodata" i
      | Section_string sz ->
          elf_mergeable_string_section sz ".section	.rodata"
      | Section_literal sz ->
          elf_mergeable_literal_section sz ".section	.rodata"
      | Section_jumptable    -> ".section	.rodata"
      | Section_debug_info _ -> ".section	.debug_info,\"\",%progbits"
      | Section_debug_loc    -> ".section	.debug_loc,\"\",%progbits"
      | Section_debug_abbrev -> ".section	.debug_abbrev,\"\",%progbits"
      | Section_debug_line _ -> ".section	.debug_line,\"\",%progbits"
      | Section_debug_ranges -> ".section	.debug_ranges,\"\",%progbits"
      | Section_debug_str    -> ".section	.debug_str,\"MS\",%progbits,1"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",\"a%s%s\",%%progbits"
            s (if wr then "w" else "") (if ex then "x" else "")
      | Section_ais_annotation -> sprintf ".section	\"__compcert_ais_annotations\",\"\",@note"

    let section oc sec =
      fprintf oc "	%s\n" (name_of_section sec)

(* Associate labels to floating-point constants and to symbols. *)

(*    let emit_constants oc lit =
      if exists_constants () then begin
         section oc lit;
         if Hashtbl.length literal64_labels > 0 then
           begin
             fprintf oc "	.align 3\n";
             Hashtbl.iter
               (fun bf lbl -> fprintf oc "%a:	.quad	0x%Lx\n" label lbl bf)
               literal64_labels
           end;
         if Hashtbl.length literal32_labels > 0 then
           begin
             fprintf oc "	.align	2\n";
             Hashtbl.iter
               (fun bf lbl ->
                  fprintf oc "%a:	.long	0x%lx\n" label lbl bf)
               literal32_labels
           end;
         reset_literals ()
      end
 *)
(* Generate code to load the address of id + ofs in register_arch r *)

    (* let loadsymbol oc r id ofs = () *)

(* Emit .file / .loc debugging directives *)

    let print_file_line oc file line =
      print_file_line oc comment file line

(*
    let print_location oc loc =
      if loc <> Cutil.no_loc then print_file_line oc (fst loc) (snd loc)
*)

(* Add "w" suffix to 32-bit instructions if we are in 64-bit mode *)

    (* let w oc = *)
    (*   if Archi.ptr64 then output_string oc "w" *)

(* Offset part of a load or store *)

    (* let offset oc = function _ -> "offset" *)

    let coqint_as_offset oc n =
      let n = camlint_of_coqint n in
      let cmp = Int32.compare n Int32.zero in
      if cmp >= 0 then fprintf oc "+ %ld" n
          else fprintf oc "- %ld" (Int32.abs n)


    let  sizew (s:sizeOp) =
           match s with
           | Byte | HalfWord | Word | WordAny | SignedWord  -> W32
           | DBWord | DBWordAny -> W64

    let warchi = if Archi.ptr64 then W64 else W32
    
    (* Printing of instructions *)
    let print_instruction oc = function
      | Pload (op, reg1, reg2, off) ->

        fprintf oc "	%a = *(%a *)(%a %a)\n" (register (sizew op))  reg1 sizeOp op (register W64) reg2 coqint_as_offset off

      | Pstore (op, reg, regimm, off) ->
         fprintf oc "	*(%a *)(%a %a) = %a\n" sizeOp op (register W64) reg  coqint_as_offset off
           (register_or_immediate (sizew op)) regimm

      | Palu (MOV,W64,reg,regimm) -> fprintf oc "	%a = %a\n" (register W64) reg (register_or_immediate_ll W64) regimm
      | Palu (op, w, reg, regimm) ->
        fprintf oc "	%a%a%a\n" (register w) reg operator op (register_or_immediate w) regimm

      | Pcmp (op, w, reg, regimm) -> print_cmp oc op reg w regimm
      | Pjmp goto -> fprintf oc "	goto %a\n" (print_sum print_label symbol) goto
      | Pjmpcmp (op, w, reg, regimm, label) -> print_jump_cmp oc op w reg regimm label

      | Pcall ((Datatypes.Coq_inr s), _) -> fprintf oc "	call %a\n" symbol s
      | Pcall ((Datatypes.Coq_inl r), _) -> fprintf oc "	callx %a\n" (register warchi) r

      | Pret -> fprintf oc "	exit\n"

      | Plabel label -> fprintf oc "%a:\n" print_label label

      | Ploadsymbol(r,id,ofs) -> (* ebpf addresses are 64 bits... *)
         fprintf oc "	%a = \"%a\" + %a\n" (register W64) r symbol id (ptrofs W64) ofs
    
      | Pbuiltin _
      | Pallocframe _
      | Pfreeframe _ -> assert false

(*    let get_section_names name =
      let (text, lit) =
        match C2C.atom_sections name with
        | t :: l :: _ -> (t, l)
        | _    -> (Section_text, Section_literal) in
      text,lit,Section_jumptable *)

    let print_align oc alignment =
      fprintf oc "	.balign %d\n" alignment

    let print_jumptable oc jmptbl =
      let print_tbl oc (lbl, tbl) =
        fprintf oc "%a:\n" label lbl;
        List.iter
          (fun l -> fprintf oc "	.long	%a - %a\n"
                               print_label l label lbl)
          tbl in
      if !jumptables <> [] then
        begin
          section oc jmptbl;
          fprintf oc "	.balign 4\n";
          List.iter (print_tbl oc) !jumptables;
          jumptables := []
        end

    let print_fun_info = elf_print_fun_info

    let print_optional_fun_info _ = ()

    let print_var_info = elf_print_var_info

    let print_comm_symb oc sz name align =
      if C2C.atom_is_static name then
        fprintf oc "	.local	%a\n" symbol name;
        fprintf oc "	.comm	%a, %s, %d\n"
        symbol name
        (Z.to_string sz)
        align

    let print_instructions oc fn =
      current_function_sig := fn.fn_sig;
      List.iter (print_instruction oc) fn.fn_code


(* Data *)

    let address = if Archi.ptr64 then ".quad" else ".long"

    let print_prologue oc = ()
      (* fprintf oc "	.option %s\n" (if Archi.pic_code() then "pic" else "nopic"); *)
      (* if !Clflags.option_g then begin *)
      (*   section oc Section_text; *)
      (* end *)

    let print_epilogue oc = ()
      (* if !Clflags.option_g then begin *)
      (*   Debug.compute_gnu_file_enum (fun f -> ignore (print_file oc f)); *)
      (*   section oc Section_text; *)
      (* end *)

    let default_falignment = 2

                               (*let cfi_startproc oc = ()*)
                               (*let cfi_endproc oc = ()*)

  end

let sel_target () =
  (module Target:TARGET)
