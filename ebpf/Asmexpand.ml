(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the eBPF assembly code. *)

open Asm
open Asmexpandaux
open AST
open Camlcoq

exception Error of string


(* Expansion of instructions *)
let expand_alloc_frame sz ofs_ra ofs_link =
  Datatypes.(
  (* RO := SP *)
  emit (Palu(MOV,R0,Coq_inl R10));
  (* SP := SP - sz *)
  emit (Palu(SUB,R10,Coq_inr sz));
  (* *(SP+ofs_link) := R0 *)
  emit (Pstore(Word,R10,Coq_inl R0,ofs_link));
  (* *(SP+ofs_ra) := RA *)
  emit (Pstore(Word,R10,Coq_inl RA,ofs_ra)))

let expand_free_frame sz ofs_ra ofs_link =
  Datatypes.(
  (* RA := *(SP+ofs_ra) *)
  emit (Pload(Word,RA,R10,ofs_ra));
  (* SP := SP + sz *)
  emit (Palu(ADD,R10,Coq_inr sz)))


let expand_instruction instr =
  match instr with
  | Pbuiltin _ -> failwith "Builtin are not supported"
  | Pallocframe(sz,ofs_ra,ofs_link) -> expand_alloc_frame sz ofs_ra ofs_link
  | Pfreeframe(sz,ofs_ra,ofs_link)  -> expand_free_frame sz ofs_ra ofs_link

  | _ -> emit instr


(* NOTE: Dwarf register maps for RV32G are not yet specified
   officially.  This is just a placeholder.  *)

let int_reg_to_dwarf = function
               | R0  -> 1  | R1  -> 2  | R2  -> 3
   | R3  -> 4  | R4  -> 5  | R5  -> 6  | R6  -> 7
   | R7  -> 8  | R8  -> 9  | R9  -> 10 | R10 -> 11 | RA -> 12

let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r
   | _ -> assert false

let expand_function id fn =
  try
    set_current_function fn;
    expand id (int_reg_to_dwarf R10) preg_to_dwarf expand_instruction fn.fn_code;
    Errors.OK (get_current_function ())
  with Error s ->
    Errors.Error (Errors.msg (coqstring_of_camlstring s))

let expand_fundef id = function
  | Internal f ->
      begin match expand_function id f with
      | Errors.OK tf -> Errors.OK (Internal tf)
      | Errors.Error msg -> Errors.Error msg
      end
  | External ef ->
      Errors.OK (External ef)

let expand_program (p: Asm.program) : Asm.program Errors.res =
  AST.transform_partial_program2 expand_fundef (fun id v -> Errors.OK v) p
