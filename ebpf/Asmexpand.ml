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

let ra = R9
let sp = R10

let warchi = if Archi.ptr64 then W64 else W32


let chunk_of_pointer = if Archi.ptr64 then DBWord else Word

(* Expansion of instructions *)
let expand_alloc_frame sz ofs_ra ofs_link =
  let sz = Integers.Int.repr sz in
  Datatypes.(
  (* RO := SP *)
  emit (Palu(MOV,warchi,R0,Coq_inl sp));
  (* SP := SP - sz *)
  emit (Palu(SUB,warchi,sp,Coq_inr sz));
  (* *(SP+ofs_link) := R0 *)
  emit (Pstore(chunk_of_pointer,sp,Coq_inl R0,ofs_link));
  (* *(SP+ofs_ra) := RA *)
  emit (Pstore(chunk_of_pointer,sp,Coq_inl ra,ofs_ra)))

let expand_free_frame sz ofs_ra ofs_link =
  let sz = Integers.Int.repr sz in
  Datatypes.(
  (* RA := *(SP+ofs_ra) *)
  emit (Pload(chunk_of_pointer,ra,sp,ofs_ra));
  (* SP := SP + sz *)
  emit (Palu(ADD,warchi,sp,Coq_inr sz)))


let expand_instruction instr =
  match instr with
  | Pbuiltin _ -> failwith "Builtin are not supported"
  | Pallocframe(sz,ofs_ra,ofs_link) -> expand_alloc_frame sz ofs_ra ofs_link
  | Pfreeframe(sz,ofs_ra,ofs_link)  -> expand_free_frame sz ofs_ra ofs_link
  | Pcmp(cmp,w,reg,regimm) ->
    (* reg := reg cmp regimm *)
    Datatypes.(
      let label_true = new_label () in
      let label_end   = new_label () in 
      (* if reg cmp regimm Goto goto_true *)
      emit (Pjmpcmp(cmp,w,reg,regimm, label_true));
      (* else reg := false *)
      emit (Palu(MOV,W64,reg, Coq_inr Integers.Int.zero));
      emit (Pjmp (Coq_inl label_end));
      emit (Plabel label_true);
      emit  (Palu(MOV,W64,reg, Coq_inr Integers.Int.one));
    emit (Plabel label_end))
  | _ -> emit instr


(* NOTE: Dwarf register maps for RV32G are not yet specified
   officially.  This is just a placeholder.  *)

let int_reg_to_dwarf = function
               | R0  -> 1  | R1  -> 2  | R2  -> 3
   | R3  -> 4  | R4  -> 5  | R5  -> 6  | R6  -> 7
   | R7  -> 8  | R8  -> 9  | R9  -> 10 | R10 -> 11 (*| RA -> 12*)

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
