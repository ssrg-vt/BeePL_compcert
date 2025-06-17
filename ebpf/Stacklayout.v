(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Machine- and ABI-dependent layout information for activation records. *)

Require Import Coqlib.
Require Import AST Memory Separation.
Require Import Bounds.

(* Reuse x86 layout - in particular return address at the top *)

(** The general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- Space for outgoing arguments to function calls.
- Saved values of integer callee-save registers used by the function.
- Saved values of float callee-save registers used by the function.
- Local stack slots.
- Space for the stack-allocated data declared in Cminor
- Back link to parent frame
- Return address.

The [frame_env] compilation environment records the positions of
the boundaries between areas in the frame part.

*)

Definition fe_ofs_arg := 0.

(** Computation of the frame environment from the bounds of the current
  function. *)

Definition make_env (b: bounds) : frame_env :=
  let w := if Archi.ptr64 then 8 else 4 in
  let ocs := align (fe_ofs_arg + 4 * b.(bound_outgoing)) w in  (* callee-saves *)
  let ol :=  align (size_callee_save_area b ocs) 8 in (* locals *)
  let ostkdata := align (ol + 4 * b.(bound_local)) 8 in (* stack data *)
  let olink := align (ostkdata + b.(bound_stack_data)) w in (* parent stack pointer *)
  let oretaddr := align (olink + w) w in (* return address *)
  let sz := oretaddr + w in (* total size *)
  {| fe_size := sz;
     fe_ofs_link := olink;
     fe_ofs_retaddr := oretaddr;
     fe_ofs_local := ol;
     fe_ofs_callee_save := ocs;
     fe_stack_data := ostkdata;
     fe_used_callee_save := b.(used_callee_save) |}.

Local Open Scope sep_scope.

Lemma frame_env_separated:
  forall b sp m P,
  let fe := make_env b in
  m |= range sp 0 (fe_stack_data fe) ** range sp (fe_stack_data fe + bound_stack_data b) (fe_size fe) ** P ->
  m |= range sp (fe_ofs_local fe) (fe_ofs_local fe + 4 * bound_local b)
       ** range sp fe_ofs_arg (fe_ofs_arg + 4 * bound_outgoing b)
       ** range sp (fe_ofs_link fe) (fe_ofs_link fe + size_chunk Mptr)
       ** range sp (fe_ofs_retaddr fe) (fe_ofs_retaddr fe + size_chunk Mptr)
       ** range sp (fe_ofs_callee_save fe) (size_callee_save_area b (fe_ofs_callee_save fe))
       ** P.
Proof.
  Local Opaque Z.add Z.mul sepconj range.
  simpl. intros b sp m P.
  set (w := if Archi.ptr64 then 8 else 4).
  set (ocs := align (fe_ofs_arg + 4 * b.(bound_outgoing)) w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (olink := align (ostkdata +  b.(bound_stack_data)) w).
  set (oretaddr := align (olink + w) w).
  replace (size_chunk Mptr) with w by (rewrite size_chunk_Mptr; auto).
  intro HYP.
  assert (0 < w) by (unfold w; destruct Archi.ptr64; lia).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= fe_ofs_arg) by (unfold fe_ofs_arg;  lia).
  assert (0 <= 4 * b.(bound_outgoing)) by lia.
  assert (fe_ofs_arg + 4 * b.(bound_outgoing) <= ocs) by (apply align_le; lia).
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr).
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; lia).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; lia).
  assert (ostkdata + bound_stack_data b <= olink) by (apply align_le; lia).
  assert (olink + w <= oretaddr) by (apply align_le; lia).
  (* Reorder as:
     outgoing
     callee-save
     local
     back link
     retaddr *)
  rewrite sep_swap12.
  rewrite sep_swap45.
  rewrite sep_swap34.
  rewrite sep_swap23.
(* Apply range_split and range_split2 repeatedly *)
  apply range_drop_left with 0. lia.
  apply range_drop_right with ocs. lia.
  apply range_split. lia.
  apply range_drop_right with ol. lia.
  apply range_split. lia.
  apply range_drop_right with ostkdata. lia.
  rewrite sep_swap12.
  rewrite sep_swap23.
  apply range_drop_right with oretaddr. lia.
  apply range_split. lia.
  apply range_drop_left with (ostkdata + bound_stack_data b).
  lia.
  rewrite sep_swap12.
  exact HYP.
Qed.

Lemma frame_env_range:
  forall b,
  let fe := make_env b in
  0 <= fe_stack_data fe /\ fe_stack_data fe + bound_stack_data b <= fe_size fe.
Proof.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  set (ocs := align (fe_ofs_arg + 4 * b.(bound_outgoing)) w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (olink := align (ostkdata +  b.(bound_stack_data)) w).
  set (oretaddr := align (olink + w) w).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; lia).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= fe_ofs_arg) by (unfold fe_ofs_arg; lia).
  assert (0 <= 4 * b.(bound_outgoing)) by lia.
  assert (fe_ofs_arg + 4 * b.(bound_outgoing) <= ocs) by (apply align_le; lia).
  assert ((size_callee_save_area b ocs) <= ol) by (apply align_le; lia).
  assert (ocs <= size_callee_save_area b ocs) by  (apply size_callee_save_area_incr).
  assert (ol + 4 * bound_local b <= ostkdata) by  (apply align_le;lia).
  assert (ostkdata + bound_stack_data b <= olink) by (apply align_le;lia).
  assert (olink + w <= oretaddr) by (apply align_le;lia).
  lia.
Qed.

Lemma frame_env_aligned:
  forall b,
  let fe := make_env b in
     (8 | fe_ofs_arg)
  /\ (8 | fe_ofs_local fe)
  /\ (8 | fe_stack_data fe)
  /\ (align_chunk Mptr | fe_ofs_link fe)
  /\ (align_chunk Mptr | fe_ofs_retaddr fe).
Proof.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  set (ocs := align (fe_ofs_arg + 4 * b.(bound_outgoing)) w).
  set (ol :=  align (size_callee_save_area b ocs) w).
  set (ostkdata := align (ol + 4 * b.(bound_local)) w).
  set (olink := align (ostkdata +  b.(bound_stack_data)) w).
  set (oretaddr := align (olink + w) w).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; lia).
  replace (align_chunk Mptr) with w by (rewrite align_chunk_Mptr; auto).
  split. exists (fe_ofs_arg / 8). unfold fe_ofs_arg;  reflexivity.
  split.
  apply align_divides; lia.
  split. apply align_divides; lia.
  split. apply align_divides; lia.
  apply align_divides; lia.
Qed.
