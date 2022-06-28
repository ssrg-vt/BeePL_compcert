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

(** Abstract syntax and semantics for RISC-V assembly language. *)

Require Import Coqlib Ctypes AST Integers.
Require Import Maps Values Memory.
Require Import Globalenvs.
Require Import Locations.

(** * Abstract syntax *)

(** Integer registers. *)

Inductive ireg: Type := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.


(** We model the following registers of the eBPF architecture. *)

Inductive preg :=
| IR : ireg -> preg  (**r integer registers *)
| PC : preg          (**r program counter *)
| RA : preg.         (**r pseudo-reg representing return address *)

Coercion IR: ireg >-> preg.

Lemma reg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq.
Defined.

Module RegEq.
  Definition t  := preg.
  Definition eq := reg_eq.
End RegEq.

Module Regmap := EMap(RegEq).


(** Translation of the LTL/Linear/Mach view of machine registers
  to the eBPF view. *)

Definition preg_of (r: mreg) : option preg :=
  match r with
  | I0 => Some (IR R0) | I1 => Some (IR R1) | I2 => Some (IR R2)
  | I3 => Some (IR R3) | I4 => Some (IR R4) | I5 => Some (IR R5)
  | I6 => Some (IR R6) | I7 => Some (IR R7) | I8 => Some (IR R8)
  | I9 => Some (IR R9)
  | D0 | D1 | D2 => None
  end.


(** Conventional names for stack pointer ([SP]) *)

Notation "'SP'" := (IR R10) (only parsing) : asm.


(** The instruction set.  Most instructions correspond exactly to
  actual instructions of the eBPF instructions set. See the eBPF
  reference manuals for more details.  Some instructions,
  described below, are pseudo-instructions: they expand to
  canned instruction sequences during the printing of the assembly
  code. *)

Definition off := Ptrofs.int. (* 16 bits *)
Definition imm := int. (* 20 bits *)
Definition label := positive.

Inductive aluOp : Type :=
  | ADD   (**r dst += src *)
  | SUB   (**r dst -= src *)
  | MUL   (**r dst *= src *)
  | DIV   (**r dst /= src *)
  | OR    (**r dst |= src *)
  | AND   (**r dst &= src *)
  | LSH   (**r dst <<= src *)
  | RSH   (**r dst >>= src (unsigned) *)
  | NEG   (**r dst = ~src *)
  | MOD   (**r dst %= src *)
  | XOR   (**r dst ^= src *)
  | MOV   (**r dst = src *)
  | ARSH. (**r dst >>= src (signed) *)

Inductive cmpOp : Type :=
  | EQ: cmpOp                (**r e1 == e2 *)
  | NE: cmpOp                (**r e1 != e2 *)
  | SET: cmpOp               (**r e1 &  e2 *)
  | GT: signedness -> cmpOp  (**r e1 >  e2 *)
  | GE: signedness -> cmpOp  (**r e1 >= e2 *)
  | LT: signedness -> cmpOp  (**r e1 <  e2 *)
  | LE: signedness -> cmpOp. (**r e1 <= e2 *)

Inductive sizeOp : Type :=
  | Byte      (**r 1 byte *)
  | HalfWord  (**r 2 bytes *)
  | Word.     (**r 4 bytes *)

Inductive instruction : Type :=
  | Pload : sizeOp -> preg -> preg -> off -> instruction        (**r dereference load *)
  | Pstore : sizeOp -> preg -> preg+imm -> off -> instruction   (**r dereference store *)
  | Palu : aluOp -> preg -> preg+imm -> instruction             (**r arithmetics *)
  | Pcmp : cmpOp -> preg -> preg+imm -> instruction             (**r comparison without branching: eBPF extension *)
  | Pjmp : ident+label -> instruction                           (**r unconditional jump *)
  | Pjmpcmp : cmpOp -> preg -> preg+imm -> label -> instruction (**r conditional jump with comparison *)
  | Pcall : ident -> signature -> instruction                   (**r function call *)
  | Pret : instruction                                          (**r function return *)

  (* Pseudo-instructions *)
  | Plabel (lbl: label)                                         (**r define a code label *)
  | Pbuiltin: external_function -> list (builtin_arg preg)
              -> builtin_res preg -> instruction                (**r built-in function (pseudo) *)
  | Pallocframe (sz: Z) (pos: ptrofs)                           (**r allocate new stack frame *)
  | Pfreeframe  (sz: Z) (pos: ptrofs).                          (**r deallocate stack frame and restore previous frame *)


Definition code := list instruction.
Record function : Type := mkfunction {fn_sig: signature; fn_code: code}.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and condition bits to either [Vzero] or [Vone]. *)

Definition regset := Regmap.t val.
Definition genv := Genv.t fundef unit.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.

Section RELSEM.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl lbl0); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

Variable ge: genv.


(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome : Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.


(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC Ptrofs.one).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _          => Stuck
      end
  end.

Definition eval_reg_imm (rs : regset) (ri: preg+imm) : val :=
  match ri with
  | inl r => rs#r
  | inr i => Vint i
  end.

(** Evaluation of [Palu] operands *)

Definition eval_alu (b: aluOp) (v1 v2: val) : option val :=
  match b with
  | ADD => Some (Val.add v1 v2)
  | SUB => Some (Val.sub v1 v2)
  | MUL => Some (Val.mul v1 v2)
  | DIV => Val.divu v1 v2
  | OR  => Some (Val.or v1 v2)
  | AND => Some (Val.and v1 v2)
  | LSH => Some (Val.shl v1 v2)
  | RSH => Some (Val.shru v1 v2)
  | NEG => Some (Val.neg v2)
  | MOD => Val.modu v1 v2
  | XOR => Some (Val.xor v1 v2)
  | MOV => Some v2
  | ARSH => Some (Val.shr v1 v2)
  end.

(** Evaluation of [Pcmp] and [Pjmpcmp] operands *)

Definition eval_cmp (op: cmpOp) (rs: regset) (m: mem) (r: preg) (ri: preg+imm) : option bool :=
  match op with
  | EQ          => Val.cmp_bool Ceq (rs#r) (eval_reg_imm rs ri)
  | GT Signed   => Val.cmp_bool Cgt (rs#r) (eval_reg_imm rs ri)
  | GT Unsigned => Val.cmpu_bool (Mem.valid_pointer m) Cgt (rs#r) (eval_reg_imm rs ri)
  | GE Signed   => Val.cmp_bool Cge (rs#r) (eval_reg_imm rs ri)
  | GE Unsigned => Val.cmpu_bool (Mem.valid_pointer m) Cge (rs#r) (eval_reg_imm rs ri)
  | LT Signed   => Val.cmp_bool Clt (rs#r) (eval_reg_imm rs ri)
  | LT Unsigned => Val.cmpu_bool (Mem.valid_pointer m) Clt (rs#r) (eval_reg_imm rs ri)
  | LE Signed   => Val.cmp_bool Cle (rs#r) (eval_reg_imm rs ri)
  | LE Unsigned => Val.cmpu_bool (Mem.valid_pointer m) Cle (rs#r) (eval_reg_imm rs ri)
  | SET         => Val.cmp_bool Cne (Val.and (rs#r) (eval_reg_imm rs ri)) (Vint Int.zero)
  | NE          => Val.cmp_bool Cne (rs#r) (eval_reg_imm rs ri)
  end.


(** Auxiliaries for memory accesses *)

Definition size_to_memory_chunk (size: sizeOp) : memory_chunk :=
  match size with
  | Byte => Mint8unsigned
  | HalfWord => Mint16unsigned
  | Word => Many32
  end.

Definition exec_load (k: sizeOp) (r:preg) (r':preg) (o:Ptrofs.int) (rs: regset) (m:mem) :=
  match Mem.loadv (size_to_memory_chunk k) m (Val.offset_ptr rs#r' o) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#r <- v)) m
  end.

Definition exec_store (k: sizeOp) (r:preg) (ri:preg+imm) (o:Ptrofs.int) (rs: regset) (m:mem) :=
  match Mem.storev (size_to_memory_chunk k) m (Val.offset_ptr rs#r o) (eval_reg_imm rs ri) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

Definition exec_alu (o: aluOp)  (r: preg) (ri: preg+imm) (rs: regset) (m: mem) :=
  match eval_alu o (rs#r) (eval_reg_imm rs ri) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#r <- v)) m
  end.

Definition exec_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
  | Some true  => goto_label f l rs m
  | Some false => Next (nextinstr rs) m
  | None => Stuck
  end.


(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual eBPF instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the eBPF reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above. *)

Definition exec_instr (f: function) (i: instruction) (rs:regset) (m: mem) : outcome :=
  match i with
  | Pload k r r' o   => exec_load k r r' o rs m
  | Pstore k r ri o  => exec_store k r ri o rs m
  | Palu o r ri      => exec_alu o r ri rs m
  | Pcmp o r ri      => Next (rs#r <- (Val.of_optbool (eval_cmp o rs m r ri))) m
  | Pjmp (inl l)     => goto_label f l rs m
  | Pjmp (inr id)    => Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pjmpcmp o r ri l => exec_branch f l rs m (eval_cmp o rs m r ri)
  | Pcall s sg       => Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one)
                                #PC <- (Genv.symbol_address ge s Ptrofs.zero)
                          ) m
  | Pret             => Next (rs#PC <- (rs#RA)) m
  | Plabel l         => Next (nextinstr rs) m
  | _                => Stuck
  end.

End RELSEM.
