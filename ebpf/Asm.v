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

Require Import Conventions Events Smallstep.
Require Stacklayout.
Require Import Op.

(** * Abstract syntax *)

(** Registers. *)
(* eBPF has 10 general purpose registers and R10 reserved for 
   read-only frame pointer register: size 32/64 bits *)
(* R0 : Return value 
   R1 - R5 : Arguments for the function (caller-saved)
   R6 - R9 : Callee-saved registers that the function calls will preserve 
   R10 : Read-only frame pointer to access stack 
   R0-R5 can be spilled to stack in case of less number of available registers *)
(* The context argument to an eBPF program is loaded into R1 before its execution begins.*)
Inductive ireg: Type := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10.

Inductive freg: Type := F0 | F1 | F2.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.


(** We model the following registers of the eBPF architecture. *)

Inductive preg :=
| IR : ireg -> preg  (**r integer registers *)
| FR : freg -> preg  (**r float registers, not available in eBPF *)
| PC : preg          (**r program counter *)
| RA : preg          (**r pseudo link register *)
.

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq.
Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).


(** Translation of the LTL/Linear/Mach view of machine registers
  to the eBPF view. *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | I0 => IR R0 | I1 => IR R1 | I2 => IR R2 | I3 => IR R3 | I4 => IR R4
  | I5 => IR R5 | I6 => IR R6 | I7 => IR R7 | I8 => IR R8 | I9 => IR R9

  | D0 => FR F0 | D1 => FR F1 | D2 => FR F2
  end.

Declare Scope asm.

(** Conventional names for stack pointer ([SP]) *)
(** Can BPF programs access stack pointer ?
    A: NO. Only frame pointer (register R10) is accessible. 
       From compiler point of view it’s necessary to have stack pointer. 
       For example, LLVM defines register R11 as stack pointer in its BPF backend, 
       but it makes sure that generated code never uses it.*)
Notation "'SP'" := R10 (only parsing) : asm.


(** The instruction set.  Most instructions correspond exactly to
  actual instructions of the eBPF instructions set. See the eBPF
  reference manuals for more details.  Some instructions,
  described below, are pseudo-instructions: they expand to
  canned instruction sequences during the printing of the assembly
  code. *)

Definition off := Ptrofs.int. (* 16 bits *)
Definition imm := int. (* 32 bits *)
Definition label := positive.

Inductive width := W32 | W64.

(*Inductive immw : width -> Type :=
| Imm32  : forall (i:int), immw W32
| Imm64  : forall (i:int64), immw W64.
*)

Definition warchi := if Archi.ptr64 then W64 else W32.

Inductive conv :=
| DWOFW (* long of int *)
| WOFDW (* int of long *)
.

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
  | ARSH  (**r dst >>= src (signed) *)
  | CONV (c:conv)  (**r dst = src *)
.

Inductive cmpOp : Type :=
  | EQ: cmpOp                (**r e1 == e2 *)
  | NE: cmpOp                (**r e1 != e2 *)
  | SET: cmpOp               (**r e1 &  e2 *)
  | GT: signedness -> cmpOp  (**r e1 >  e2 *)
  | GE: signedness -> cmpOp  (**r e1 >= e2 *)
  | LT: signedness -> cmpOp  (**r e1 <  e2 *)
  | LE: signedness -> cmpOp. (**r e1 <= e2 *)

Inductive sizeOp : Type :=
  (** 32 bits *)
| Byte        (**r 1 byte *)
| HalfWord    (**r 2 bytes *)
| Word        (**r 4 bytes *)
| WordAny     (**r 4 bytes *)
| SignedWord (**r 4 bytes (signed) *)
(** 64 bits *)
| DBWord     (**r 8 bytes *)
| DBWordAny.  (**r 8 bytes *)


Definition sizew (s:sizeOp) :=
  match s with
  | Byte | HalfWord | Word | WordAny | SignedWord  => W32
  | DBWord | DBWordAny => W64
  end.

Inductive instruction : Type :=
  | Pmov  : forall (dst:ireg) (cst:int64), instruction   (** dst = cst *)
  | Pload : forall (sz:sizeOp) (dst:ireg) (src:ireg) (offset:off), instruction        (** dst = * (size) (src + offset) *)
  | Pstore : forall (sz:sizeOp) (dst:ireg) (src:ireg+int) (offset:off), instruction   (**r * (size) (dst + offset) = src *)
  | Palu : forall (o:aluOp) (w:width) (r:ireg) (a:ireg+int), instruction    (**r arithmetics *)
  | Pcmp : forall (o:cmpOp) (w:width) (r:ireg) (a:ireg+int), instruction             (**r comparison without branching: eBPF extension *)
  | Pjmp : ident+label -> instruction                           (**r unconditional jump *)
  | Pjmpcmp : forall (o:cmpOp) (w:width) (r:ireg) (a:ireg+int) (l:label), instruction (**r conditional jump with comparison *)
  | Pcall : ireg+ident -> signature -> instruction              (**r function call *)
    (** Three kinds of call:
        - call helper functions by address (this is taken care by ident) 
        - call functions at location pc+offset (this is taken care by ireg)
        - call helper function by BTF id:  
          BTF ID encoded in the imm field, 
          where the BTF ID identifies the helper name and type (this is taken care by ident)*)
  | Pret : instruction                                          (**r function return *)

  (* Pseudo-instructions *)
| Plabel (lbl: label)                                         (**r define a code label *)
| Ploadsymbol (rd:ireg) (id:ident) (ofs: ptrofs)              (**r load address of symbol *)
| Pbuiltin: external_function -> list (builtin_arg preg)
              -> builtin_res preg -> instruction                (**r built-in function (pseudo) *)
| Pallocframe (sz: Z) (ofs_ra ofs_link: ptrofs)               (**r allocate new stack frame *)
| Pfreeframe  (sz: Z) (ofs_ra ofs_link: ptrofs).              (**r deallocate stack frame and restore previous frame *)


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

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.
Open Scope asm.

(** Undefining some registers *)
(* This should undefine R0 to R5 as R1 to R5 are caller save registers and R0 is the return value *)
Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

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


Definition int64_of_int (i:int) := Int64.repr (Int.signed i).


Definition map_sum_left {A B A': Type} (F: A -> A')  (x: A+B) : A'+B :=
  match x with
  | inl i => inl (F i)
  | inr i => inr i
  end.

(**
   https://docs.cilium.io/en/latest/bpf/architecture/#instruction-set
 imm(ediate) is of signed type *)

Definition eval_reg_immw (w:width) (rs : regset) (ri: ireg+int) : val :=
  match ri with
  | inl i => rs i
  | inr i => match w with
             | W32 => Vint i
             | W64 => Vlong (int64_of_int i)
             end
  end.


Definition eval_val_int (w:width)  (ri: val+int) : val :=
  match ri with
  | inl i =>  i
  | inr i => match w with
             | W32 => Vint i
             | W64 => Vlong (int64_of_int i)
                            (* constant are given a signed interpretation *)
             end
  end.

(** Evaluation of [Palu] operands *)
Definition eval_alu (b: aluOp) (w:width) (v1:val) (v2: val+int) : option val :=
  match b with
  | ADD => Some ((if w then Val.add else Val.addl) v1 (eval_val_int w v2))
  | SUB => Some ((if w then Val.sub else Val.subl) v1 (eval_val_int w v2))
  | MUL => Some ((if w then Val.mul else Val.mull) v1 (eval_val_int w v2))
  | DIV => (if w then Val.divu else Val.divlu) v1 (eval_val_int w v2)
  | OR  => Some ((if w then Val.or else Val.orl) v1 (eval_val_int w v2))
  | AND => Some ((if w then Val.and else Val.andl) v1 (eval_val_int w v2))
  | LSH => Some ((if w then Val.shl else Val.shll) v1 (eval_val_int W32 v2))
  | RSH => Some ((if w then Val.shru else Val.shrlu) v1 (eval_val_int W32 v2))
  | NEG => Some ((if w then Val.neg else Val.negl) (eval_val_int w v2))
  | MOD => (if w then Val.modu else Val.modlu) v1 (eval_val_int w v2)
  | XOR => Some ((if w then Val.xor else Val.xorl) v1 (eval_val_int w v2))
  | MOV => Some (eval_val_int w v2)
  | ARSH => Some ((if w then Val.shr else Val.shrl) v1 (eval_val_int W32 v2))
  | CONV DWOFW  => Some (Val.longofintu v1) (* v1 & FF_FF_FF_FF *)
  | CONV WOFDW  => Some (Val.loword v1)     (* v1 & FF_FF_FF_FF *)
  end.

(** Evaluation of [Pcmp] and [Pjmpcmp] operands *)

Definition cmpu (w:width) :=
  if w then Val.cmpu_bool else Val.cmplu_bool.

Definition cmp (w:width) :=
  if  w then Val.cmp_bool else Val.cmpl_bool.

Definition eval_cmp (op: cmpOp) (w:width) (rs: regset) (m: mem) (r: ireg) (ri: ireg+int) : option bool :=
  match op with
  | EQ          => (cmpu w) (Mem.valid_pointer m) Ceq (rs#r) (eval_reg_immw w rs ri)
  | GT Signed   => (cmp w) Cgt (rs#r) (eval_reg_immw w rs ri)
  | GT Unsigned => (cmpu w) (Mem.valid_pointer m) Cgt (rs#r) (eval_reg_immw w rs ri)
  | GE Signed   => (cmp w) Cge (rs#r) (eval_reg_immw w rs ri)
  | GE Unsigned => (cmpu w) (Mem.valid_pointer m) Cge (rs#r) (eval_reg_immw w rs ri)
  | LT Signed   => (cmp w) Clt (rs#r) (eval_reg_immw w rs ri)
  | LT Unsigned => (cmpu w) (Mem.valid_pointer m) Clt (rs#r) (eval_reg_immw w rs ri)
  | LE Signed   => (cmp w) Cle (rs#r) (eval_reg_immw w rs ri)
  | LE Unsigned => (cmpu w) (Mem.valid_pointer m) Cle (rs#r) (eval_reg_immw w rs ri)
  | SET         => (cmpu w) (Mem.valid_pointer m) Cne (Val.and (rs#r) (eval_reg_immw w rs ri)) (Vint Int.zero)
  | NE          => (cmpu w) (Mem.valid_pointer m) Cne (rs#r) (eval_reg_immw w rs ri)
  end.


(** Auxiliaries for memory accesses *)

(*Definition size_to_memory_chunk (size: sizeOp) : memory_chunk :=
  match size with
  | Byte => Mint8unsigned
  | HalfWord => Mint16unsigned
  | Word => Many32
  | SignedWord => Mint32
  end.
 *)

Definition load (k: sizeOp) (addr:val) (m:mem) :=
  match k with
  | Byte => Mem.loadv Mint8unsigned m addr
  | HalfWord => Mem.loadv Mint16unsigned m addr
  | Word     => Mem.loadv Mint32 m addr
  | WordAny  => Mem.loadv Many32 m addr
  | SignedWord => if Archi.ptr64
                  then match Mem.loadv Mint32 m addr with
                       | None => None
                       | Some v => Some (Val.longofint v)
                       end
                  else None
  | DBWord     => if Archi.ptr64 then Mem.loadv Mint64 m addr else None
  | DBWordAny  => if Archi.ptr64 then Mem.loadv Many64 m addr else None
  end.

Definition exec_load (k: sizeOp) (r:ireg) (r':ireg) (o:Ptrofs.int) (rs: regset) (m:mem) :=
  match load k (Val.offset_ptr rs#r' o) m with
  | None => Stuck
  | Some v => Next (nextinstr (rs#r <- v)) m
  end.


Definition cast_long_int (v:val) : val :=
  match v with
  | Vlong l => Vint (Int.repr (Int64.unsigned l))
  | _       => Vundef
  end.



Definition store (k: sizeOp) (addr:val) (v:val) (m:mem) :=
  match k with
  | Byte => Mem.storev Mint8unsigned m addr v
  | HalfWord => Mem.storev Mint16unsigned m addr v
  | Word     => Mem.storev Mint32 m addr v
  | WordAny  => Mem.storev Many32 m addr v
  | SignedWord => if Archi.ptr64 then Mem.storev Mint32 m addr (cast_long_int v) else None
  | DBWord     => if Archi.ptr64 then Mem.storev Mint64 m addr v else None
  | DBWordAny  => if Archi.ptr64 then Mem.storev Many64 m addr v else None
  end.


Definition exec_store (k: sizeOp) (r:ireg) (ri:ireg+int) (o:Ptrofs.int) (rs: regset) (m:mem) :=
  match store  k (Val.offset_ptr rs#r o) (eval_reg_immw (sizew k) rs ri) m with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

Definition exec_alu (o: aluOp) (w:width) (r: ireg) (ri: ireg+int) (rs: regset) (m: mem) :=
  match eval_alu o w (rs#r) (map_sum_left (fun (x:ireg) => rs#x) ri) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#r <- v)) m
  end.

Definition exec_cmp (r: ireg) (rs: regset) (m: mem) (res: option bool) :=
  Next (nextinstr (rs#r <- (Val.of_optbool res))) m.

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
  | Pmov r v        => Next (nextinstr (rs#r <- (Vlong v))) m
  | Pload k r r' o   => exec_load k r r' o rs m
  | Pstore k r ri o  => exec_store k r ri o rs m
  | Palu o w r ri      => exec_alu o w r ri rs m
  | Pcmp o w r ri      => exec_cmp r rs m (eval_cmp o w rs m r ri)
  | Pjmp (inl l)     => goto_label f l rs m
  | Pjmp (inr id)    => Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pjmpcmp o w r ri l => exec_branch f l rs m (eval_cmp o w rs m r ri)
  | Pcall (inr s) sg => Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one)
                                #PC <- (Genv.symbol_address ge s Ptrofs.zero)
                          ) m
  | Pcall (inl r) sg => Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one)
                               #PC  <- (rs#r)) m
  | Pret             => Next (rs#PC <- (rs#RA)) m

  (** Pseudo-instructions *)
  | Pallocframe sz ofs_ra ofs_link =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mptr m1 (Val.offset_ptr sp ofs_link) rs#SP with
      | None => Stuck
      | Some m2 =>
          match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_ra) rs#RA with
          | None => Stuck
          | Some m3 => Next (nextinstr (rs #R0 <- (rs#SP) #SP <- sp)) m3
          end
      end

  | Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#SP ofs_ra) with
      | None => Stuck
      | Some ra =>
          match Mem.loadv Mptr m (Val.offset_ptr rs#SP ofs_link) with
          | None => Stuck
          | Some sp =>
              match rs#SP with
              | Vptr stk ofs =>
                  match Mem.free m stk 0 sz with
                  | None => Stuck
                  | Some m' => Next (nextinstr (rs#SP <- sp #RA <- ra)) m'
                  end
              | _ => Stuck
              end
          end
      end

  | Plabel l         => Next (nextinstr rs) m
  | Ploadsymbol rd s ofs => Next (nextinstr (rs#rd <- (Genv.symbol_address ge s ofs))) m
  | _                => Stuck
  end.

(** Undefine all registers except SP and callee-save registers *)

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r SP
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use eBPF registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr rs#SP (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).

(** Execution of the instruction at [rs PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs SP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs)) #PC <- (rs RA) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # SP <- Vnullptr
        # RA <- Vnullptr in
      Genv.init_mem p = Some m0 ->
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs PC = Vnullptr ->
      rs R0 = Vint r ->
      final_state (State rs m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
  split. constructor. auto.
  discriminate.
  discriminate.
  assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H8. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros. inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal. congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. unfold Vzero in H0. red; intros; red; intros.
  inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR _ => true
  | FR _ => true
  | PC   => false
  | RA   => false
  end.
