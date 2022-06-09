From compcert Require Import Coqlib Ctypes AST Integers.
From compcert Require Import Maps Values Memory.
From compcert Require Import Globalenvs.


(* ebpf registers - PC is not included *)
Inductive ireg: Type :=
  | R0:ireg | R1:ireg | R2:ireg
  | R3:ireg | R4:ireg | R5:ireg
  | R6:ireg | R7:ireg | R8:ireg
  | R9:ireg | R10:ireg
.

Inductive preg :=
| IR : ireg -> preg
| PC : preg.

Lemma ereg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma reg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ereg_eq.
Defined.

Module RegEq.
  Definition t  := preg.
  Definition eq := reg_eq.
End RegEq.

Module Regmap := EMap(RegEq).

(** Conventional names for stack pointer ([SP]) and return address ([RA]). *)
Declare Scope asm.

Notation "'SP'" := (left R10) (only parsing) : asm.
Notation "'RA'" := (left R1) (only parsing) : asm. (* Does not quite exist... *)

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
(*Notation "a ## b" := (get0w a b) (at level 1) : asm.
Notation "a ### b" := (get0l a b) (at level 1) : asm. *)
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.


Inductive cond :=
| Eq
| Gt: signedness -> cond
| Ge: signedness -> cond
| Lt: signedness -> cond
| Le: signedness -> cond
| SEt
| Ne
.

Inductive binOp: Type :=
| ADD | SUB | MUL | DIV | OR | AND
| LSH | RSH | MOD | XOR | ARSH.

Definition off := Ptrofs.int. (* 16 bits *)
Definition imm := int. (* 16 bits *)
Definition label := positive.

Inductive instruction: Type :=
(**r ALU *)
| NEG    : preg -> instruction
| BINARY : binOp -> preg -> preg+imm -> instruction
(**r Branch *)
| JA   : label -> instruction
| JUMP : cond -> preg -> preg+imm -> label -> instruction
(**r Load *)
| LDDW_low : preg -> imm -> instruction
| LDDW_high : preg -> imm -> instruction
(**r Load_x *)
| LDX  : memory_chunk -> preg -> preg -> off -> instruction
(**r Store/ Store_x *)
| ST   : memory_chunk -> preg -> preg -> off -> instruction
(*(**r exit *)
| CALL : imm -> instruction
| RET  : instruction *)
(**r Pseudo-instructions *)
| Plabel (lbl: label)
| Pbuiltin: external_function -> list (builtin_arg preg)
              -> builtin_res preg -> instruction    (**r built-in function (pseudo) *)
.

Definition code := list instruction.

Record function : Type := mkfunction {fn_sig: signature; fn_code: code}.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition regset := Regmap.t val.

Definition genv := Genv.t fundef unit.

Inductive outcome : Type :=
| Next: regset -> mem -> outcome
| Stuck: outcome.

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC Ptrofs.one).

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.


Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _          => Stuck
      end
  end.


Definition eval_binop (b: binOp) (v1 v2: val) : option val :=
  match b with
  | ADD => Some (Val.add v1 v2)
  | SUB => Some (Val.sub v1 v2)
  | MUL => Some (Val.mul v1 v2)
  | DIV => Val.divu v1 v2
  | OR  => Some (Val.or v1 v2)
  | AND => Some (Val.and v1 v2)
  | LSH => Some (Val.shl v1 v2)
  | RSH => Some (Val.shru v1 v2)
  | MOD => Val.modu v1 v2
  | XOR => Some (Val.xor v1 v2)
  | ARSH => Some (Val.shr v1 v2)
  end.

Definition eval_cond (valid_ptr : block -> Z -> bool) (c: cond) (v1 v2: val) : option bool :=
  match c with
  | Eq => Val.cmp_bool Ceq v1 v2
  | Gt Signed => Val.cmp_bool Cgt  v1 v2
  | Gt Unsigned => Val.cmpu_bool valid_ptr Cgt  v1 v2
  | Ge Signed   => Val.cmp_bool Cge v1 v2
  | Ge Unsigned   => Val.cmpu_bool valid_ptr Cge v1 v2
  | Lt Signed => Val.cmp_bool Clt  v1 v2
  | Lt Unsigned => Val.cmpu_bool valid_ptr Clt  v1 v2
  | Le Signed => Val.cmp_bool Cle  v1 v2
  | Le Unsigned => Val.cmpu_bool valid_ptr Cle  v1 v2
  | SEt         => Val.cmp_bool Cne (Val.and v1 v2) (Vint Int.zero)
  | Ne          => Val.cmp_bool Cne v1 v2
  end.

Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
    | Some true  => goto_label f l rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
  end.


Definition eval_reg_imm (rs : regset) (ri: preg+imm)  : val :=
  match ri with
  | inl r => rs#r
  | inr i => Vint i
  end.

Definition exec_binop (o: binOp)  (r: preg) (ri: preg+imm) (rs: regset) (m: mem) :=
  match eval_binop o (rs#r) (eval_reg_imm rs ri) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#r <- v)) m
  end.

Definition exec_load (k: memory_chunk) (r:preg) (r':preg) (o:Ptrofs.int) (rs: regset) (m:mem) :=
  match Mem.loadv k m (Val.offset_ptr rs#r' o) with
                       | None => Stuck
                       | Some v => Next (nextinstr (rs#r <- v)) m
  end.

Definition exec_store (k: memory_chunk) (r:preg) (r':preg) (o:Ptrofs.int) (rs: regset) (m:mem) :=
  match Mem.storev k m (Val.offset_ptr rs#r o) rs#r' with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

Definition exec_instr (f: function) (i: instruction) (rs:regset) (m: mem) : outcome :=
  match i with
  | NEG r => Next (nextinstr  (rs#r <- (Val.neg rs#r))) m
  | BINARY o r ri =>  exec_binop o r ri rs m
  | JA o          =>  goto_label f o rs m
  | JUMP c r  ri o =>
      eval_branch f o rs m (eval_cond (Mem.valid_pointer m) c (rs#r) (eval_reg_imm rs ri))
  | LDDW_low r i    => Next (nextinstr (rs#r <- (Vint i))) m
  | LDDW_high r i   => Next (nextinstr (rs#r <- (Val.add (Val.shl (Vint i) (Vint (Int.repr 16))) (rs#r)))) m
  | LDX k r r' o    => exec_load k r r' o rs m
  | ST k r r' o     => exec_store k r r' o rs m
  | Plabel l         => Next (nextinstr rs) m
  | _ => Stuck
  end.
