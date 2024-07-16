(* *********************************************************************)
(*           Check range                                               *)
(*       Frédéric Besson (frederic.besson@inria.fr), Inria Rennes      *)
(* *********************************************************************)

Require Import Coqlib Errors Maps.
Require Import AST Zbits Integers Floats Values Memory Globalenvs.

Definition is_16_signed (n:Z) :=
  Z.leb (-(2^15)) n && Z.leb n (2^15 - 1).

Definition is_int (n:Z) :=
  Z.leb Int.min_signed n && Z.leb n Int.max_signed.

Module Ptrofs.

  Definition is_16_signed (p:ptrofs) :=
    is_16_signed (Ptrofs.signed p).

  Definition is_int (n:ptrofs) :=
    if negb Archi.ptr64 then true
    else is_int (Ptrofs.signed n).

End Ptrofs.

Module Int64.

  Definition is_16_signed (p:int64) :=
    is_16_signed (Int64.signed p).

  Definition is_int (n:int64) :=
    if negb Archi.ptr64 then true
    else is_int (Int64.signed n).

End Int64.

Module Int.

  Definition is_16_signed (p:int) :=
    is_16_signed (Int.signed p).

End Int.
