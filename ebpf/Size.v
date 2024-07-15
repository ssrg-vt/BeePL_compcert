(* *********************************************************************)
(*           Check range                                               *)
(*       Frédéric Besson (frederic.besson@inria.fr), Inria Rennes      *)
(* *********************************************************************)

Require Import Coqlib Errors Maps.
Require Import AST Zbits Integers Floats Values Memory Globalenvs.

Module Ptrofs.

  Definition is_16_signed (p:ptrofs) :=
    let i := Ptrofs.signed p in
    Z.leb (-(2^15)) i && Z.leb i (2^15 - 1).

  Definition is_int (n:ptrofs) :=
    if negb Archi.ptr64 then true
    else
      let i := Ptrofs.signed n in
      Z.leb Int.min_signed i && Z.leb i Int.max_signed.


End Ptrofs.
