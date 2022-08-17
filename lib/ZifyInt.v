Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import ZifyClasses ZifyBool.

Lemma cst : forall i : int, 0 <= Int.unsigned i < 4294967296.
Proof.
  exact Int.unsigned_range.
Qed.

Instance Int : InjTyp int Z :=
  mkinj _ _ Int.unsigned (fun x => 0 <= x < 4294967296) cst.
Add Zify InjTyp Int.

Instance Repr : UnOp Int.repr :=
  { TUOp := (fun x => x mod 4294967296) ;  TUOpInj := Int.unsigned_repr_eq }.
Add Zify UnOp Repr.

Program Instance Unsigned : UnOp Int.unsigned :=
  {| TUOp := (fun x => x)  ;  TUOpInj := _ |}.
Add Zify UnOp Unsigned.

(*
Lemma signed_unsigned : forall x,
    Int.signed x = (Int.unsigned x + Int.half_modulus) mod Int.modulus - Int.half_modulus.
Proof.
  unfold Int.signed. intros.
  pose proof (Int.unsigned_range x).
  destruct (zlt (Int.unsigned x) Int.half_modulus).
  - rewrite Z.mod_small. ring.
    rewrite Int.half_modulus_modulus. lia.
  - replace (Int.unsigned x + Int.half_modulus) with ((Int.unsigned x + Int.half_modulus - Int.modulus) + 1 * Int.modulus) by ring.
  rewrite Z.mod_add. rewrite Z.mod_small. ring.
  rewrite Int.half_modulus_modulus in *.  lia.
  generalize Int.modulus_pos. lia.
Qed.

Program Instance Signed : UnOp Int.signed :=
  {| TUOp := (fun x => (x  + 2147483648) mod 4294967296 - 2147483648)  ;  TUOpInj := signed_unsigned |}.
Add Zify UnOp Signed.
*)

Definition signed (x:Z) := if Z.ltb x Int.half_modulus then x else x - Int.modulus.


Program Instance Signed : UnOp Int.signed :=
  {| TUOp := signed ;  TUOpInj := _ |}.
Next Obligation.
  unfold Int.signed, signed.
  destruct (zlt (Int.unsigned x) Int.half_modulus).
  rewrite Zaux.Zlt_bool_true by auto. reflexivity.
  rewrite Zaux.Zlt_bool_false. reflexivity. lia.
Qed.
Add Zify UnOp Signed.


Program Instance ADD : BinOp Int.add :=
  { TBOp := (fun x y => (x  + y) mod 4294967296) ;  TBOpInj := _ }.
Next Obligation.
  unfold Int.add.
  rewrite Int.unsigned_repr_eq.
  reflexivity.
Qed.
Add Zify BinOp ADD.

Program Instance MUL : BinOp Int.mul :=
  { TBOp := (fun x y => (x  * y) mod 4294967296) ;  TBOpInj := _ }.
Next Obligation.
  unfold Int.mul.
  rewrite Int.unsigned_repr_eq.
  reflexivity.
Qed.
Add Zify BinOp MUL.

Program Instance AND : BinOp Int.and :=
  { TBOp := (fun x y => (Z.land x y) mod 4294967296) ;  TBOpInj := _ }.
Next Obligation.
  unfold Int.and.
  rewrite Int.unsigned_repr_eq.
  reflexivity.
Qed.
Add Zify BinOp AND.

Program Instance NEG : UnOp Int.neg :=
  { TUOp := (fun x =>  (- x) mod 4294967296) ;  TUOpInj := _ }.
Next Obligation.
  unfold Int.neg.
  rewrite Int.unsigned_repr_eq.
  reflexivity.
Qed.
Add Zify UnOp NEG.

Program Instance SUB : BinOp Int.sub :=
  { TBOp := (fun x y => (x  - y) mod 4294967296) ;  TBOpInj := _ }.
Next Obligation.
  unfold Int.sub.
  rewrite Int.unsigned_repr_eq.
  reflexivity.
Qed.
Add Zify BinOp SUB.

Instance Cst_modulus : CstOp Int.modulus := { TCst := 4294967296; TCstInj := eq_refl }.
Add Zify CstOp Cst_modulus.

Instance Cst_half_modulus : CstOp Int.half_modulus := { TCst := 2147483648; TCstInj := eq_refl }.
Add Zify CstOp Cst_half_modulus.



Program Instance MODU : BinOp Int.modu :=
  { TBOp := (fun x y => x  mod y)  ;  TBOpInj := _ }.
Next Obligation.
  unfold Int.modu.
  rewrite Int.unsigned_repr_eq.
  rewrite Z.mod_small.
  reflexivity.
  assert (Int.unsigned m = 0 \/ Int.unsigned m <> 0) by lia.
  destruct H. rewrite H.
  rewrite Zmod_0_r. compute. intuition congruence.
  generalize (Z_mod_remainder (Int.unsigned n) (Int.unsigned m) H).
  unfold Remainder.
  lia.
Qed.
Add Zify BinOp MODU.

Program Instance ZEROEXT : BinOp Int.zero_ext :=
  { TBOp := fun x y => (Zbits.Zzero_ext x y) mod 4294967296  ;  TBOpInj := _ }.
Next Obligation.
unfold Int.zero_ext.
rewrite Int.unsigned_repr_eq.
reflexivity.
Qed.
Add Zify BinOp ZEROEXT.

Definition proj1' [P1 P2:Prop] (P : P1/\ P2) : P1.
Proof.
  destruct P.
  exact H.
Defined.

Definition proj2' [P1 P2:Prop] (P : P1/\ P2) : P2.
Proof.
  destruct P.
  exact H0.
Defined.

Lemma and_conj : forall (P1 P2: Prop)
                        (P : P1 /\ P2),
    conj (proj1' P) (proj2' P) = P.
Proof.
  intros.
  destruct P.
  reflexivity.
Qed.

Lemma inj_eq : forall n m,
    n = m <-> Int.unsigned n = Int.unsigned m.
Proof.
  split ; intros.
  - congruence.
  - unfold Int.unsigned in H.
    destruct n,m.
    simpl in *.
    subst.
    f_equal.
    unfold Z.lt in *.
    assert (proj1' intrange = proj1' intrange0).
    {
      apply Eqdep_dec.UIP_dec.
      decide equality.
    }
    assert (proj2' intrange = proj2' intrange0).
    {
      apply Eqdep_dec.UIP_dec.
      decide equality.
    }
    destruct intrange0.
    destruct intrange.
    simpl in *.
    congruence.
Qed.

Instance eq_int : BinRel (@eq int)  :=  {| TR := @eq Z ; TRInj := inj_eq |}.
Add Zify BinRel eq_int.

Instance Cst_max_unsigned : CstOp Int.max_unsigned := { TCst := 4294967295 ; TCstInj := eq_refl }.
Add Zify CstOp Cst_max_unsigned.

Instance Cst_mone : CstOp Int.mone := { TCst := 4294967295 ; TCstInj := eq_refl }.
Add Zify CstOp Cst_mone.

Instance Cst_one : CstOp Int.one := { TCst := 1 ; TCstInj := eq_refl }.
Add Zify CstOp Cst_one.

Instance Cst_zero : CstOp Int.zero := { TCst := 0 ; TCstInj := eq_refl }.
Add Zify CstOp Cst_zero.


Instance Cst_zwordsize : CstOp Int.zwordsize := { TCst := 32; TCstInj := eq_refl }.
Add Zify CstOp Cst_zwordsize.

Program Instance CmpuCle : BinOp (Int.cmpu Cle) := {TBOp := Z.leb ; TBOpInj := _ }.
Next Obligation.
  unfold Int.ltu.
  destruct (zlt (Int.unsigned m) (Int.unsigned n)).
  lia. lia.
Qed.
Add Zify BinOp CmpuCle.

Program Instance CmpuCeq : BinOp (Int.cmpu Ceq) := {TBOp := Z.eqb ; TBOpInj := _ }.
Next Obligation.
  unfold Int.eq.
  destruct (zeq (Int.unsigned n) (Int.unsigned m)).
  lia. lia.
Qed.
Add Zify BinOp CmpuCeq.

Program Instance CmpuClt : BinOp (Int.cmpu Clt) := {TBOp := Z.ltb ; TBOpInj := _ }.
Next Obligation.
  unfold Int.ltu.
  destruct (zlt (Int.unsigned n) (Int.unsigned m)).
  lia. lia.
Qed.
Add Zify BinOp CmpuClt.


Program Instance Inteq : BinOp Int.eq := {TBOp := Z.eqb ; TBOpInj := _ }.
Next Obligation.
  unfold Int.eq.
  destruct (zeq (Int.unsigned n) (Int.unsigned m)).
  lia. lia.
Qed.
Add Zify BinOp Inteq.

Program Instance Ltu : BinOp Int.ltu := {TBOp := Z.ltb ; TBOpInj := _ }.
Next Obligation.
  unfold Int.ltu.
  destruct (zlt (Int.unsigned n) (Int.unsigned m)).
  lia. lia.
Qed.
Add Zify BinOp Ltu.

Program Instance Zzero_ext_spec : BinOpSpec Zbits.Zzero_ext :=
  { BPred n m r := (n < 0 -> r = 0) /\ (0 <= n -> r = m mod 2 ^n) ; BSpec := _}.
Next Obligation.
  split.
  - intros.
    destruct x ; try lia. reflexivity.
  - intros.
    rewrite Zbits.Zzero_ext_mod by auto.
    f_equal.
    apply two_p_correct.
Qed.
Add Zify BinOpSpec Zzero_ext_spec.

Lemma unsigned_ptrofs : forall i : Ptrofs.int, 0 <= Ptrofs.unsigned i < 4294967296.
Proof.
  exact Ptrofs.unsigned_range.
Qed.

Instance Ptrofs : InjTyp Ptrofs.int Z :=
  mkinj _ _ Ptrofs.unsigned (fun x => 0 <= x < 4294967296) unsigned_ptrofs.
Add Zify InjTyp Ptrofs.

Instance PtrofsRepr : UnOp Ptrofs.repr :=
  { TUOp := (fun x => x mod 4294967296) ;  TUOpInj := Ptrofs.unsigned_repr_eq }.
Add Zify UnOp PtrofsRepr.

Program Instance PtrofsUnsigned : UnOp Ptrofs.unsigned :=
  {| TUOp := (fun x => x)  ;  TUOpInj := _ |}.
Add Zify UnOp PtrofsUnsigned.

Program Instance PtrofsOf_int : UnOp Ptrofs.of_int :=
  {| TUOp := (fun x => x mod 4294967296)  ;  TUOpInj := _ |}.
Next Obligation.
  unfold Ptrofs.of_int.
  rewrite Ptrofs.unsigned_repr_eq. reflexivity.
Qed.
Add Zify UnOp PtrofsOf_int.

Program Instance PtrofsLtu : BinOp Ptrofs.ltu := {TBOp := Z.ltb ; TBOpInj := _ }.
Next Obligation.
  unfold Ptrofs.ltu.
  destruct (zlt (Ptrofs.unsigned n) (Ptrofs.unsigned m)).
  lia. lia.
Qed.
Add Zify BinOp PtrofsLtu.

Program Instance PtrofsAdd : BinOp Ptrofs.add := {TBOp := (fun x y => (x  + y) mod 4294967296) ; TBOpInj := _ }.
Next Obligation.
  unfold Ptrofs.add.
  rewrite Ptrofs.unsigned_repr_eq.
  reflexivity.
Qed.
Add Zify BinOp PtrofsAdd.

Program Instance PtrofsSub : BinOp Ptrofs.sub := {TBOp := (fun x y => (x - y) mod 4294967296) ; TBOpInj := _ }.
Next Obligation.
  unfold Ptrofs.sub.
  rewrite Ptrofs.unsigned_repr_eq.
  reflexivity.
Qed.
Add Zify BinOp PtrofsSub.

Program Instance PtrofsTo_int : UnOp Ptrofs.to_int := {TUOp := (fun x => x) ; TUOpInj := _ }.
Next Obligation.
  unfold Ptrofs.to_int.
  rewrite Int.unsigned_repr_eq.
  rewrite Zmod_small. reflexivity.
  apply Ptrofs.unsigned_range.
Qed.
Add Zify UnOp PtrofsTo_int.

Lemma ptrofs_eq : forall n m,
    n = m <-> Ptrofs.unsigned n = Ptrofs.unsigned m.
Proof.
  split ; intros.
  - congruence.
  - unfold Ptrofs.unsigned in H.
    destruct n,m.
    simpl in *.
    subst.
    f_equal.
    unfold Z.lt in *.
    assert (proj1' intrange = proj1' intrange0).
    {
      apply Eqdep_dec.UIP_dec.
      decide equality.
    }
    assert (proj2' intrange = proj2' intrange0).
    {
      apply Eqdep_dec.UIP_dec.
      decide equality.
    }
    destruct intrange0.
    destruct intrange.
    simpl in *.
    congruence.
Qed.


Instance eq_ptrofs : BinRel (@eq ptrofs)  :=  {| TR := @eq Z ; TRInj := ptrofs_eq |}.
Add Zify BinRel eq_ptrofs.

Lemma signed_spec : forall  x : Z,
    x < 2147483648 /\ signed x = x \/
      x >= 2147483648 /\ signed x = x - 4294967296.
Proof.
  unfold signed. intros.
  destruct (x <? Int.half_modulus) eqn:T.
  lia. lia.
Qed.

Program Instance SignedSpec : UnOpSpec signed :=
  { UPred := (fun x r => ((x < 2147483648 /\ r = x)) \/ (x >= 2147483648 /\ r = x - 4294967296)) ; USpec := _ }.
Next Obligation.
  apply signed_spec.
Qed.
Add Zify UnOpSpec SignedSpec.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
