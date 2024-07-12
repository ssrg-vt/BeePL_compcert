(* *********************************************************************)
(*           Emulation of mulhs, mulhu                                 *)
(*       Frédéric Besson (frederic.besson@inria.fr), Inria Rennes      *)
(* *********************************************************************)

Require Import Coqlib Errors Maps.
Require Import AST Zbits Integers Floats Values Memory Globalenvs.

Definition mulhu' (x y:Int.int) : Int.int :=
  Int64.hiword (Int64.mul (Int64.repr (Int.unsigned x)) (Int64.repr (Int.unsigned y))).

Definition mulhs' (x y:Int.int) : Int.int :=
  Int64.hiword (Int64.mul (Int64.repr (Int.signed x)) (Int64.repr (Int.signed y))).

#[ global] Hint Resolve Int64.int_unsigned_range : mulh.

Lemma int64_max_unsigned_pos : Int64.max_unsigned > 0.
Proof.
  compute; congruence.
Qed.

#[ global] Hint Resolve int64_max_unsigned_pos : mulh.

Lemma unsigned_repr_int_unsigned : forall x,
    Int64.unsigned (Int64.repr (Int.unsigned x)) = Int.unsigned x.
Proof.
  intros.
  rewrite Int64.unsigned_repr; auto with mulh.
Qed.

Lemma signed_repr_int_signed : forall x,
    Int64.signed (Int64.repr (Int.signed x)) = Int.signed x.
Proof.
  intros. rewrite Int64.signed_repr;auto.
  generalize (Int.signed_range x).
  assert (Int64.min_signed <= Int.min_signed).
  { compute. congruence. }
    assert (Int.max_signed <= Int64.max_signed).
  { compute. congruence. }
  lia.
Qed.

Lemma mulhu_eq : forall x y, Int.mulhu x y = mulhu' x y.
Proof.
  unfold Int.mulhu, mulhu'.
  intros. unfold Int64.hiword.
  symmetry.
  f_equal.
  rewrite Int64.shru_div_two_p.
  change (two_p (Int64.unsigned (Int64.repr Int.zwordsize))) with (Int.modulus).
  assert (MULB : 0 <= Int.unsigned x * Int.unsigned y <= Int64.max_unsigned).
  {
    generalize (Int.unsigned_range_2 x).
    generalize (Int.unsigned_range_2 y).
    assert (Int.max_unsigned * Int.max_unsigned <= Int64.max_unsigned).
    { compute. congruence. }
    nia.
  }
  unfold Int64.mul.
  rewrite! Int64.unsigned_repr;auto with mulh;
    rewrite! Int64.unsigned_repr; auto with mulh.
  { apply Zdiv_interval_2;auto.
    lia. generalize int64_max_unsigned_pos; lia.
    apply Int.modulus_pos.
  }
  rewrite! unsigned_repr_int_unsigned; auto.
Qed.

Lemma hiword_shrl : forall i, Int64.hiword i = Int64.loword (Int64.shr' i (Int.repr 32)).
Proof.
  intros.
  apply Int.same_bits_eq.
  intros.
  rewrite Int64.bits_hiword by auto.
  rewrite Int64.bits_loword by auto.
  assert (LT : 2 * Int.zwordsize = Int64.zwordsize) by (compute; congruence).
  rewrite Int64.bits_shr' by lia.
  destruct (zlt (i0 + Int.unsigned (Int.repr 32)) Int64.zwordsize).
  reflexivity.
  change (Int.unsigned (Int.repr 32)) with Int.zwordsize in g.
  lia.
Qed.

Lemma zmod_small_add : forall a b,
    0 <= a + b < b ->
    a mod b = a + b.
Proof.
  intros.
  rewrite <- (Z_mod_plus_full a 1).
  rewrite Zmod_small. ring.
  lia.
Qed.

Lemma signed_unsigned_diff0 : forall x,
    Int.signed x <> 0 -> Int.unsigned x <> 0.
Proof.
  intros.
  intro.
  unfold Int.signed in H.
  destruct (zlt (Int.unsigned x) Int.half_modulus).
  tauto. generalize Int.half_modulus_pos. lia.
Qed.


Lemma mulhs_eq : forall x y, Int.mulhs x y = mulhs' x y.
Proof.
  unfold Int.mulhs, mulhs'.
  intros.
  unfold Int64.hiword.
  rewrite Int64.shru_div_two_p.
  change (two_p (Int64.unsigned (Int64.repr Int.zwordsize))) with (Int.modulus).
  rewrite Int64.mul_signed.
  rewrite! signed_repr_int_signed.
  rewrite Int64.unsigned_repr.
  {
    rewrite Int64.unsigned_repr_eq.
    destruct (Z.eq_dec (Int.signed x) 0) as [ZX |NZX].
    rewrite ZX. reflexivity.
    destruct (Z.eq_dec (Int.signed y) 0) as [ZY |NZY].
    rewrite ZY. rewrite Z.mul_0_r. reflexivity.
    apply signed_unsigned_diff0 in NZX.
    apply signed_unsigned_diff0 in NZY.
    apply Int.same_bits_eq. intros.
    rewrite! Int.testbit_repr by auto.
    change Int.modulus with (2^32).
    change Int64.modulus with (2^64).
    rewrite Z.div_pow2_bits  by lia.
    rewrite Z.div_pow2_bits  by lia.
    rewrite Z.testbit_mod_pow2 by lia.
    destruct (i + 32 <? 64) eqn:LT.
    reflexivity.
    simpl.
    rewrite Z.ltb_ge in LT.
    change Int.zwordsize with 32 in H. lia.
  }
  { apply Zdiv_interval_2;auto.
    apply Int64.unsigned_range_2.
    lia. generalize int64_max_unsigned_pos;lia.
    apply Int.modulus_pos.
  }
Qed.
