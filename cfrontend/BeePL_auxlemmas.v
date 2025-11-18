Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy Coqlib Errors.

From mathcomp Require Import all_ssreflect. 

Definition access_modeBC (t : type) : mode :=
  match t with
  | Vtype Tbool => By_value Mint8unsigned
  | Vtype (Tint IBool _ _) => By_value Mbool
  | Stype _ _ | Bytes => By_copy
  | _ => access_mode_type t
  end.
(*
Definition access_modeBC (t : type) : mode :=
  match t with
  | Vtype pt => match pt with
               | Tbool => By_value Mint8unsigned
               | pt => access_mode_prim pt
               end
  | t => access_mode_type t
  end.
*)

Lemma access_mode_preserved : forall ty cty md,
access_modeBC ty = md ->
transBeePL_type ty =  cty ->
Ctypes.access_mode cty = md.
Proof.
induction ty.
- induction md; simpl; intros; inv H; subst; auto.
- induction md; simpl; intros; destruct p; simpl in *.
    * injection H. intros. subst. auto.
    * destruct i.
      destruct s; injection H; intros; subst; auto.
      destruct s; injection H; intros; subst; auto.
    * destruct s; injection H; intros; subst; auto.
    * destruct s; injection H; intros; subst; auto.
    * destruct s; injection H; intros; subst; auto.
    * inv H. destruct i; inv H.
      destruct s; inv H2.
      destruct s; inv H2. inv H.
      inv H. destruct i; inv H.
      destruct s; inv H2. destruct s; inv H2.
      inv H. inv H. destruct i; inv H.
      destruct s; inv H2. destruct s; inv H2.
      inv H.
- simpl. intros. subst.
  admit.
- simpl. intros. subst. auto.
- simpl. intros. subst. auto.
- simpl. intros. subst. auto.
- simpl. intros. subst. simpl. auto.
Admitted.

Lemma non_volatile_type_preserved : forall ty cty b,
type_is_volatile (transBeePL_type ty) = b ->
transBeePL_type ty = cty ->
Ctypes.type_is_volatile cty = b.
Proof.
intros. Search type_is_volatile.
induction ty.
- induction cty; simpl in *; try (rewrite <- H0; auto).
  + auto.
- induction cty; simpl in *; try (rewrite <- H0; auto).
- induction cty; simpl in *; try (rewrite <- H0; auto).
- induction cty; simpl in *; try (rewrite <- H0; auto).
- induction cty; simpl in *; try (rewrite <- H0; auto).
- induction cty; simpl in *; try (rewrite <- H0; auto).
- induction cty; simpl in *; try (rewrite <- H0; auto).
Qed.

(* Lemma typec_expr : forall e ct ce g' g'' i',
transBeePL_type (typeof_expr e) = ct ->
transBeePL_expr_expr e  g' = Res ce g'' i' ->
ct = Csyntax.typeof ce.
Proof.
Admitted. *)

Lemma bv_cv_reflex : forall v' v,
trans_cvalue_bvalue v' = OK v ->
trans_bvalue_cvalue v = v'.
Proof.
  intros v' v H.
  destruct v' eqn:?; simpl in *; try discriminate;
  inv H; reflexivity.
Qed.

Lemma bc_cv_comp : forall v,
trans_cvalue_bvalue (trans_bvalue_cvalue v) = OK v.
Proof.
intros.
induction v eqn:?.
- Locate trans_cvalue_bvalue.
  (* Can't be proved without fixing Vunit issue in trans_bvalue_cvalue*)
Admitted.


(* Since translation of types does not depend on the generator, it 
   should produce the same result irrespective of them *)
(* Coqlib.v has lot of lemmas related to Ple *)
Lemma type_preserved_generator : forall t r r' ,
transBeePL_type t = r ->
transBeePL_type t = r'->
r = r'.
Proof. (* use inductive principle proved in BeeTypes.v *)
intros. induction H. induction H0. auto.
Qed.

Lemma eq_bt: forall t t',
    eq_basic_type t t' ->
    t = t'.
intros. induction t; induction t'; try inv H.
induction p; induction p0; try inv H; auto.
simpl in H1. apply diff_false_true in H1. inv H1.
simpl in H1. apply diff_false_true in H1. inv H1.
simpl in H1. apply diff_false_true in H1. inv H1.
simpl in H1. induction i; induction i0; induction s; induction s0;
  try discriminate; try auto;
  try (destruct (attr_eq _ _) eqn:Heq; simpl in *; try discriminate;
    rewrite e; reflexivity).
simpl in H1. apply diff_false_true in H1. inv H1.
simpl in H1. apply diff_false_true in H1. inv H1.
simpl in H1. apply diff_false_true in H1. inv H1.
simpl in H1. induction s; induction s0;
  try discriminate; try auto;
  try (destruct (attr_eq _ _) eqn:Heq; simpl in *; try discriminate;
    rewrite e; reflexivity).
apply andb_prop in H1. destruct H1.
apply Pos.eqb_eq in H. destruct (attr_eq _ _) eqn:Heq; subst; auto.
simpl in *. discriminate.
apply andb_prop in H1. destruct H1. apply andb_prop in H.
destruct H. apply Z.eqb_eq in H1.
destruct (attr_eq _ _) eqn:Heqa; simpl in *; try discriminate; subst; auto.
destruct p; destruct p0; try inv H; simpl in *; auto.
destruct i; destruct i0; destruct s; destruct s0;
  simpl in *; try discriminate; try auto.
    destruct (attr_eq a a1) eqn:Heq; simpl in *; try discriminate; rewrite e; auto.
    destruct (attr_eq a a1) eqn:Heq; simpl in *; try discriminate; rewrite e; auto.
    destruct (attr_eq a a1) eqn:Heq; simpl in *; try discriminate; rewrite e; auto.
    destruct (attr_eq a a1) eqn:Heq; simpl in *; try discriminate; rewrite e; auto.
    destruct (attr_eq a a1) eqn:Heq; simpl in *; try discriminate; rewrite e; auto.
    destruct (attr_eq a a1) eqn:Heq; simpl in *; try discriminate; rewrite e; auto.
    destruct (attr_eq a a1) eqn:Heq; simpl in *; try discriminate; rewrite e; auto.
    destruct (attr_eq a a1) eqn:Heq; simpl in *; try discriminate; rewrite e; auto.
simpl in *.
destruct s; destruct s0;
  simpl in *; try discriminate; try auto.
    destruct (attr_eq a a1) eqn:Heq; simpl in *; try discriminate; subst; auto.
    destruct (attr_eq a a1) eqn:Heq; simpl in *; try discriminate; subst; auto.
Qed.

Lemma eq_prim : forall t t',
    eq_primitive_type t t' = true ->
    t = t'.
Proof.
  intro t. induction t.
  induction t'; intros; simpl in *; try discriminate; try inv H; auto.
  induction t'; intros; simpl in *; try discriminate; try inv H; auto.
  destruct i; destruct i0; destruct s; destruct s0;
    destruct (attr_eq a a0) eqn:Heq; simpl in *; try discriminate; rewrite e; auto.
  induction t'; intros; simpl in *; try discriminate; try inv H; auto.
destruct s; destruct s0;
    destruct (attr_eq a a0) eqn:Heq; simpl in *; try discriminate; rewrite e; auto.
Qed.

Lemma eq_typ : forall t t',
    eq_type t t'->
    t = t'.
Proof.
  intro t. induction t.
  induction t'; try discriminate; try auto.
  induction t'; try discriminate; try auto.
  - induction p; induction p0; try inv H1; try discriminate; auto.
    intros.
  destruct i; destruct i0; destruct s; destruct s0; try discriminate; auto;
    destruct (attr_eq a a0) eqn:Heq; simpl in *; try discriminate; subst; auto.
  rewrite Heq in H. unfold proj_sumbool in H. simpl in H. discriminate.
  rewrite Heq in H. unfold proj_sumbool in H. simpl in H. discriminate.
  rewrite Heq in H. unfold proj_sumbool in H. simpl in H. discriminate.
  rewrite Heq in H. unfold proj_sumbool in H. simpl in H. discriminate.
  rewrite Heq in H. unfold proj_sumbool in H. simpl in H. discriminate.
  rewrite Heq in H. unfold proj_sumbool in H. simpl in H. discriminate.
  rewrite Heq in H. unfold proj_sumbool in H. simpl in H. discriminate.
  rewrite Heq in H. unfold proj_sumbool in H. simpl in H. discriminate.
  intros. destruct s; destruct s0; try discriminate; auto;
    destruct (attr_eq a a0) eqn:Heq; simpl in *; try discriminate; subst; auto.
  rewrite Heq in H. unfold proj_sumbool in H. simpl in H. discriminate.
  rewrite Heq in H. unfold proj_sumbool in H. simpl in H. discriminate.
- induction t'; try discriminate; try inv H.
  revert p0. induction p; induction p0; try discriminate; try inv H.
  intros.
  destruct i; destruct i0; destruct b; destruct b0; try discriminate; auto;
    destruct (attr_eq a a0) eqn:Heq; simpl in *; try discriminate; subst; auto;
  apply andb_prop in H; destruct H; try apply andb_prop in H; destruct H;
  try apply Pos.eqb_eq in H; try apply eq_prim in H1; subst; auto;
  try (rewrite Heq in H0; unfold proj_sumbool in H0; simpl in H0; discriminate);
  try (apply andb_prop in H1; destruct H1; apply Pos.eqb_eq in H; subst;
  destruct (attr_eq a1 a2) eqn:Heqa; subst; auto); simpl in *; try discriminate.
  try (apply andb_prop in H1; destruct H1; apply andb_prop in H; destruct H;
  apply Z.eqb_eq in H2; subst; apply eq_prim in H; subst;
  destruct (attr_eq a1 a2) eqn:Heqa; subst; auto; discriminate).

  try (apply andb_prop in H1; destruct H1; apply andb_prop in H; destruct H;
  apply Z.eqb_eq in H2; subst; apply eq_prim in H; subst;
  destruct (attr_eq a1 a2) eqn:Heqa; subst; auto; discriminate). symmetry in Heq.
  rewrite <- Heq in H0. simpl in H0. symmetry in H0. apply eq_prim in H0. subst.
  auto. admit.
  destruct (attr_eq a1 a2) eqn:Heqa; subst; auto; discriminate.
  destruct (attr_eq a1 a2) eqn:Heqa; subst; auto; try discriminate.
  apply andb_prop in H. destruct H. apply Z.eqb_eq in H2. apply eq_prim in H. subst.
  auto.
intros. simpl in *. specialize IHp with p0. apply IHp in H.
Admitted.

Lemma eq_type_trans : forall t t' t'',
eq_type t t' ->
transBeePL_type t' = t'' ->
t'' = transBeePL_type t. 
Proof.
Admitted.

Lemma eq_ptr: forall t t',
    eq_ptr_type t t' ->
    t = t'.
Proof.
  Admitted.
  (*
intros.
induction t; induction t'; try inv H.
 apply andb_prop in H1 as [H01 H02].
    apply andb_prop in H01 as [H01 H03].
    apply Pos.eqb_eq in H01. simpl in *.
    apply eq_bt in H03.
    subst.
    destruct (attr_eq _ _) eqn: Heqa; simpl in *; try discriminate; subst; auto.
    simpl in *. admit.
 apply andb_prop in H1 as [H01 H02].
    apply andb_prop in H01 as [H01 H03].
    destruct t t0.
*)



Lemma eq_type_trans : forall t t' t'',
eq_type t t' ->
transBeePL_type t' = t'' ->
t'' = transBeePL_type t. 
Proof.
induction t.
- induction t'; intros; auto; try inv H.
- induction t'; intros; auto; try inv H.
  apply eq_prim in H2. subst. auto.
- induction t'; intros; auto; try inv H.
  induction p; induction p0; auto; try inv H;
  try (simpl in H2; apply diff_false_true in H2; inv H2).
  simpl in H2. apply andb_prop in H2. destruct H2.
  apply andb_prop in H. destruct H.
  apply eq_bt in H1. apply Pos.eqb_eq in H.
  destruct (attr_eq a a0) eqn:Heqa; simpl in *; try discriminate.
  subst. auto. inv H2. admit.
  admit. admit.
Admitted.  
(*
- induction t'; auto; try inv H.
  simpl in *. destruct p; destruct p0; try inv H2.
  + apply andb_prop in H0 as [H01 H02].
    apply andb_prop in H01 as [H01 H03].
    apply Pos.eqb_eq in H01. subst. simpl in *.
    apply eq_bt in H03.
    destruct (attr_eq _ _) eqn:Heqa; simpl in *; subst.
    auto. discriminate.
  + simpl in *.





  destruct b; destruct b0. destruct (attr_eq _ _) eqn:Heqa.
  subst.
  destruct p; destruct p0; auto; try discriminate.
  simpl in *.
  destruct i; destruct s;
    destruct i1; destruct s0;
    try (destruct (attr_eq _ _) eqn:Heq; simpl in *; try discriminate;
    rewrite e; reflexivity).
  simpl in *.
  destruct s; destruct s0;
        try (destruct (attr_eq _ _) eqn:Heq; simpl in *; try discriminate;
    rewrite e; reflexivity).
   destruct p; destruct p0; auto; try discriminate.
   simpl in *; apply diff_false_true in H03; inv H03.
   simpl in *; apply diff_false_true in H03; inv H03.
   simpl in *; apply diff_false_true in H03; inv H03.
   simpl in *. apply andb_prop in H03. destruct H03.
   destruct (attr_eq a1 a2) eqn:Heqa. subst.
   apply Pos.eqb_eq in H. subst. destruct (attr_eq a a0) eqn:Heqa1.
   subst. auto. simpl in *. apply diff_false_true in H02; inv H02.
   simpl in *. apply diff_false_true in H0. inv H0.
  simpl in *.apply diff_false_true in H03. inv H03.
  simpl in *; apply diff_false_true in H03; inv H03.
  simpl in *; apply diff_false_true in H03; inv H03.




  
    try (destruct (attr_eq _ _) eqn:Heq; simpl in H2; try discriminate;
    rewrite e; reflexivity).
  apply eq_basic_type_spec in H02. inversion H02; subst.
  apply attr_eq_spec in H03. inversion H03; subst.
  simpl in *.
  auto.
  simpl.
  simpl in H2.
-
subst.
*)


(*** Auxillary lemmas related to types and effects ***)
Lemma eq_effect_refl : forall a,
eq_effect_label a a = true.
Proof.
  intros. unfold eq_effect_label.
  destruct a; auto; try(rewrite Pos.eqb_refl; auto).
Qed.

Lemma sub_effect_ss : forall a ef1 ef2,
    sub_effect (a::ef1) (a :: ef2) ->
    sub_effect ef1 ef2.
Proof.
  intros. simpl in H. rewrite eq_effect_refl in H. auto.
Qed.

(* Complete Me: Easy *)
Lemma sub_effect_refl : forall ef, 
sub_effect ef ef = true.
Proof.
induction ef; auto.
simpl. rewrite eq_effect_refl. auto.
Qed.

Lemma sub_effect_nil : forall ef, 
sub_effect nil ef = true.
Proof.
intros. induction ef; auto.
Qed.

Lemma sub_effect_1s : forall a ef1 ef2,
    sub_effect ef1 ef2 ->
    sub_effect ef1 (a :: ef2).
Proof.
  intros a ef1. generalize dependent a. induction ef1.
  - auto.
  - intros. simpl. destruct (eq_effect_label a a0); auto.
    induction ef2.
    + inv H.
    + apply IHef1. simpl in H. destruct (eq_effect_label a a1); auto.
Qed.

Lemma sub_effect_1c : forall ef1 ef2 ef3,
    sub_effect ef1 ef2 ->
    sub_effect ef1 (ef3 ++ ef2).
Proof.
  intros. induction ef3.
  - auto.
  - Search cat. rewrite cat_cons. apply sub_effect_1s. auto.
Qed.

Lemma eq_effect_trans: forall a a0 a1,
    eq_effect_label a a0 ->
    eq_effect_label a a1 ->
    eq_effect_label a0 a1.
Proof.
  intros. induction a.
  induction a0; induction a1; auto; try(inv H).
  induction a0; induction a1; auto; try(inv H1).
  induction a0; induction a1; auto; try(inv H).
  + apply Peqb_true_eq in H2. subst. auto.
  induction a0; induction a1; auto; try(inv H).
  +  apply Peqb_true_eq in H2. subst. auto.
  induction a0; induction a1; auto; try(inv H).
  +  apply Peqb_true_eq in H2. subst. auto.
  induction a0; induction a1; auto; try(inv H1).
Qed.
  
Lemma eq_effect_trans': forall a a0 a1,
    eq_effect_label a0 a ->
    eq_effect_label a1 a ->
    eq_effect_label a0 a1.
Proof.
  intros. induction a.
  induction a0; induction a1; auto; try(inv H).
  induction a0; induction a1; auto; try(inv H1).
  induction a0; induction a1; auto; try(inv H).
  + apply Peqb_true_eq in H2. subst. auto.
    unfold eq_effect_label in *. rewrite Pos.eqb_sym. auto.
  induction a0; induction a1; auto; try(inv H).
  + apply Peqb_true_eq in H2. subst. auto.
    unfold eq_effect_label in *. rewrite Pos.eqb_sym. auto.
  induction a0; induction a1; auto; try(inv H).
  + apply Peqb_true_eq in H2. subst. auto.
    unfold eq_effect_label in *. rewrite Pos.eqb_sym. auto.
  induction a0; induction a1; auto; try(inv H).
Qed.

Lemma eq_effect_sym : forall a b,
    eq_effect_label a b ->
    eq_effect_label b a.
Proof.
  intros. induction a; induction b; auto.
  - unfold eq_effect_label in *. rewrite Pos.eqb_sym. auto.
  - unfold eq_effect_label in *. rewrite Pos.eqb_sym. auto.
  - unfold eq_effect_label in *. rewrite Pos.eqb_sym. auto.
Qed.

(* Complete Me: Easy *)
Lemma sub_effect_trans : forall ef1 ef2 ef3, 
sub_effect ef1 ef2 = true ->
sub_effect ef2 ef3 = true ->
sub_effect ef1 ef3 = true.
Proof.
  intro. induction ef1.
  - intros. apply sub_effect_nil.
  - intros. generalize dependent ef3. induction ef2.
    + intros. inv H.
    + intros. induction ef3.
      * inv H0.
      * simpl. destruct (eq_effect_label a a1) eqn:Eqaa1.
        -- simpl in H. simpl in H0. destruct (eq_effect_label a a0) eqn:Eqaa0.
           ++ assert (eq_effect_label a0 a1 = true).
              apply eq_effect_trans with (a := a); auto.
              rewrite H1 in H0. apply IHef1 with (ef2 := ef2); auto.
           ++ destruct (eq_effect_label a0 a1) eqn:Eqa01.
              ** assert (eq_effect_label a a0).
                 apply eq_effect_trans' with (a := a1). auto.
                 auto. congruence.
              ** apply IHef1 with (ef2 := ef2).
                 --- apply sub_effect_1s with (a := a) in H.
                     apply sub_effect_ss in H. auto.
                     apply sub_effect_1s with (a := a0) in H0.
                     apply sub_effect_ss in H0. auto.
                 --- have Hmid : sub_effect (a :: ef1) (a1 :: ef3) = true.
                     simpl. rewrite Eqaa1. 
                     apply IHef3.
                     apply sub_effect_1s with (a:= a) in H.
                     apply sub_effect_ss in H. apply IHef1 with (ef3 := a1 :: ef3) in H; auto.
                     destruct (eq_effect_label a0 a1) eqn:Eqa01.
                     simpl in H0. rewrite Eqa01 in H0.
                     admit.
                     simpl in H0. rewrite Eqa01 in H0. auto.
                     simpl in Hmid. rewrite Eqaa1 in Hmid. auto.
Admitted.                 




(* Complete Me: Easy *)
Lemma prefix_sub_effect : forall (ef1 ef2 : effect), 
sub_effect ef1 (ef1 ++ ef2)%list = true.
Proof.
induction ef1.
- apply sub_effect_nil.
- intros. simpl. rewrite eq_effect_refl.   apply IHef1.
Qed.
(* Complete Me: Easy *)

       
(* Complete Me: Easy *)
Lemma suffix_sub_effect : forall (ef1 ef2 : effect), 
sub_effect ef2 (ef1 ++ ef2)%list = true.
Proof.
  intros. revert ef1.
induction ef2; intros.
- apply sub_effect_nil.
- simpl. induction ef1.
  +  simpl. rewrite eq_effect_refl. apply sub_effect_refl.
  + simpl. destruct (eq_effect_label a a0).
    * assert ((ef1 ++ (a :: ef2)%SEQ)%list = (ef1 ++ [:: a]) ++ ef2).
      rewrite - catA. rewrite cat1s. auto.
      rewrite H. apply IHef2. apply IHef1.
Qed.

Lemma sub_effect_lem1 : forall efa efb,
    sub_effect efa efb ->
    sub_effect efa efa.
Proof.
  induction efa; auto.
  - intros. apply sub_effect_refl.
Qed.

(* Complete Me: Easy *)
Lemma sub_effect_concat : forall ef1 ef2 ef1' ef2',
sub_effect ef1 ef1' ->
sub_effect ef2 ef2' ->
sub_effect (ef1 ++ ef2) (ef1' ++ ef2').
Proof.
intro ef1. induction ef1.
-  intros. generalize dependent ef2. generalize dependent ef2'. induction ef1'.
  + auto. 
  + intros. rewrite sub_effect_nil in IHef1'.
    simpl. generalize dependent ef2'. induction ef2.
    * auto.
    * intros. destruct (eq_effect_label a0 a).
      -- simpl in IHef1'. apply IHef1'; auto.
         ++ apply sub_effect_1s with (a := a0) in H0.
         apply sub_effect_ss in H0. apply H0.
      -- apply sub_effect_1c. auto.
- intros. generalize dependent ef2. generalize dependent ef2'.
  induction ef1'.
  + intros. inv H.
  + intros. simpl in *. destruct (eq_effect_label a a0). 
    apply IHef1; auto. apply IHef1' with (ef2 := ef2) (ef2' := ef2') in H; auto.
Qed.

Lemma no_divergence_a : forall a ef,
    no_divergence (a :: ef) <->
    no_divergence ef /\ no_divergence [:: a].
Proof.
  split.
  - intros. simpl in H.
    destruct a; auto.
  - intros. destruct H. unfold no_divergence.
    unfold no_divergence in H0. destruct (eq_effect_label Divergence a); auto.
Qed.

Lemma no_divergence_fe : forall a ef,
    no_divergence (ef ++ [:: a]) <->
      no_divergence (a :: ef).
Proof.
split.
- intros. generalize dependent a.
  induction ef; auto.
  + intros.  destruct a0; try (simpl; simpl in H).
    * destruct a; try (apply IHef in H; auto); try auto.
    * destruct a; try (apply IHef in H; auto); try auto.
    * destruct a; try (apply IHef in H; auto); try auto.
    * destruct a; try (apply IHef in H; auto); try auto.
    * destruct a; try (apply IHef in H; auto); try auto.
    * destruct a; try (apply IHef in H; auto); try auto.
- intros. generalize dependent a.
  induction ef; auto.
  + intros. destruct a; try(simpl; apply IHef; simpl in H).
    * destruct a0; auto.
    * destruct a0; auto.
    * destruct a0; auto.
    * destruct a0; auto.
    * destruct a0; auto.
    * destruct a0; auto.
Qed.

(* Complete Me: Easy *)
Lemma no_divergence_concat : forall ef ef',
no_divergence ef ->
no_divergence ef' ->
no_divergence (ef ++ ef').
Proof.
  intros. generalize dependent ef. induction ef'; intros.
  - rewrite cats0. auto.
  - assert (ef ++ a :: ef' = (ef ++ [:: a]) ++ ef'). rewrite -catA. auto.
    rewrite H1. apply IHef'; auto; try (apply no_divergence_a in  H0;  destruct H0; auto).
    +  assert (no_divergence ef /\ no_divergence [:: a]). auto.
       apply no_divergence_a in H3. apply no_divergence_fe. assumption.
Qed.

Lemma unzip1_cancel {A} {B} : forall (l1 : list A) (l2 : list B),
  length l1 = length l2 ->
  l1 = BeePL_aux.unzip1 (BeePL_aux.zip l1 l2).
Proof.
  induction l1; intros.
  - destruct l2; auto.
  - simpl.
    destruct l2.
    + discriminate.
    + simpl. f_equal. auto.
Qed.

Lemma unzip2_cancel {A} {B} : forall (l1 : list A) (l2 : list B),
  length l1 = length l2 ->
  l1 = BeePL_aux.unzip2 (BeePL_aux.zip l2 l1).
Proof.
  induction l1; intros.
  - destruct l2; auto.
  - simpl.
    destruct l2.
    + discriminate.
    + simpl. f_equal. auto.
Qed.

Lemma unzip1_preserves_length {A} {B} {C} : forall (l1 : list (A * B)) (l2 : list C),
  length (BeePL_aux.unzip1 l1) = length l2 <->
  length l1 = length l2.
Proof.
  induction l1; intros; split; intros; auto.
  - simpl. 
    destruct l2.
    + discriminate.
    + simpl in *. f_equal. rewrite <- IHl1. auto.
  - simpl.
    destruct l2.
    + discriminate.
    + simpl in *. f_equal. rewrite IHl1. auto.
Qed.

Lemma unzip2_preserves_length {A} {B} {C} : forall (l1 : list (A * B)) (l2 : list C),
  length (BeePL_aux.unzip2 l1) = length l2 <->
  length l1 = length l2.
Proof.
  induction l1; intros; split; intros; auto.
  - simpl. 
    destruct l2.
    + discriminate.
    + simpl in *. f_equal. rewrite <- IHl1. auto.
  - simpl.
    destruct l2.
    + discriminate.
    + simpl in *. f_equal. rewrite IHl1. auto.
Qed.


Lemma ptr_eq_trans : forall p p0, 
eq_ptr_type p p0 -> 
transBeePL_ptr_type p0 = transBeePL_ptr_type p.
Proof.
move=> [].
+ move=> h b a [] //=.
  + move=> h' [] //=.
    + move=> [] //=.
      + move=> a' /=. case: b=> //=.
        + move=> [] //=.
          + by move=> i s a1 /andP [] /andP [] h1 //=.
          by move=> s a1 /andP [] /andP [] h1 //=.
        by move=> i a1 /andP [] /andP [] h1 //=.
      move=> [] //=.
      + by move=> z a1 /andP [] /andP [] h1 //=.
      + by move=> i s a1 z a2 /andP [] /andP [] h1 //=.
      by move=> s a1 z a2 /andP [] /andP [] h1 //=.
    case: b=> //=.
    + move=> [] //=.
      + by move=> i s a1 a2 /andP [] /andP [] h1 //=.
      + move=> sz s a1 sz' s' a2 a3 /andP. case: ifP=> //=.
        + case: ifP=> //=.
          + case: ifP=> //=.
            + move=> ha hs hsz [] hh ha'.
              destruct (attr_eq a1 a2) eqn:Heqa1; try discriminate; auto.
              destruct (attr_eq a a3) eqn:Heqa2; try discriminate; auto.
              destruct (Ctyping.signedness_eq s s') eqn:Heqs; try discriminate; auto.
              destruct (Ctyping.intsize_eq sz sz') eqn:Heqsz; try discriminate; auto.
              subst. auto.
            by move=> ha hs hsz [] /andP [] h1 //=.
          by move=> hs hsz [] /andP [] hh //=. 
        by move=> hsz [] /andP [] hh //=.
      by move=> s a1 i s' a2 a3 /andP [] /andP [] hh //=.
    by move=> h1 a1 i1 s a3 a4 /andP [] /andP [] hh //=.
  move=> [].
  + by move=> z a1 i s a2 a3 /andP [] /andP [] hh //=.
  + by move=> sz s a' z a1 i'' s' a2 a3 /andP [] /andP [] hh //=.
  + by move=> s a1 z a2 i s' a3 a4 /andP [] /andP [] hh //=.
  + case: b=> //=.
    + move=> [] //=.
      + by move=> s a1 a2 /andP [] /andP [] hh //=.
      by move=> sz s a1 s' a2 a3 /andP [] /andP [] hh //=.
    move=> s a1 s' a2 a3 /andP. case: ifP=> //=.
    + case: ifP=> //=.
      + move=> ha hs [] hh ha'.
        destruct (attr_eq a1 a2) eqn:Heqa1; try discriminate; auto.
        destruct (attr_eq a a3) eqn:Heqa2; try discriminate; auto.
        destruct (Ctyping.signedness_eq s s') eqn:Heqs; try discriminate; auto.
        subst. auto.
      by move=> ha hs [] /andP [] h1 //=.
    by move=> hs [] /andP [] hh //=. 
  by move=> h1 a1 s a3 a4 /andP [] /andP [] hh //=.
 + by move=> p z a1 s a2 a3 /andP [] /andP [] hh //=. 
 + case: b=> //=.
   + move=> [].
     + by move=> h1 a1 a2 /andP [] /andP [] hh //=.
     + by move=> sz a' a1 i1 a2 a3 /andP [] /andP [] hh //=.
     by move=> s a1 i a2 a3 /andP [] /andP [] hh //=.
   move=> i a1 i1 a2 a3 /andP [] /andP [] hh /andP [] h1 h2 h3.
   destruct (attr_eq a1 a2) eqn:Heqa1; try discriminate; auto.
   destruct (attr_eq a a3) eqn:Heqa2; try discriminate; auto.
   apply Pos.eqb_eq in hh. apply Pos.eqb_eq in h1. subst. auto.
 + move=> [] //=.
   + by move=> z a1 i a2 a3 /andP [] /andP [] hh //=.
   + by move=> sz a1 a1' z a2 a3 a4 a5 /andP [] /andP [] hh //=.
   by move=> s a1 z a2 i a3 a4 /andP [] /andP [] hh //=.
 + move=> [] //=.
   + case: b=> //=.
     + by move=> p z a1 a2 /andP [] /andP [] hh //=.
     + by move=> i a1 z a2 a3 /andP [] /andP [] hh //=.
     move=> [] //=.
     + move=> z a1 z2 a2 a3 /andP [] /andP [] hh /andP [] hz ha1 ha2.
       apply Pos.eqb_eq in hh. apply Z.eqb_eq in hz.
       destruct (attr_eq a1 a2) eqn:Heqa1; try discriminate; auto.
       destruct (attr_eq a a3) eqn:Heqa2; try discriminate; auto.
       subst. auto.
     + by move=> sz s a1 z a2 z' a3 a4 /andP [] /andP [] hh //=.
     by move=> s a1 z a2 z' a3 a4 /andP [] /andP [] hh //=.
   + case: b=> //=.
     + by move=> p i s a1 z a2 a3 /andP [] /andP [] hh //=.
     by move=> i a' i'' s a1 z a2 a3 /andP [] /andP [] hh //=.
   + move=> [] //=.
     + by move=> z a1 sz s a1' z' a2 a3 /andP [] /andP [] hh //=.
     move=> sz a1 a2 z a3 sz' a4 a5 z'' a6 a7. case: ifP=> //=.
     + case: ifP=> //=.
       + case: ifP=> //=.
         + move=> ha hs hsz /andP [] /andP [] hh /andP [] hz ha1 ha2.
           apply Pos.eqb_eq in hh. apply Z.eqb_eq in hz.
           destruct (attr_eq a2 a5) eqn:Heqa1; try discriminate; auto.
           destruct (attr_eq a3 a6) eqn:Heqa2; try discriminate; auto.
           destruct (attr_eq a a7) eqn:Heqa3; try discriminate; auto.
           destruct (Ctyping.signedness_eq a1 a4) eqn:Heqs; try discriminate; auto.
           destruct (Ctyping.intsize_eq sz sz') eqn:Heqsz; try discriminate; auto.
           subst. auto.
         by move=> ha hs hsz /andP [] /andP [] hh //=.
       by move=> hs hsz /andP [] /andP [] hh //=.
     by move=> hsz /andP [] /andP [] hh //=.
   by move=> s a1 z a2 i s' a3 z' a4 a5 /andP [] /andP [] hh //=.
  + case: b=> //=.
    + by move=> p s a1 z a2 a3 /andP [] /andP [] hh //=.
    + by move=> h1 a1 s a2 z a3 a4 /andP [] /andP [] hh //=.
    move=> [] //=.
    + by move=> z a1 s a2 z' a3 a4 /andP [] /andP [] hh //=.
    + by move=> sz a' a1 z a2 s' a3 z' a4 a5 /andP [] /andP [] hh //=.
  move=> s a1 z a2 s' a3 z1 a4 a5. case: ifP=> //=.
  + case: ifP=> /=.
    + move=> ha hs /andP [] /andP [] hh /andP [] hz ha1 ha2. 
      apply Pos.eqb_eq in hh. apply Z.eqb_eq in hz.
      destruct (attr_eq a2 a4) eqn:Heqa1; try discriminate; auto.
      destruct (attr_eq a a5) eqn:Heqa2; try discriminate; auto.
      destruct (attr_eq a1 a3) eqn:Heqa3; try discriminate; auto.
      destruct (Ctyping.signedness_eq s s') eqn:Heqs; try discriminate; auto.
      subst. auto.
    by move=> ha hs /andP [] /andP [] hh //=.
  by move=> hs /andP [] /andP [] hh //=.
+ move=> [] //=.
  + move=> h [] //=.
    + move=> p a [] //= p0. case: p0=> //=.
      move=> h' [] //=.
      + move=> [] //=.
        + case: p=> //=.
          + by move=> sz a' a1 a2 /andP [] /andP [] hh //=.
          by move=> s a1 a2 /andP [] /andP [] hh //=.
        case: p=> //=.
        + by move=> sz s a1 a2 /andP [] /andP [] hh //=.
        move=> sz a' a1 sz' s' a2 a3. case: ifP=> //=.
        + case: ifP=> //=.
          + case: ifP=> //=.
            + move=> ha hs hsz /andP [] /andP [] hh _ ha1.
              apply Pos.eqb_eq in hh. 
              destruct (attr_eq a1 a2) eqn:Heqa1; try discriminate; auto.
              destruct (attr_eq a a3) eqn:Heqa2; try discriminate; auto.
              destruct (Ctyping.signedness_eq a' s') eqn:Heqs; try discriminate; auto.
              destruct (Ctyping.intsize_eq sz sz') eqn:Heqsz; try discriminate; auto.
              subst. auto.
          by move=> ha1 hs1 hsz1 /andP [] /andP [] hh //=.
        by move=> hs hsz /andP [] /andP [] hh //=.
      by move=> hsz /andP [] /andP [] hh //=.
    by move=> s a1 i a' a2 a3 /andP [] /andP [] hh //=.
  + case: p=> //=.
    + by move=> s a1 a2 /andP [] /andP [] hh //=.
    + by move=> sz a'' a1 a' a2 a3 /andP [] /andP [] hh //=.
    + move=> s a1 a' a2 a3. case: ifP=> //=.
      + case: ifP=> //=.
        + intros. apply andb_prop in H. destruct H.
          apply andb_prop in H. destruct H.
          destruct (attr_eq a1 a2) eqn:Heqa1; try discriminate; auto.
          destruct (attr_eq a a3) eqn:Heqa2; try discriminate; auto.
          destruct (Ctyping.signedness_eq s a') eqn:Heqs; try discriminate; auto.
          subst. auto.
        by move=> ha hs /andP [] /andP [] hh //=.
      by move=> hs /andP [] /andP [] hh //=.
    + by move=> h1 a1 a2 /andP [] /andP [] hh //=.
    + by move=> p1 z a1 a2 /andP [] /andP [] hh //=.
    + move=> h1 a1 a2 [].
      + by move=> h2 b a //=.
      + move=> [] //= h3 [] //=. 
        + by move=> p a /andP [] /andP [] hh //=.
        + move=> h4 a3 a4 /andP [] /andP [] hh1 hh2 ha.
          apply andb_prop in hh2. destruct hh2.
          apply Pos.eqb_eq in H. 
          destruct (attr_eq a1 a3) eqn:Heqa1; try discriminate; auto.
          destruct (attr_eq a2 a4) eqn:Heqa2; try discriminate; auto.
          subst. auto.
        by move=> p z a3 a4 /andP [] /andP [] hh //=.
      by move=> es e t //=.
    + move=> p z a1 a2 p0. case: p0=> //=. move=> [] //=.
      move=> h1 [] //=.  
      + by move=> p' a /andP [] /andP [] hh //=.
      + by move=> h2 a3 a4 /andP [] /andP [] hh //=.
      case: p=> //=.
      + move=> [] //=.
        + intros. repeat (apply andb_prop in H as [? H]).
          apply andb_prop in H0. destruct H0. apply andb_prop in H1. destruct H1.
          destruct (attr_eq a1 a) eqn:Heqa1; try discriminate; auto.
          destruct (attr_eq a2 a0) eqn:Heqa2; try discriminate; auto.
          apply Z.eqb_eq in H1. subst. auto.
        + by move=> sz a a' z' a3 a4 /andP [] /andP [] hh //=.
        by move=> s a z1 a4 a5 /andP [] /andP [] hh //=.
      move=> sz s a [] //=.
      + by move=> z1 a4 a5 /andP [] /andP [] hh //=.
      + move=> sz1 s1 a3 z1 a4 a5. case: ifP=> //=.
        + case: ifP=> //=.
          + case: ifP=> //=.
            + intros. repeat (apply andb_prop in H as [? H]).
              apply andb_prop in H0. destruct H0. apply andb_prop in H1. destruct H1.
              destruct (attr_eq a1 a4) eqn:Heqa1; try discriminate; auto.
              destruct (attr_eq a2 a5) eqn:Heqa2; try discriminate; auto.
              destruct (attr_eq a a3) eqn:Heqa3; try discriminate; auto.
              apply Z.eqb_eq in H1.
              destruct (Ctyping.signedness_eq s s1) eqn:Heqs; try discriminate; auto.
              destruct (Ctyping.intsize_eq sz sz1) eqn:Heqsz; try discriminate; auto.
              subst. auto.
            by move=> ha1 hs1 hsz1 /andP [] /andP [] hh1 //=.
          by move=> hs hsz /andP  [] /andP [] hh1 //=.
        by move=> hsz /andP [] /andP [] hh //=.
      by move=> s1 a3 z1 a4 a5 /andP [] /andP [] hh //=.
Admitted.


Lemma ptr_t_eq_trans : forall t p,
eq_type t (Ptrtype p) ->
transBeePL_ptr_type p = transBeePL_type t.
Proof.
move=> [].
+ move=> [].
  + by move=> h b a //=.
  + by move=> [] h b //=.
  by move=> es e t //=.
+ by move=> [] //=.
+ move=> p1 p2 hp /=. by have hp' := ptr_eq_trans p1 p2 hp.
+ by move=> h a p //=.
+ by move=> t z a p /= //=.
+ by move=> es e t p /=.
by move=> p /=.     
Qed.


Lemma ptr_eq_trans : forall p p0, 
eq_ptr_type p p0 -> 
transBeePL_ptr_type p0 = transBeePL_ptr_type p.
Proof.
move=> [].
+ move=> h b a [] //=.
  + move=> h' [] //=.
    + move=> [] //=.
      + move=> a' /=. case: b=> //=.
        + move=> [] //=.
          + by move=> i s a1 /andP [] /andP [] h1 //=.
          by move=> s a1 /andP [] /andP [] h1 //=.
        by move=> i a1 /andP [] /andP [] h1 //=.
      move=> [] //=.
      + by move=> z a1 /andP [] /andP [] h1 //=.
      + by move=> i s a1 z a2 /andP [] /andP [] h1 //=.
      by move=> s a1 z a2 /andP [] /andP [] h1 //=.
    case: b=> //=.
    + move=> [] //=.
      + by move=> i s a1 a2 /andP [] /andP [] h1 //=.
      + move=> sz s a1 sz' s' a2 a3 /andP. case: ifP=> //=.
        + case: ifP=> //=.
          + case: ifP=> //=.
            + move=> ha hs hsz [] hh ha'. admit. (* provable *)
            by move=> ha hs hsz [] /andP [] h1 //=.
          by move=> hs hsz [] /andP [] hh //=. 
        by move=> hsz [] /andP [] hh //=.
      by move=> s a1 i s' a2 a3 /andP [] /andP [] hh //=.
    by move=> h1 a1 i1 s a3 a4 /andP [] /andP [] hh //=.
  move=> [].
  + by move=> z a1 i s a2 a3 /andP [] /andP [] hh //=.
  + by move=> sz s a' z a1 i'' s' a2 a3 /andP [] /andP [] hh //=.
  + by move=> s a1 z a2 i s' a3 a4 /andP [] /andP [] hh //=.
  + case: b=> //=.
    + move=> [] //=.
      + by move=> s a1 a2 /andP [] /andP [] hh //=.
      by move=> sz s a1 s' a2 a3 /andP [] /andP [] hh //=.
    move=> s a1 s' a2 a3 /andP. case: ifP=> //=.
    + case: ifP=> //=.
      + move=> ha hs [] hh ha'. admit. (* provable *)
      by move=> ha hs [] /andP [] h1 //=.
    by move=> hs [] /andP [] hh //=. 
  by move=> h1 a1 s a3 a4 /andP [] /andP [] hh //=.
 + by move=> p z a1 s a2 a3 /andP [] /andP [] hh //=. 
 + case: b=> //=.
   + move=> [].
     + by move=> h1 a1 a2 /andP [] /andP [] hh //=.
     + by move=> sz a' a1 i1 a2 a3 /andP [] /andP [] hh //=.
     by move=> s a1 i a2 a3 /andP [] /andP [] hh //=.
   move=> i a1 i1 a2 a3 /andP [] /andP [] hh /andP [] h1 h2 h3. admit. (* provable *)
 + move=> [] //=.
   + by move=> z a1 i a2 a3 /andP [] /andP [] hh //=.
   + by move=> sz a1 a1' z a2 a3 a4 a5 /andP [] /andP [] hh //=.
   by move=> s a1 z a2 i a3 a4 /andP [] /andP [] hh //=.
 + move=> [] //=.
   + case: b=> //=.
     + by move=> p z a1 a2 /andP [] /andP [] hh //=.
     + by move=> i a1 z a2 a3 /andP [] /andP [] hh //=.
     move=> [] //=.
     + move=> z a1 z2 a2 a3 /andP [] /andP [] hh /andP [] hz ha1 ha2. admit. (* provable *)
     + by move=> sz s a1 z a2 z' a3 a4 /andP [] /andP [] hh //=.
     by move=> s a1 z a2 z' a3 a4 /andP [] /andP [] hh //=.
   + case: b=> //=.
     + by move=> p i s a1 z a2 a3 /andP [] /andP [] hh //=.
     by move=> i a' i'' s a1 z a2 a3 /andP [] /andP [] hh //=.
   + move=> [] //=.
     + by move=> z a1 sz s a1' z' a2 a3 /andP [] /andP [] hh //=.
     move=> sz a1 a2 z a3 sz' a4 a5 z'' a6 a7. case: ifP=> //=.
     + case: ifP=> //=.
       + case: ifP=> //=.
         + move=> ha hs hsz /andP [] /andP [] hh /andP [] hz ha1 ha2. admit. (* provable *)
         by move=> ha hs hsz /andP [] /andP [] hh //=.
       by move=> hs hsz /andP [] /andP [] hh //=.
     by move=> hsz /andP [] /andP [] hh //=.
   by move=> s a1 z a2 i s' a3 z' a4 a5 /andP [] /andP [] hh //=.
  + case: b=> //=.
    + by move=> p s a1 z a2 a3 /andP [] /andP [] hh //=.
    + by move=> h1 a1 s a2 z a3 a4 /andP [] /andP [] hh //=.
    move=> [] //=.
    + by move=> z a1 s a2 z' a3 a4 /andP [] /andP [] hh //=.
    + by move=> sz a' a1 z a2 s' a3 z' a4 a5 /andP [] /andP [] hh //=.
  move=> s a1 z a2 s' a3 z1 a4 a5. case: ifP=> //=.
  + case: ifP=> /=.
    + move=> ha hs /andP [] /andP [] hh /andP [] hz ha1 ha2. admit. (* provable *)
    by move=> ha hs /andP [] /andP [] hh //=.
  by move=> hs /andP [] /andP [] hh //=.
+ move=> [] //=.
  + move=> h [] //=.
    + move=> p a [] //= p0. case: p0=> //=.
      move=> h' [] //=.
      + move=> [] //=.
        + case: p=> //=.
          + by move=> sz a' a1 a2 /andP [] /andP [] hh //=.
          by move=> s a1 a2 /andP [] /andP [] hh //=.
        case: p=> //=.
        + by move=> sz s a1 a2 /andP [] /andP [] hh //=.
        move=> sz a' a1 sz' s' a2 a3. case: ifP=> //=.
        + case: ifP=> //=.
          + case: ifP=> //=.
            + move=> ha hs hsz /andP [] /andP [] hh _ ha1. admit. (* provable *)
          by move=> ha1 hs1 hsz1 /andP [] /andP [] hh //=.
        by move=> hs hsz /andP [] /andP [] hh //=.
      by move=> hsz /andP [] /andP [] hh //=.
    by move=> s a1 i a' a2 a3 /andP [] /andP [] hh //=.
  + case: p=> //=.
    + by move=> s a1 a2 /andP [] /andP [] hh //=.
    + by move=> sz a'' a1 a' a2 a3 /andP [] /andP [] hh //=.
    + move=> s a1 a' a2 a3. case: ifP=> //=.
      + case: ifP=> //=.
        + admit. (* provable *)
        by move=> ha hs /andP [] /andP [] hh //=.
      by move=> hs /andP [] /andP [] hh //=.
    + by move=> h1 a1 a2 /andP [] /andP [] hh //=.
    + by move=> p1 z a1 a2 /andP [] /andP [] hh //=.
    + move=> h1 a1 a2 [].
      + by move=> h2 b a //=.
      + move=> [] //= h3 [] //=. 
        + by move=> p a /andP [] /andP [] hh //=.
        + move=> h4 a3 a4 /andP [] /andP [] hh1 hh2 ha. admit. (* provable *)
        by move=> p z a3 a4 /andP [] /andP [] hh //=.
      by move=> es e t //=.
    + move=> p z a1 a2 p0. case: p0=> //=. move=> [] //=.
      move=> h1 [] //=.  
      + by move=> p' a /andP [] /andP [] hh //=.
      + by move=> h2 a3 a4 /andP [] /andP [] hh //=.
      case: p=> //=.
      + move=> [] //=.
        + admit. (* provable *)
        + by move=> sz a a' z' a3 a4 /andP [] /andP [] hh //=.
        by move=> s a z1 a4 a5 /andP [] /andP [] hh //=.
      move=> sz s a [] //=.
      + by move=> z1 a4 a5 /andP [] /andP [] hh //=.
      + move=> sz1 s1 a3 z1 a4 a5. case: ifP=> //=.
        + case: ifP=> //=.
          + case: ifP=> //=.
            + admit. (* provable *)
            by move=> ha1 hs1 hsz1 /andP [] /andP [] hh1 //=.
          by move=> hs hsz /andP  [] /andP [] hh1 //=.
        by move=> hsz /andP [] /andP [] hh //=.
      by move=> s1 a3 z1 a4 a5 /andP [] /andP [] hh //=.
Admitted.


Lemma ptr_t_eq_trans : forall t p,
eq_type t (Ptrtype p) ->
transBeePL_ptr_type p = transBeePL_type t.
Proof.
move=> [].
+ move=> [].
  + by move=> h b a //=.
  + by move=> [] h b //=.
  by move=> es e t //=.
+ by move=> [] //=.
+ move=> p1 p2 hp /=. by have hp' := ptr_eq_trans p1 p2 hp.
+ by move=> h a p //=.
+ by move=> t z a p /= //=.
+ by move=> es e t p /=.
by move=> p /=.     
Qed.







