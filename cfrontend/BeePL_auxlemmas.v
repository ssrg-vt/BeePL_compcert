Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy Coqlib Errors.

From mathcomp Require Import all_ssreflect. 

Print access_mode.
Print access_mode_type.
(* BeePL
type :=
Inductive ptr_type : Set :=
    Reftype : ident -> basic_type -> attr -> ptr_type
  | Vptype : primitive_type -> ptr_type
  | Otype : ptr_type -> ptr_type
  | Fptype : list type -> effect -> type -> ptr_type
  | Sptype : ident -> attr -> ptr_type
  | Aptype : type -> Z -> attr -> ptr_type
  with type : Set :=
***    Utype : type
***  | Vtype : primitive_type -> type
***  | Ptrtype : ptr_type -> type
  | Stype : ident -> attr -> type
  | Atype : type -> Z -> attr -> type
  | Ftype : list type -> effect -> type -> type
  | Bytes : type.

Only thing that is Reference is
Ctypes
Tarray Tfunction
 *)
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
Print access_mode_type.
Print access_mode_prim. Print Ctypes.access_mode.

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
- induction md; simpl; intros.
  induction p; auto; injection H; intros; subst; auto.
  destruct b; auto. destruct p; auto.
  destruct p; auto.
  destruct p; auto. inv H. inv H. inv H.
- simpl. intros. subst. auto.
- simpl. intros. subst. auto.
- simpl. intros. subst. auto.
- simpl. intros. subst. simpl. auto.
Qed.
 (*
induction ty.
- induction md; simpl; intros.
  + inv H.
  + inv H.
  + inv H.
  + subst. auto.
- induction md; simpl; intros.
  + destruct p.
    * simpl in *. injection H. intros.
      subst. auto.
    * destruct i;  destruct s; destruct a; destruct m; simpl in *;  try auto; try inv H;
      try auto; try simpl.
-  admit.  admit.*) 
(* Looks like this is unresolvable without
 well-formedness theorem on chunk_of_type*)

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
Proof. 
intros. induction H. induction H0.
auto.
Qed.

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

(*** Auxillary lemmas related to types and effects ***)
(* Complete Me: Easy *)
Lemma sub_effect_refl : forall ef, 
sub_effect ef ef = true.
Proof.
induction ef; auto.
simpl. rewrite eq_effect_refl. auto.
Qed.

(*
Lemma value_cannot_be_reduced : forall bge benv e m e' m',
is_value e -> 
~ (rreduction bge benv e m e' m') /\
~ (lreduction bge benv e m e' m').
Proof.
move=> bge benv e. elim: e=> //= v t m e' m' _ /=. split=> //=.
+ move=> h. by inversion h.
move=> h. by inversion h.
Qed.
*)

(* 
Lemma addr_cannot_be_reduced : forall bge benv e m e' m',
is_addr e -> 
~ (rreduction bge benv e m e' m') /\
~ (lreduction bge benv e m e' m').
Proof.
Admitted.
*)

(* Complete Me: Easy *)
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
- intros. simpl.
  destruct a; simpl; try apply IHef1;
  try (rewrite Pos.eqb_refl; apply IHef1).
Qed.

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

