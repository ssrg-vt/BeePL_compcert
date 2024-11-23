Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL BeePL_auxlemmas.
From mathcomp Require Import all_ssreflect. 

Definition empty_effect : effect := nil. 

Inductive type_expr : ty_context -> store_context -> expr -> effect -> type -> Prop :=
| Ty_var : forall Gamma Sigma x t, 
           get_ty Gamma x.(vname) = Some t ->
           x.(vtype) = t ->
           type_expr Gamma Sigma (Var x) empty_effect t
| Ty_const : forall Gamma Sigma c t,
             type_expr Gamma Sigma (Const c t) empty_effect t
| Ty_appr : forall Gamma Sigma r e es h bt rt ef efs ts, 
            get_ty Gamma r.(vname) = Some rt ->
            type_expr Gamma Sigma (Var r) empty_effect rt -> 
            type_expr Gamma Sigma e ef (Reftype h bt) -> 
            type_exprs Gamma Sigma es efs ts -> 
            type_expr Gamma Sigma (App (Some r.(vname)) e es rt) (ef ++ efs) rt
| Ty_app : forall Gamma Sigma e es h bt rt ef ts, 
           type_expr Gamma Sigma e ef (Reftype h bt) -> 
           type_exprs Gamma Sigma es ef ts -> 
           type_expr Gamma Sigma (App None e es rt) ef rt
| Ty_prim_ref : forall Gamma Sigma e ef h bt, 
                type_expr Gamma Sigma e ef (Ptype bt) ->
                type_expr Gamma Sigma (Prim Ref (e::nil) (Reftype h (Bprim bt))) (ef ++ (Alloc h :: nil)) (Reftype h (Bprim bt))
| Ty_prim_deref : forall Gamma Sigma e ef h bt, 
                  type_expr Gamma Sigma e ef (Reftype h (Bprim bt)) -> 
                  type_expr Gamma Sigma (Prim Deref (e::nil) (Ptype bt)) (ef ++ (Read h :: nil)) (Ptype bt)
| Ty_prim_massgn : forall Gamma Sigma e e' h bt ef ef',
                   type_expr Gamma Sigma e ef (Reftype h (Bprim bt)) ->
                   type_expr Gamma Sigma e' ef' (Ptype bt) ->
                   type_expr Gamma Sigma (Prim Massgn (e::e'::nil) (Ptype Tunit)) (ef ++ ef' ++ (Alloc h :: nil)) (Ptype Tunit)
| Ty_prim_uop : forall Gamma Sigma op e ef t,
                type_expr Gamma Sigma e ef t ->
                type_expr Gamma Sigma (Prim (Uop op) (e::nil) t) ef t 
| Ty_prim_bop : forall Gamma Sigma op e ef t e',
                type_expr Gamma Sigma e ef t ->
                type_expr Gamma Sigma e' ef t ->
                type_expr Gamma Sigma (Prim (Bop op) (e::e'::nil) t) ef t 
| Ty_bind : forall Gamma Sigma x t e e' t' ef,
            type_expr Gamma Sigma e' ef t' ->
            type_expr (extend_context Gamma x t) Sigma e ef t ->
            type_expr Gamma Sigma (Bind x t e e' t') ef t'
| Ty_cond : forall Gamma Sigma e1 e2 e3 t ef ef',
            type_expr Gamma Sigma e1 ef (Ptype Tbool) ->
            type_expr Gamma Sigma e2 ef' t ->
            type_expr Gamma Sigma e3 ef' t ->
            type_expr Gamma Sigma (Cond e1 e2 e3 t) (ef ++ ef') t
| Ty_loc : forall Gamma Sigma l h bt,
           get_sty Sigma l.(lname) = Some (Reftype h bt)  ->
           l.(ltype) = (Reftype h bt) ->
           type_expr Gamma Sigma (Addr l) empty_effect (Reftype h bt) 
with type_exprs : ty_context -> store_context -> list expr -> effect -> list type -> Prop :=
| Ty_nil : forall Gamma Sigma,
           type_exprs Gamma Sigma nil nil nil
| Ty_cons : forall Gamma Sigma e es ef efs t ts,
            type_expr Gamma Sigma e ef t ->
            type_exprs Gamma Sigma es efs ts ->
            type_exprs Gamma Sigma (e :: es) (ef ++ efs) (t :: ts).
           

(**** Supoorting lemmas ****)
Lemma type_rel_typeof : forall Gamma Sigma e ef t,
type_expr Gamma Sigma e ef t ->
typeof_expr e = t.
Proof.
move=> Gamma Sigma e ef t ht; inversion ht; subst; rewrite /typeof_expr /=; auto.
Qed.

Lemma sem_unary_operation_val_type : forall op v t v', 
sem_unary_operation op v t = Some v' ->
typeof_value v t /\ typeof_value v' t.
Proof.
(*move=> [].
+ move=> v t v' hs.
  have ht := extract_type_notbool v t v' hs; subst. split.
  + by case: v hs=> //=.
  case: v' hs=> //=.
  + move=> hs. rewrite /sem_notbool in hs. by case: v hs=> //=.
  + move=> i hs. rewrite /sem_notbool in hs. by case: v hs=> //=.
  + move=> i hs. rewrite /sem_notbool in hs. by case: v hs=> //=.
  move=> p hs. rewrite /sem_notbool in hs. by case: v hs=> //=.
+ move=> v t v' hs.
  have ht := extract_type_notint v t v' hs; subst. case: ht=> //= ht; subst. 
  + split. 
    + by case: v hs=> //=.
    case: v' hs=> //=.
    + rewrite /sem_notint /=. by case: v=>//=.
    + rewrite /sem_notint /=. by case: v=> //=.
    + rewrite /sem_notint /=. by case: v=> //=.
    by rewrite /sem_notint /=;case: v=> //=.
  split=> //=.  
  + by case: v hs=> //=.
  case: v' hs=> //=.
  + rewrite /sem_notint /=. by case: v=>//=.
  + rewrite /sem_notint /=. case: v=> //= i i'.
    rewrite /of_int /=. move=> [] //=. case: i=> //=. case: i'=> //=.
    + rewrite /sem_notint /=. by case: v=> //=.
    by rewrite /sem_notint /=;case: v=> //=.

  case: 
  by case: v hs=> //=.
move=> v t v' hs.
have ht := extract_type_neg v t v' hs; subst. case: ht=> //= ht; subst. 
+ by case: v hs=> //=.
by case: v hs=> //=.
Qed.*) Admitted.

(**** Preservation ****)
Lemma preservation : forall Gamma Sigma genv e ef t st st' v, 
type_expr Gamma Sigma e ef t ->
sem_expr genv st e st' v ->
typeof_value v t.
Proof.
(*move=> Gamma Sigma genv e ef t st st' v ht he. move: st st' ef t ht he. elim: e=> //=.
(* Var *)
+ admit.
(* Const *)
+ move=> c t' st st' ef t /= ht /= he; inversion he; subst.
  (* Int *)
  + rewrite /typeof_value /=. case: t ht=> //= p.
    + case: p=> //=.
      + by move=> ht; inversion ht.
      + by move=> ht; inversion ht.
      + by move=> ht; inversion ht.
    by move=> b ht; inversion ht.
  by move=> e t ht;inversion ht.
  (* Bool *)   
  + rewrite /typeof_value /=. case: t ht=> //= p.
    + case: p=> //=.
      + by move=> ht; inversion ht.
      + by move=> ht; inversion ht.
      + by move=> ht; inversion ht.
    by move=> b' ht;inversion ht.
  by move=> e t ht;inversion ht.
  (* Unit *)
  + rewrite /typeof_value /=. case: t ht=> //= p.
    + case: p=> //=.
      + by move=> ht; inversion ht.
      + by move=> ht; inversion ht.
      + by move=> ht; inversion ht.
    by move=> b' ht;inversion ht.
  by move=> e t ht;inversion ht.
(* App *)
+ admit.
(* Prim *)
+ move=> [].
  (* Ref *)
  + by move=> es t st st' ef t' ht he;inversion he.
  (* Deref *)
  + admit.
  (* Massgn *)
  + admit.
  (* Uop *)
  + move=> u es t st st' ef t' ht he; inversion ht; subst; inversion he; subst.
    have hte := type_rel_typeof Gamma Sigma e ef t' H6. rewrite hte in H8. 
    have := sem_unary_operation_val_type u v0 t' v H8.
    
  *) Admitted.
