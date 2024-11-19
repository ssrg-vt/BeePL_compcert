Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL.
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
                type_expr Gamma Sigma (Prim Ref (e::nil) (Ptype bt)) (ef ++ (Alloc h :: nil)) (Reftype h (Bprim bt))
| Ty_prim_deref : forall Gamma Sigma e ef h bt, 
                  type_expr Gamma Sigma e ef (Reftype h (Bprim bt)) -> 
                  type_expr Gamma Sigma (Prim Deref (e::nil) (Reftype h (Bprim bt))) (ef ++ (Read h :: nil)) (Ptype bt)
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
           get_sty Sigma l.(lname) = Some bt ->
           type_expr Gamma Sigma (Addr l) empty_effect (Reftype h bt) 
with type_exprs : ty_context -> store_context -> list expr -> effect -> list type -> Prop :=
| Ty_nil : forall Gamma Sigma,
           type_exprs Gamma Sigma nil nil nil
| Ty_cons : forall Gamma Sigma e es ef efs t ts,
            type_expr Gamma Sigma e ef t ->
            type_exprs Gamma Sigma es efs ts ->
            type_exprs Gamma Sigma (e :: es) (ef ++ efs) (t :: ts).
           

(**** Supoorting lemmas ****)
Lemma get_ty_write_var : forall Gamma vm r v vm' t,
write_var vm r v = vm' ->
typeof_value v t ->
get_ty Gamma r.(vname) = Some t.
Proof.
Admitted.

Lemma write_var_preserve_ty : forall Gamma Sigma vm r rv vm' t,
write_var vm r rv = vm' ->
typeof_value rv t ->
type_expr Gamma Sigma (Var r) empty_effect t.
Proof.
Admitted.

(**** Preservation ****)
Lemma preservation : forall Gamma Sigma genv e ef t st st' v, 
type_expr Gamma Sigma e ef t ->
sem_expr genv st e st' v ->
typeof_value v t.
Proof.
move=> Gamma Sigma genv e ef t st st' v ht he. move: st st' ef t ht he. elim: e=> //=.
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
+ move=> o e ih es ts st st' ef t ht he; inversion he; subst.
  inversion ht; subst. admit.
Admitted.
  
