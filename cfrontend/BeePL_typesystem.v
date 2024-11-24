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
| Ty_constint : forall Gamma Sigma t sz s i,
                t = (Ptype (Tint sz s)) ->
                type_expr Gamma Sigma (Const (ConsInt i) t) empty_effect t
| Ty_constbool : forall Gamma Sigma t b,
                 t = (Ptype Tbool) ->
                 type_expr Gamma Sigma (Const (ConsBool b) t) empty_effect t
| Ty_constunit : forall Gamma Sigma t,
                t = (Ptype Tunit) ->
                type_expr Gamma Sigma (Const (ConsUnit) t) empty_effect t
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
| Ty_prim_bop : forall Gamma Sigma op e ef t tr e',
                type_expr Gamma Sigma e ef t ->
                type_expr Gamma Sigma e' ef t ->
                eq_type tr (if is_not_comparison op then t else (Ptype Tbool)) ->
                type_expr Gamma Sigma (Prim (Bop op) (e::e'::nil) tr) ef tr 
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
typeof_expr e = match e with 
                | Prim (Bop op) es t => (if (is_not_comparison op) then t else (Ptype Tbool)) 
                | _ => t
                end.
Proof.
move=> Gamma Sigma e ef t ht; inversion ht; subst; rewrite /typeof_expr /=; auto.
case: ifP=> //= ho. move: H1. rewrite ho /=. case: t ht=> //= p. by case: p=> //=.
Qed.

Lemma sem_unary_operation_val_type : forall op v t v', 
sem_unary_operation op v t = Some v' ->
typeof_value v t /\ typeof_value v' t.
Proof.
move=> [].
+ move=> v t v' hs.
  have ht := extract_type_notbool v t v' hs; subst. split.
  + by case: v hs=> //=.
  case: v' hs=> //=.
  + move=> hs. rewrite /sem_notbool in hs. by case: v hs=> //=.
  + move=> i hs. rewrite /sem_notbool in hs. by case: v hs=> //=.
  move=> i hs. rewrite /sem_notbool in hs. by case: v hs=> //=.
+ move=> v t v' hs.
  have [sz [s ht]]:= extract_type_notint v t v' hs; subst. split.
  + case: v hs=> //=. case: v' hs=> //=.
    + rewrite /sem_notint /=. by case: v=> //=.
    rewrite /sem_notint /=. by case: v=> //=.
  rewrite /sem_notint /=. by case: v=> //=.
move=> v t v' hs. have [sz [s ht]] := extract_type_neg v t v' hs; subst. split.
+ by case: v hs=> //=.
case: v' hs=> //=.
+ rewrite /sem_neg /=. by case: v=> //=.
+ rewrite /sem_neg /=. by case: v=> //=.
rewrite /sem_neg /=. by case: v=> //=.
Qed.

Lemma sem_binary_operation_val_type : forall op v1 v2 t v, 
sem_binary_operation op v1 v2 t t = Some v ->
typeof_value v (if (is_not_comparison op) then t else (Ptype Tbool)).
Proof.
move=> [];rewrite /sem_binary_operation.
+ move=> v1 v2 t v hs. move: hs. rewrite /sem_plus. 
  case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] s s' i i' [] hv; subst.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v hs. move: hs. rewrite /sem_plus. 
  case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] s s' i i' [] hv; subst.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v hs. move: hs. rewrite /sem_plus. 
  case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] s s' i i' [] hv; subst.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v hs. move: hs. rewrite /sem_plus. 
  case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t=> //= p. case: p=> //= i s i1 i2. 
    case: s=> //=. 
    + case: i=> //=. by case: ifP=> //= he [] hv; subst.
    case: i=> //=. by case: ifP=> //= he [] hv; subst.
  + case: v2=> //=. case: t=> //= p. case: p=> //=.
    case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. case: v1=> //=.  
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
    case: v2=> //=. case: t=> //= p. by case: p=> //=.
  case: v2=> //=. case: t=> //= p. by case:p=> //= b b' [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. case: v1=> //=.  
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
    case: v2=> //=. case: t=> //= p. by case: p=> //=.
  case: v2=> //=. case: t=> //= p. by case:p=> //= b b' [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. case: v1=> //=.  
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
    case: v2=> //=. case: t=> //= p. by case: p=> //=.
  case: v2=> //=. case: t=> //= p. by case:p=> //= b b' [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. case: v1=> //=.  
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
    case: v2=> //=. case: t=> //= p. case: p=> //= sz s. case: sz=> //= i i'.
    by case: ifP=> //= hl [] hv; subst.
  case: v2=> //=. case: t=> //= p. by case:p=> //= b b' [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. case: v1=> //=.  
  + case: v2=> //=. case: t=> //= p. by case: p=> //=.
    case: v2=> //=. case: t=> //= p. case: p=> //= sz s. case: s=> //= i i'.
    case: sz=> //=. by case: ifP=> //= hl [] hv; subst.
    case: sz=> //=. by case: ifP=> //= hl [] hv; subst.
  case: v2=> //=. case: t=> //= p. by case:p=> //= b b' [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. rewrite /is_not_comparison /=. case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  + case: v2=> //= i i'. case: t=> //= p. case: p=> //= sz s. case: s=> //=.
    + by case: sz=> //= [] [] hv; subst.
    + by case: sz=> //= [] [] hv; subst.
    case: v2=> //= b b'. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. rewrite /is_not_comparison /=. case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  + case: v2=> //= i i'. case: t=> //= p. case: p=> //= sz s. case: s=> //=.
    + by case: sz=> //= [] [] hv; subst.
    + by case: sz=> //= [] [] hv; subst.
    case: v2=> //= b b'. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. rewrite /is_not_comparison /=. case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  + case: v2=> //= i i'. case: t=> //= p. case: p=> //= sz s. case: s=> //=.
    + by case: sz=> //= [] [] hv; subst.
    + by case: sz=> //= [] [] hv; subst.
    case: v2=> //= b b'. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. rewrite /is_not_comparison /=. case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  + case: v2=> //= i i'. case: t=> //= p. case: p=> //= sz s. case: s=> //=.
    + by case: sz=> //= [] [] hv; subst.
    + by case: sz=> //= [] [] hv; subst.
    case: v2=> //= b b'. case: t=> //= p. case: p=> //= [] [] hv; subst.
    move: hv. by case: ifP=> //= hb [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
+ move=> v1 v2 t v. rewrite /is_not_comparison /=. case: v1=> //=.
  + case: v2=> //=. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  + case: v2=> //= i i'. case: t=> //= p. case: p=> //= sz s. case: s=> //=.
    + by case: sz=> //= [] [] hv; subst.
    + by case: sz=> //= [] [] hv; subst.
    case: v2=> //= b b'. case: t=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
move=> v1 v2 t v. rewrite /is_not_comparison /=. case: v1=> //=.
+ case: v2=> //=. case: t=> //= p. by case: p=> //= [] [] hv; subst.
+ case: v2=> //= i i'. case: t=> //= p. case: p=> //= sz s. case: s=> //=.
  + by case: sz=> //= [] [] hv; subst.
  + by case: sz=> //= [] [] hv; subst.
  case: v2=> //= b b'. case: t=> //= p. case: p=> //= [] [] hv; subst.
  move: hv. by case: ifP=> //= hb [] hv; subst.
case: v2=> //=. case: t=> //= i b. case: b=> //= p. by case: p=> //=.
Qed.

Lemma sem_binary_operation_val_type1 : forall op v1 v2 t1 t2 v, 
sem_binary_operation op v1 v2 t1 t2 = Some v ->
typeof_value v (if (is_not_comparison op) then t1 else (Ptype Tbool)).
Proof.
move=> [];rewrite /sem_binary_operation.
+ move=> v1 v2 t1 t2 v /=. case: v1=> //=.
  + case: v2=> //=. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t1=> //= p i1 i2. case: p=> //= sz s.
    case: t2=> //= p. by case: p=> //= sz' s' [] hv; subst.
  + case: v2=> //=. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. case: p=> //=.
  case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
  case: p=> //= sz s. case: t2=> //= i' b'. case: b'=> //= p.
  by case: p=> //=.
+ move=> v1 v2 t1 t2 v /=. case: v1=> //=.
  + case: v2=> //=. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t1=> //= p i1 i2. case: p=> //= sz s.
    case: t2=> //= p. by case: p=> //= sz' s' [] hv; subst.
  + case: v2=> //=. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. case: p=> //=.
  + case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
    case: p=> //= sz s. case: t2=> //= i' b'. case: b'=> //= p.
    by case: p=> //=.
+ move=> v1 v2 t1 t2 v /=. case: v1=> //=.
  + case: v2=> //=. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t1=> //= p i1 i2. case: p=> //= sz s.
    case: t2=> //= p. by case: p=> //= sz' s' [] hv; subst.
  + case: v2=> //=. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. case: p=> //=.
  + case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
    case: p=> //= sz s. case: t2=> //= i' b'. case: b'=> //= p.
    by case: p=> //=.
+ move=> v1 v2 t1 t2 v /=. case: v1=> //=.
  + case: v2=> //=. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t1=> //= p i1 i2. case: p=> //= sz s.
    case: t2=> //= p. case: p=> //= sz' s'. case: s=> //=.
    + case: s'=> //=. case: sz=> //=. case: sz'=> //=. 
      by case: ifP=> //= ht [] hv; subst.
    case: s'=> //=. case: sz=> //=. case: sz'=> //=.
    by case: ifP=> //= hl [] hv; subst.
  + case: v2=> //=. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. case: p=> //=.
  + case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
    case: p=> //= sz s. case: t2=> //= i' b'. case: b'=> //= p.
    by case: p=> //=.
+ move=> v1 v2 t1 t2 v. case: v1=> //=.
  + case: v2=> //=. case: t1=> //= p.
    case: p=> //=. case: t2=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t1=> //= p. case: p=> //= sz s.
    case: t2=> //= p. by case: p=> //=. 
  + case: v2=> //= b b'. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
  case: p=> //= sz s. case: t2=> //= i' b'. case: b'=> //= p.
  by case: p=> //=.
+ move=> v1 v2 t1 t2 v. case: v1=> //=.
  + case: v2=> //=. case: t1=> //= p.
    case: p=> //=. case: t2=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t1=> //= p. case: p=> //= sz s.
    case: t2=> //= p. by case: p=> //=. 
  + case: v2=> //= b b'. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
  case: p=> //= sz s. case: t2=> //= i' b'. case: b'=> //= p.
  by case: p=> //=.
+ move=> v1 v2 t1 t2 v. case: v1=> //=.
  + case: v2=> //=. case: t1=> //= p.
    case: p=> //=. case: t2=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t1=> //= p. case: p=> //= sz s.
    case: t2=> //= p. by case: p=> //=. 
  + case: v2=> //= b b'. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
  case: p=> //= sz s. case: t2=> //= i' b'. case: b'=> //= p.
  by case: p=> //=.
+ move=> v1 v2 t1 t2 v. case: v1=> //=.
  + case: v2=> //=. case: t1=> //= p.
    case: p=> //=. case: t2=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t1=> //= p. case: p=> //= sz s.
    case: t2=> //= p.  case: p=> //= sz' s' i1 i2.
    case: sz=> //=. case: sz'=> //=. by case: ifP=> //= hl [] hv; subst.  
  + case: v2=> //= b b'. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
  case: p=> //= sz s. case: t2=> //= i' b'. case: b'=> //= p.
  by case: p=> //=.
+ move=> v1 v2 t1 t2 v. case: v1=> //=.
  + case: v2=> //=. case: t1=> //= p.
    case: p=> //=. case: t2=> //= p. by case: p=> //=.
  + case: v2=> //=. case: t1=> //= p. case: p=> //= sz s.
    case: t2=> //= p.  case: p=> //= sz' s' i1 i2.
    case: s=> //=.
    + case: s'=> //=. case: sz=> //=. case: sz'=> //=.
      case: ifP=> //= hl [] hv; subst.
   (* case: sz=> //=. case: sz'=> //= by case: ifP=> //= hl [] hv; subst.  
  + case: v2=> //= b b'. case: t1=> //= p. case: p=> //=.
    case: t2=> //= p. by case: p=> //= [] [] hv; subst.
  case: v2=> //=. case: t1=> //= i b. case: b=> //= p.
  case: p=> //= sz s. case: t2=> //= i' b'. case: b'=> //= p.
  by case: p=> //=.*)
Admitted.

Lemma type_reflex : forall v t t' v',
typeof_value v t ->
typeof_value v t' ->
typeof_value v' t ->
typeof_value v' t'.
Proof.
move=> v t t' v'. rewrite /typeof_value /=.
case: v=> //=.
+ case: t=> //= p. case: p=> //=.
  case: t'=> //= p'. by case: p'=> //=.
+ case: t=> //= p. case: p=> //=.
  case: t'=> //= p. by case: p=> //=.
+ case: t=> //= p. case: p=> //=.
  case: t'=> //= p. by case: p=> //=.
case: t=> //= i b. case: b=> //= p.
case: p=> //=. case: t'=> //= i' b. 
case: b=> //= p. by case: p=> //=.
Qed.

Lemma eq_type_rel : forall v t t',
eq_type t t' ->
typeof_value v t' ->
typeof_value v t.
Proof.
move=> v t t'. case: t'=> //=.
+ case: t=> //= p p'. case: p=> //=.
  + by case: p'=> //=.
  + by case: p'=> //=.
  by case: p'=> //=.
+ case: t=> //= i b i' b'. move=> /andP [] hi.
  case: b=> //= p. case: b'=> //= p'. case: p=> //=.
  + by case: p'=> //=.
  + by case: p'=> //=.
  case: p'=> //=.
move=> es e t'. by case: t=> //=.
Qed.
  
(**** Preservation ****)
Lemma preservation : forall Gamma Sigma genv e ef t st st' v, 
type_expr Gamma Sigma e ef t ->
sem_expr genv st e st' v ->
typeof_value v t.
Proof.
move=> Gamma Sigma genv e ef t st st' v ht he. move: st st' v he.
induction ht.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
(* Ref *)
+ admit.
(* Deref *)
+ admit.
(* Massgn *)
+ admit.
(* Uop *)
+ move=> st st' v he. inversion he; subst.
  have [h1 h2] := sem_unary_operation_val_type op v0 (typeof_expr e) v H7.
  move: (IHht st st' v0 H6)=> hv0t.
  have := type_rel_typeof Gamma Sigma e ef t ht. case: e ht IHht he H6 H7 h1 h2=> //=.
  + by move=> v1 ht IHht he H6 H7 h1 h2 <-.
  + by move=> c t0 ht IHht he H6 H7 h1 h2 <-.
  + by move=> o e es t0 ht IHht he H6 H7 h1 h2 <-.
  move=> b es t0 ht IHht he H6 H7 h1 h2. case: b ht IHht he H6=> //=.
  + by move=> ht IHht he H6 <-.
  + by move=> ht IHht he H6 <-.
  + by move=> ht IHht he H6 <-.
  + by move=> uop ht IHht he H6 <-.
  + move=> b ht IHht he H6 heq; subst. rewrite heq /= in h2.
    move: h2. case: ifP=> //= hc hv. + by have := type_reflex v0 t0 t v h1 hv0t hv. 
    rewrite hc in heq; subst. by have := type_reflex v0 (Ptype Tbool) t v h1 hv0t hv.
  + by move=> h ht IHht he H6 <-.
  + by move=> i t0 e e' t1 ht IHht he H6 ho h1 h2 <-.
  + by move=> e e1 e2 t' ht IHht he H6 ho h1 h2 <-.
  + by move=> l ht IHht he H6 ho h1 h2 <-.
  by move=> h e t' ht IHht he H6 ho h1 h2 <-.
(* Bop *)
+ move=> st st' v he; inversion he; subst.
  move: (IHht1 st st' v1 H8)=> hvt1.
  move: (IHht2 st' st'' v2 H9)=> hvt2.
  move: H. case: ifP=> //= hc.
  + have ht :=  sem_binary_operation_val_type1 op v1 v2 (typeof_expr e) (typeof_expr e') v H10.
    move=> heq. have htv1' := eq_type_rel v1 tr t heq hvt1. rewrite hc in ht.
    have hte := type_rel_typeof Gamma Sigma e ef t ht1.
    case: e ht1 IHht1 he H8 H10 ht hte=> //=.
    + move=> vi ht1 IHht1 he H8 H10 ht hte; subst. 
      by have := eq_type_rel v tr (vtype vi) heq ht. 
    + move=> c t' ht1 IHht1 he H8 H10 ht hte; subst.
      by have := eq_type_rel v tr t heq ht. 
    + move=> i e es t' ht1 IHht1 he H8 H10 ht hte; subst.
      by have := eq_type_rel v tr t heq ht. 
    + move=> [] //=.
      + move=> es t' ht1 IHht1 he H8 H10 ht hte; subst. 
        by have := eq_type_rel v tr t heq ht. 
      + move=> es t' ht1 IHht1 he H8 H10 ht hte; subst.
        by have := eq_type_rel v tr t heq ht. 
      + move=> es t' ht1 IHht1 he H8 H10 ht hte; subst.
        by have := eq_type_rel v tr t heq ht. 
      + move=> uop es t' ht1 IHht1 he H8 H10 ht hte; subst.
        by have := eq_type_rel v tr t heq ht. 
      + move=> bop es t' ht1 IHht1 he H8 H10 ht hte; subst. 
Admitted.
 


   

    
    
