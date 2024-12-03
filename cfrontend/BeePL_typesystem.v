Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Coqlib Memory Ctypes Memtype.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL BeePL_auxlemmas.
From mathcomp Require Import all_ssreflect. 

Definition empty_effect : effect := nil. 

Inductive type_expr : ty_context -> store_context -> expr -> effect -> type -> Prop :=
| Ty_var : forall Gamma Sigma x t, 
           PTree.get x.(vname) (extend_context Gamma x.(vname) t) = Some t ->
           x.(vtype) = t ->
           type_expr Gamma Sigma (Var x) empty_effect t
| Ty_constint : forall Gamma Sigma t sz s a i,
                t = (Tint sz s a) ->
                type_expr Gamma Sigma (Const (ConsInt i) t) empty_effect t
| Ty_constlong : forall Gamma Sigma t s a i,
                 t = (Tlong s a) ->
                 type_expr Gamma Sigma (Const (ConsLong i) t) empty_effect t
| Ty_constunit : forall Gamma Sigma t,
                t = Tunit ->
                type_expr Gamma Sigma (Const (ConsUnit) t) empty_effect t
| Ty_appr : forall Gamma Sigma r e es h bt rt ef efs ts a, 
            PTree.get r.(vname) Gamma = Some rt ->
            type_expr Gamma Sigma (Var r) empty_effect rt -> 
            type_expr Gamma Sigma e ef (Reftype h bt a) -> 
            bt = Ftype ts ef rt -> 
            type_exprs Gamma Sigma es efs ts -> 
            type_expr Gamma Sigma (App (Some r.(vname)) e es rt) (ef ++ efs) rt
| Ty_app : forall Gamma Sigma e es h bt rt ef ts a, 
           type_expr Gamma Sigma e ef (Reftype h bt a) -> 
           type_exprs Gamma Sigma es ef ts -> 
           type_expr Gamma Sigma (App None e es rt) ef rt
| Ty_prim_ref : forall Gamma Sigma e ef h bt a, 
                type_expr Gamma Sigma e ef bt ->
                type_expr Gamma Sigma (Prim Ref (e::nil) (Reftype h bt a)) (ef ++ (Alloc h :: nil)) (Reftype h bt a)
| Ty_prim_deref : forall Gamma Sigma e ef h bt a, (* inner expression should be unrestricted as it will be used later *)
                  type_expr Gamma Sigma e ef (Reftype h bt a) -> 
                  type_expr Gamma Sigma (Prim Deref (e::nil) bt) (ef ++ (Read h :: nil)) bt
| Ty_prim_massgn : forall Gamma Sigma e e' h bt ef a, (* fix me *)
                   type_expr Gamma Sigma e ef (Reftype h bt a) ->
                   type_expr Gamma Sigma e' ef bt ->
                   type_expr Gamma Sigma (Prim Massgn (e::e'::nil) (Reftype h bt a)) (ef ++ (Alloc h :: nil)) (Reftype h bt a)
| Ty_prim_uop : forall Gamma Sigma op e ef t,
                type_expr Gamma Sigma e ef t ->
                type_expr Gamma Sigma (Prim (Uop op) (e::nil) t) ef t 
| Ty_prim_bop : forall Gamma Sigma op e ef t tr e',
                type_expr Gamma Sigma e ef t ->
                type_expr Gamma Sigma e' ef t ->
                type_expr Gamma Sigma (Prim (Bop op) (e::e'::nil) tr) ef tr 
| Ty_bind : forall Gamma Sigma x t e e' t' ef,
            type_expr Gamma Sigma e ef t ->
            type_expr (extend_context Gamma x t) Sigma e' ef t' ->
            type_expr Gamma Sigma (Bind x t e e' t') ef t'
| Ty_cond : forall Gamma Sigma e1 e2 e3 tb t ef, (* add that tb represents bool *)
            type_expr Gamma Sigma e1 ef tb ->
            type_expr Gamma Sigma e2 ef t ->
            type_expr Gamma Sigma e3 ef t ->
            type_expr Gamma Sigma (Cond e1 e2 e3 t) ef t
| Ty_loc : forall Gamma Sigma l h bt a,
           PTree.get l.(lname) Sigma = Some (Reftype h bt a)  ->
           l.(ltype) = (Reftype h bt a) ->
           type_expr Gamma Sigma (Addr l) empty_effect (Reftype h bt a) 
with type_exprs : ty_context -> store_context -> list expr -> effect -> list type -> Prop :=
| Ty_nil : forall Gamma Sigma,
           type_exprs Gamma Sigma nil nil nil
| Ty_cons : forall Gamma Sigma e es ef efs t ts,
            type_expr Gamma Sigma e ef t ->
            type_exprs Gamma Sigma es efs ts ->
            type_exprs Gamma Sigma (e :: es) (ef ++ efs) (t :: ts).
           
Scheme type_expr_ind_mut := Induction for type_expr Sort Prop
  with type_exprs_ind_mut := Induction for type_exprs Sort Prop.
Combined Scheme type_exprs_type_expr_ind_mut from type_exprs_ind_mut, type_expr_ind_mut.

Lemma type_exprsE : forall Gamma Sigma es efs ts,
type_exprs Gamma Sigma es efs ts ->
match es with 
| [::] => efs = [::] /\ ts = [::]
| e1 :: es1 => exists ef1 t1 efs1 ts1,
               type_expr Gamma Sigma e1 ef1 t1 /\  
               type_exprs Gamma Sigma es1 efs1 ts1 /\
               es = e1 :: es1 /\ efs = ef1 ++ efs1 /\ ts = t1 :: ts1
end.
Proof.
move=> Gamma Sigma es efs ts hs. elim: es hs=> //=.
+ by move=> hs; inversion hs.
move=> e es ih hs; inversion hs; subst.
by exists ef, t, efs0, ts0; split=> //=.
Qed.      

Section type_expr_ind.
Context (Pts : ty_context -> store_context -> list expr -> effect -> list type -> Prop).
Context (Pt : ty_context -> store_context -> expr -> effect -> type -> Prop).
Context (Htvar : forall Gamma Sigma x t,
                 PTree.get x.(vname) (extend_context Gamma x.(vname) t) = Some t ->
                 x.(vtype) = t ->
                 Pt Gamma Sigma (Var x) empty_effect t).
Context (Htconti : forall Gamma Sigma t sz s i a,
                   t = (Tint sz s a) ->
                   Pt Gamma Sigma (Const (ConsInt i) t) empty_effect t).
Context (Htcontl : forall Gamma Sigma t s i a,
                   t = (Tlong s a) ->
                   Pt Gamma Sigma (Const (ConsLong i) t) empty_effect t).
Context (Htcontu : forall Gamma Sigma t,
                   t = Tunit ->
                   Pt Gamma Sigma (Const (ConsUnit) t) empty_effect t).
Context (Htappr : forall Gamma Sigma r e es h bt a rt ef efs ts, 
                  PTree.get r.(vname) Gamma = Some rt ->
                  Pt Gamma Sigma (Var r) empty_effect rt ->
                  Pt Gamma Sigma e ef (Reftype h bt a) ->
                  Pts Gamma Sigma es efs ts ->
                  bt = Ftype ts ef rt -> 
                  Pt Gamma Sigma (App (Some r.(vname)) e es rt) (ef ++ efs) rt).
Context (Htapp : forall Gamma Sigma e es ef h bt a rt ts,
                 Pt Gamma Sigma e ef (Reftype h bt a) ->
                 Pts Gamma Sigma es ef ts ->
                 Pt Gamma Sigma (App None e es rt) ef rt).      
Context (Htref : forall Gamma Sigma e ef h bt a, 
                 Pt Gamma Sigma e ef bt -> 
                 Pt Gamma Sigma (Prim Ref (e::nil) (Reftype h bt a)) (ef ++ (Alloc h :: nil)) (Reftype h bt a)).
Context (Htderef : forall Gamma Sigma e ef h bt a, 
                   Pt Gamma Sigma e ef (Reftype h bt a) ->
                   Pt Gamma Sigma (Prim Deref (e::nil) bt) (ef ++ (Read h :: nil)) bt).
Context (Htmassgn : forall Gamma Sigma e1 e2 ef h bt a, 
                    Pt Gamma Sigma e1 ef (Reftype h bt a) ->
                    Pt Gamma Sigma e2 ef bt ->
                    Pt Gamma Sigma (Prim Massgn (e1::e2::nil) (Reftype h bt a)) (ef ++ (Alloc h :: nil)) (Reftype h bt a)).
Context (Htop : forall Gamma Sigma op e ef t, 
                Pt Gamma Sigma e ef t ->
                Pt Gamma Sigma (Prim (Uop op) (e :: nil) t) ef t).
Context (Htbop : forall Gamma Sigma op e1 e2 ef t tr, 
                 Pt Gamma Sigma e1 ef t ->
                 Pt Gamma Sigma e2 ef t ->
                 Pt Gamma Sigma (Prim (Bop op) (e1 :: e2 :: nil) tr) ef tr).
Context (Htbind : forall Gamma Sigma x t e e' t' ef, 
                  Pt Gamma Sigma e ef t ->
                  Pt (extend_context Gamma x t) Sigma e' ef t' ->
                  Pt Gamma Sigma (Bind x t e e' t') ef t').
Context (Htcond : forall Gamma Sigma e1 e2 e3 ef tb t, 
                  Pt Gamma Sigma e1 ef tb -> 
                  Pt Gamma Sigma e2 ef t -> 
                  Pt Gamma Sigma e3 ef t -> 
                  Pt Gamma Sigma (Cond e1 e2 e3 t) ef t).
Context (Htloc : forall Gamma Sigma l h bt a, 
                 PTree.get l.(lname) Sigma  = Some (Reftype h bt a) ->
                 l.(ltype) = (Reftype h bt a) ->
                 Pt Gamma Sigma (Addr l) empty_effect (Reftype h bt a)). 
Context (Htnil : forall Gamma Sigma,
                 Pts Gamma Sigma nil nil nil).
Context (Htcons : forall Gamma Sigma e es t ef ts efs,
                  Pt Gamma Sigma e ef t ->
                  Pts Gamma Sigma es efs ts ->
                  Pts Gamma Sigma (e :: es) (ef ++ efs) (t :: ts)).

Lemma type_expr_indP : 
(forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts -> Pts Gamma Sigma es efs ts) /\
(forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t -> Pt Gamma Sigma e ef t).
Proof.
apply type_exprs_type_expr_ind_mut=> //=.
(* ConsInt *)
+ move=> Gamma Sigma t sz s a i. by apply Htconti.
(* ConsLong *)
+ move=> Gamma Sigma t s a i ht; subst. by apply Htcontl with s a.
(* Appr *)
+ move=> Gamma Sigma r e es h bt et e' efs ts a hg ht hi ht' hi' hf hes hts.
  by apply Htappr with h bt a ts.
(* App *)
+ move=> Gamma Sigma e es h bt rt ef ts a hte ht htes hts.
  by apply Htapp with h bt a ts.
(* Ref *)
+ move=> Gamma Sigma e ef h bt hte ht.
  by apply Htref.
(* Deref *)
+ move=> Gamma Sigma e ef h bt hte ht.
  by apply Htderef.
(* Massgn *)
+ move=> Gamma Sigma e e' h bt a ef hte ht hte' ht'.
  by apply Htmassgn. 
(* Mop *)
+ move=> Gamma Sigma op e ef t hte ht.
  by apply Htop.
(* Mbop *)
+ move=> Gamma Sigma bop e ef tr e' hte ht hte' ht' heq.
  by apply Htbop with tr.
(* Bind *)
+ move=> Gamma Sigma h t e e' t' ef hte ht hte' ht'.
  by apply Htbind.
(* Cond *)
+ move=> Gamma Sigma e1 e2 e3 tb t ef hte1 ht1 hte2 ht2 hte3 ht3.
  by apply Htcond with tb.
move=> Gamma Sigma e es ef efs t ts hte ht htes hts.
by apply Htcons.
Qed.

End type_expr_ind.

Lemma type_expr_exprs_deterministic: 
(forall Gamma Sigma es efs ts efs' ts', type_exprs Gamma Sigma es efs ts ->
                                        type_exprs Gamma Sigma es efs' ts' ->
                                        ts = ts' /\ efs = efs') /\
(forall Gamma Sigma e ef t ef' t', type_expr Gamma Sigma e ef t ->
                                   type_expr Gamma Sigma e ef' t' ->
                                   t = t' /\ ef = ef').
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall efs' ts', type_exprs Gamma Sigma es efs' ts' ->
                                      ts = ts' /\ efs = efs') /\
       (forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                                   forall ef' t', type_expr Gamma Sigma e ef' t' ->
                                   t = t' /\ ef = ef').
+ move=> [] ih ih'. split=> //=.
  + move=> Gamma Sigma es efs ts efs' ts' hes hes'. 
    by move: (ih Gamma Sigma es efs ts hes efs' ts' hes').
  move=> Gamma Sigma e ef t ef' t' he he'.
  by move: (ih' Gamma Sigma e ef t he ef' t' he').
apply type_expr_indP => //=.
+ move=> Gamma Sigma x t htx ht ef' t' het; subst. by inversion het; subst.
+ move=> Gamma Sigma t sz s i a ht ef' t' ht'; subst. by inversion ht'; subst.
+ move=> Gamma Sigma t s i a ht ef' t' ht'; subst. by inversion ht'; subst.
+ move=> Gamma Sigma t ht ef' t' ht'; subst. by inversion ht'; subst.
+ move=> Gamma Sigma r e es h bt a rt ef efs ts hrt ih ih' ih'' hbt ef' t' ht; subst.
  inversion ht; subst. move: (ih' ef0 (Reftype h0 (Ftype ts0 ef0 t') a0) H9)=> 
  [] [] h1 h2 h3 h5 h6; subst. by move: (ih'' efs0 ts0 H11)=> [] h1 h2; subst.
+ move=> Gamma Sigma e es ef h bt a rt ts ih ih' ef' t' ht; inversion ht; subst.
  by move: (ih' ef' ts0 H7)=> [] h1 h2; subst.
+ move=> Gamma Sigma e ef h bt a ih ef' t' ht; inversion ht; subst.
  by move: (ih ef0 bt H7)=> [] h1 h2; subst.
+ move=> Gamma Sigma e ef h bt a ih ef' t' ht; inversion ht; subst.
  by move: (ih ef0 (Reftype h0 t' a0) H5)=> [] [] h1 h2 h3; subst.
+ move=> Gamma Sigma e1 e2 ef h bt a ih ih' ef' t' ht; inversion ht; subst.
  by move: (ih' ef0 bt H9)=> [] h1 h2; subst.
+ move=> Gamma Sigma op e ef t ih ef' t' ht; inversion ht; subst.
  by move: (ih ef' t' H6)=> [] h1 h2; subst.
+ move=> Gamma Sigma op e1 e2 ef t tr ih ih' ef' t' ht; inversion ht; subst.
  by move: (ih ef' t0 H7)=> [] h1 h2; subst.
+ move=> Gamma Sigma x t e e' t' ef ih ih' ef' t'' ht; inversion ht; subst.
  by move: (ih' ef' t'' H9)=> [] h1 h2; subst.
+ move=> Gamma Sigma e1 e2 e3 ef tb t ih1 ih2 ih3 ef' t' ht; inversion ht; subst.
  by move: (ih3 ef' t' H9)=> [] h1 h2; subst.
+ move=> Gamma Sigma l h bt a hl heq ef' t' ht; inversion ht; subst.
  by rewrite heq in H3.
+ by move=> Gamma Sigma efs' ts' ht; inversion ht; subst.
move=> Gamma Sigma e es t ef ts efs ih ih' efs' ts' ht; inversion ht; subst.
move: (ih ef0 t0 H3)=> [] h1 h2; subst. by move: (ih' efs0 ts0 H6)=> [] h1 h2; subst.
Qed.

(**** Supoorting lemmas ****)
Lemma type_rel_typeof : forall Gamma Sigma e ef t,
type_expr Gamma Sigma e ef t ->
typeof_expr e = t.
Proof.
by move=> Gamma Sigma e ef t ht; inversion ht; subst; rewrite /typeof_expr /=; auto.
Qed.

Lemma type_reflex : forall v t t' v',
typeof_value v t ->
typeof_value v t' ->
typeof_value v' t ->
typeof_value v' t'.
Proof.
move=> v t t' v'. rewrite /typeof_value /=.
case: v=> //=.
+ by case: t=> //=; case: t'=> //=.
+ by case: t=> //=; case: t'=> //=.
+ by case: t=> //=; case: t'=> //=.
by case: t=> //=; case: t'=> //=.
Qed.

Lemma eq_type_rel : forall v t t',
eq_type t t' ->
typeof_value v t' ->
typeof_value v t.
Proof.
move=> v t t'. by case: t'=> //=;case: t=> //= p p'. 
Qed.

(**** Substitution preserves typing ****)
(* Substitution preserve typing says that suppose we
   have an expression [e] with a free variable [x], and suppose we've been
   able to assign a type [t'] to [e] under the assumption that [x] has
   some type [t].  Also, suppose that we have some other term [e'] and
   that we've shown that [e'] has type [t].  Then, since [e'] satisfies
   the assumption we made about [x] when typing [e], we should be
   able to substitute [e'] for each of the occurrences of [x] in [e]
   and obtain a new expression that still has type [t]. *)
Lemma subst_preservation : forall Gamma Sigma x t e' e ef t', 
type_expr (extend_context Gamma x.(vname) t) Sigma e ef t' ->
type_expr Gamma Sigma e' ef t ->
type_expr Gamma Sigma (subst x.(vname) e' e) ef t'.
Proof.
Admitted.

Lemma extend_ty_context_deterministic : forall Gamma Sigma x x' t1 t2 e ef t,
(x =? x')%positive = false ->
type_expr (extend_context (extend_context Gamma x t1) x' t2) Sigma e ef t ->
type_expr (extend_context Gamma x t1) Sigma e ef t. 
Proof.
Admitted.

Lemma subst_typing : forall Gamma Sigma genv vm hm hm' x e e' ef t v,
type_expr Gamma Sigma (subst x e e') ef t ->
sem_expr genv vm hm (subst x e e') hm' v ->
typeof_value v t.
Proof.
Admitted.

Lemma deref_addr_val_ty : forall ty m addr ofs v,
deref_addr ty m addr ofs Full v ->
typeof_value v ty.
Proof.
move=> ty m addr ofs v hd; inversion hd; subst.
(* by value *)
+ rewrite /transBeePL_value_cvalue /= /Mem.loadv in H0.
  have hvt := Mem.load_type m chunk addr (Ptrofs.unsigned ofs) v0 H0.
  case: chunk H H0 hvt=> //=.
  + case: ty hd=> //=. move=> sz s a. case: sz=> //=.
    + by case: s=> //=.
    + by case: s=> //=.
    by case: v H1=> //=;case: v0=> //=.
  + case: ty hd=> //=. move=> sz s a. case: sz=> //=.
    + case: s=> //=. by case: v H1=> //=;case: v0=> //=.
    + by case: s=> //=.
    case: v0 H1 hd=> //= i. move=> [] hv; subst. by case: ty=> //=.
  + case: ty hd=> //=. move=> sz s a. case: sz=> //=.
    + by case: s=> //=. 
    by case: v H1=> //=;case: v0=> //=. 
  + case: ty hd=> //=. move=> sz s a. case: sz=> //=.
    + by case: s=> //=. 
    by case: v H1=> //=;case: v0=> //=. 
  + case: ty hd=> //=. move=> sz s a. case: sz=> //=.
    + by case: s=> //=. 
    + by case: v H1=> //=;case: v0=> //=. 
    by case: v H1=> //=;case: v0=> //=. 
  + case: ty hd=> //=. move=> sz s a. case: sz=> //=.
    + by case: s=> //=. 
    + by case: s=> //=. 
    + move=> s a. case: s=> //=.
      + case: v0 H1=> //= i.  
        by move=> [] hv; subst. 
      by move=> ptr [] hv; subst. 
    + by case: v H1=> //=; case: v0=> //=.
    by case: v H1=> //=; case: v0=> //=.
  + by case: v0 H1=> //=.
  + by case: v0 H1=> //=.
  + case: v0 H1=> //= i. move=> [] hv; subst.
    by case: ty hd=> //=.
  case: ty hd=> //= sz s a; case: sz=> //=.
  + by case: s=> //=.
  by case: s=> //=.
case: ty hd H=> //= sz s a. case: sz=> //=.
+ by case: s=> //=.  
by case: s=> //=.    
Qed.    

(**** Preservation ****)
Lemma preservation : forall Gamma Sigma genv vm hm hm' e ef t v, 
type_expr Gamma Sigma e ef t ->
sem_expr genv vm hm e hm' v ->
typeof_value v t.
Proof.
move=> Gamma Sigma genv vm hm hm' e ef t v ht. move: Gamma Sigma ef t ht. 
elim: e=> //=.
(* var *)
+ move=> x Gamma Sigma ef t ht he; inversion he; subst.
  inversion ht; subst. by have := deref_addr_val_ty (vtype x) hm l Ptrofs.zero v H5.
(*move=> Gamma Sigma genv e ef t st st' v ht he. move: st st' v he.
induction ht.
+ move=> st st' v he; inversion he; subst.
  by have := get_val_var_ty st' x v H4.
(* Const int *)
+ by move=> st st' v he; inversion he; subst; rewrite /typeof_value.
(* Const bool *)
+ by move=> st st' v he; inversion he; subst; rewrite /typeof_value.
(* Const unit *)
+ by move=> st st' v he; inversion he; subst; rewrite /typeof_value.
(* App with return *) 
+ admit.
(* App with no return *)
+ admit.
(* Ref *)
+ move=> st st' v he; inversion he; subst. by rewrite /typeof_value /=.
(* Deref *)
+ move=> st st' v he; inversion he; subst.
  by move: (IHht st st' (Vloc l) H1)=> hvt.
(* Massgn *)
+ move=> st st' v he; inversion he; subst. by rewrite /typeof_value.
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
    have hvt := sem_binary_notcmp_type_val1 Gamma Sigma op v1 v2 e e' v ef t H10 ht1 hc. 
    by have := eq_type_rel v tr t heq hvt.
  move=> heq. have hvt := sem_binary_cmp_type_val Gamma Sigma op v1 v2 e e' v ef t H10 ht1 hc. 
  by have := eq_type_rel v tr (Ptype Tbool) heq hvt.
(* Bind *)
+ move=> st st' v he. have /= hs := subst_preservation Gamma Sigma {| vname := x; vtype := t |} t e e' ef t' ht2 ht1.
  inversion he; subst. by have := subst_typing Gamma Sigma genv x e e' ef t' st'0 st' v hs H9.
(* Cond *)
+ move=> st st' v he; inversion he; subst.
  + by move: (IHht2 st'0 st' v H8).
  by move: (IHht3 st'0 st' v H8).
(* Addr *)
move=> st st' v he; inversion he; subst.
rewrite /typeof_value /=. by case: bt H H0=> //= p.*)
Admitted.

    
    
