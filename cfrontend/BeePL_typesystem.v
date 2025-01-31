Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Coqlib Memory Ctypes Memtype.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL.
From mathcomp Require Import all_ssreflect. 

Definition empty_effect : effect := nil. 

Definition type_bool (t : type) : Prop :=
classify_bool t <> bool_default. 

Inductive type_expr : ty_context -> store_context -> expr -> effect -> type -> Prop :=
| Ty_val_unit : forall Gamma Sigma,
                type_expr Gamma Sigma (Val Vunit (Ptype Tunit)) empty_effect (Ptype Tunit)
| Ty_val_int : forall Gamma Sigma i sz s a,
               type_expr Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) empty_effect (Ptype (Tint sz s a))
| Ty_val_long : forall Gamma Sigma i s a,
               type_expr Gamma Sigma (Val (Vint64 i) (Ptype (Tlong s a))) empty_effect (Ptype (Tlong s a))
| Ty_val_loc : forall Gamma Sigma h t l ofs a,
               type_expr Gamma Sigma (Val (Vloc l ofs) (Reftype h (Bprim t) a)) empty_effect (Reftype h (Bprim t) a) 
| Ty_valof : forall Gamma Sigma e t,
             type_expr Gamma Sigma e empty_effect t  ->
             type_expr Gamma Sigma (Valof e t) empty_effect t
| Ty_var : forall Gamma Sigma x t, 
           PTree.get x.(vname) (extend_context Gamma x.(vname) t) = Some t ->
           x.(vtype) = t ->
           type_expr Gamma Sigma (Var x) empty_effect t
| Ty_constint : forall Gamma Sigma t sz s a i,
                t = (Ptype (Tint sz s a)) ->
                type_expr Gamma Sigma (Const (ConsInt i) t) empty_effect t
| Ty_constlong : forall Gamma Sigma t s a i,
                 t = (Ptype (Tlong s a)) ->
                 type_expr Gamma Sigma (Const (ConsLong i) t) empty_effect t
| Ty_constunit : forall Gamma Sigma t,
                 t = (Ptype Tunit) ->
                 type_expr Gamma Sigma (Const (ConsUnit) t) empty_effect t
(* Fix me *)
| Ty_app : forall Gamma Sigma e es rt efs ts ef efs', 
           type_expr Gamma Sigma e ef (Ftype ts efs rt) -> 
           type_exprs Gamma Sigma es efs' ts -> 
           type_expr Gamma Sigma (App e es rt) (ef ++ efs ++ efs') rt
| Ty_prim_ref : forall Gamma Sigma e ef h bt a, 
                type_expr Gamma Sigma e ef (Ptype bt) ->
                type_expr Gamma Sigma (Prim Ref (e::nil) (Reftype h (Bprim bt) a)) (ef ++ (Alloc h :: nil)) (Reftype h (Bprim bt) a) 
| Ty_prim_deref : forall Gamma Sigma e ef h bt a, (* inner expression should be unrestricted as it will be used later *)
                  type_expr Gamma Sigma e ef (Reftype h (Bprim bt) a) -> 
                  type_expr Gamma Sigma (Prim Deref (e::nil) (Ptype bt)) (ef ++ (Read h :: nil)) (Ptype bt)
| Ty_prim_massgn : forall Gamma Sigma e e' h bt ef a ef', 
                   type_expr Gamma Sigma e ef (Reftype h (Bprim bt) a) ->
                   type_expr Gamma Sigma e' ef' (Ptype bt) ->
                   type_expr Gamma Sigma (Prim Massgn (e::e'::nil) (Ptype Tunit)) (ef ++ ef' ++ (Write h :: nil)) (Ptype Tunit)
| Ty_prim_uop : forall Gamma Sigma op e ef t,
                type_expr Gamma Sigma e ef t ->
                type_expr Gamma Sigma (Prim (Uop op) (e::nil) t) ef t 
| Ty_prim_bop : forall Gamma Sigma op e ef t tr e',
                type_expr Gamma Sigma e ef t ->
                type_expr Gamma Sigma e' ef t ->
                type_expr Gamma Sigma (Prim (Bop op) (e::e'::nil) tr) ef tr 
| Ty_bind : forall Gamma Sigma x t e e' t' ef ef',
            type_expr Gamma Sigma e ef t ->
            type_expr (extend_context Gamma x t) Sigma e' ef' t' ->
            type_expr Gamma Sigma (Bind x t e e' t') (ef ++ ef') t'
| Ty_cond : forall Gamma Sigma e1 e2 e3 tb t ef1 ef2 ef3, 
            type_expr Gamma Sigma e1 ef1 tb ->
            type_bool tb ->
            type_expr Gamma Sigma e2 ef2 t ->
            type_expr Gamma Sigma e3 ef3 t ->
            type_expr Gamma Sigma (Cond e1 e2 e3 t) (ef1 ++ ef2 ++ ef3) t
| Ty_unit : forall Gamma Sigma,
            type_expr Gamma Sigma (Unit (Ptype Tunit)) empty_effect (Ptype Tunit)
| Ty_addr : forall Gamma Sigma l ofs h t a,
            l.(ltype) = Reftype h (Bprim t) a ->
            type_expr Gamma Sigma (Addr l ofs) empty_effect l.(ltype) 
(* fix me : Run, Hexpr *)
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

Section type_expr_ind.
Context (Pts : ty_context -> store_context -> list expr -> effect -> list type -> Prop).
Context (Pt : ty_context -> store_context -> expr -> effect -> type -> Prop).
Context (Htvalu : forall Gamma Sigma,
                  Pt Gamma Sigma (Val Vunit (Ptype Tunit)) empty_effect (Ptype Tunit)).
Context (Htvali Ty_val_int : forall Gamma Sigma i sz s a,
                             Pt Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) empty_effect (Ptype (Tint sz s a))).
Context (Htvall : forall Gamma Sigma i s a,
                  Pt Gamma Sigma (Val (Vint64 i) (Ptype (Tlong s a))) empty_effect (Ptype (Tlong s a))).
Context (Htvalloc : forall Gamma Sigma h t l ofs a,
                    Pt Gamma Sigma (Val (Vloc l ofs) (Reftype h (Bprim t) a)) empty_effect (Reftype h (Bprim t) a)). 
Context (Htvalof : forall Gamma Sigma e t,
                   Pt Gamma Sigma e empty_effect t  ->
                   Pt Gamma Sigma (Valof e t) empty_effect t).
Context (Htvar : forall Gamma Sigma x t,
                 PTree.get x.(vname) (extend_context Gamma x.(vname) t) = Some t ->
                 x.(vtype) = t ->
                 Pt Gamma Sigma (Var x) empty_effect t).
Context (Htconti : forall Gamma Sigma t sz s i a,
                   t = (Ptype (Tint sz s a)) ->
                   Pt Gamma Sigma (Const (ConsInt i) t) empty_effect t).
Context (Htcontl : forall Gamma Sigma t s i a,
                   t = (Ptype (Tlong s a)) ->
                   Pt Gamma Sigma (Const (ConsLong i) t) empty_effect t).
Context (Htcontu : forall Gamma Sigma t,
                   t = (Ptype Tunit) ->
                   Pt Gamma Sigma (Const (ConsUnit) t) empty_effect t).
Context (Htapp : forall Gamma Sigma e es rt ef efs ts efs', 
                  Pt Gamma Sigma e ef (Ftype ts efs rt) ->
                  Pts Gamma Sigma es efs' ts ->
                  Pt Gamma Sigma (App e es rt) (ef ++ efs ++ efs') rt).   
Context (Htref : forall Gamma Sigma e ef h bt a, 
                 Pt Gamma Sigma e ef (Ptype bt) ->
                 Pt Gamma Sigma (Prim Ref (e::nil) (Reftype h (Bprim bt) a)) (ef ++ (Alloc h :: nil)) (Reftype h (Bprim bt) a)).
Context (Htderef : forall Gamma Sigma e ef h bt a, 
                   Pt Gamma Sigma e ef (Reftype h (Bprim bt) a) ->
                   Pt Gamma Sigma (Prim Deref (e::nil) (Ptype bt)) (ef ++ (Read h :: nil)) (Ptype bt)).
Context (Htmassgn : forall Gamma Sigma e1 e2 ef1 ef2 h bt a, 
                    Pt Gamma Sigma e1 ef1 (Reftype h (Bprim bt) a) ->
                    Pt Gamma Sigma e2 ef2 (Ptype bt) ->
                    Pt Gamma Sigma (Prim Massgn (e1::e2::nil) (Ptype Tunit)) (ef1 ++ ef2 ++ (Write h :: nil)) (Ptype Tunit)).
Context (Htop : forall Gamma Sigma op e ef t, 
                Pt Gamma Sigma e ef t ->
                Pt Gamma Sigma (Prim (Uop op) (e :: nil) t) ef t).
Context (Htbop : forall Gamma Sigma op e1 e2 ef t tr, 
                 Pt Gamma Sigma e1 ef t ->
                 Pt Gamma Sigma e2 ef t ->
                 Pt Gamma Sigma (Prim (Bop op) (e1 :: e2 :: nil) tr) ef tr).
Context (Htbind : forall Gamma Sigma x t e e' t' ef ef', 
                  Pt Gamma Sigma e ef t ->
                  Pt (extend_context Gamma x t) Sigma e' ef' t' ->
                  Pt Gamma Sigma (Bind x t e e' t') (ef ++ ef') t').
Context (Htcond : forall Gamma Sigma e1 e2 e3 ef1 ef2 ef3 tb t, 
                  Pt Gamma Sigma e1 ef1 tb -> 
                  type_bool tb ->
                  Pt Gamma Sigma e2 ef2 t -> 
                  Pt Gamma Sigma e3 ef3 t -> 
                  Pt Gamma Sigma (Cond e1 e2 e3 t) (ef1 ++ ef2 ++ ef3) t).
Context (Htunit : forall Gamma Sigma, 
                  Pt Gamma Sigma (Unit (Ptype Tunit)) empty_effect (Ptype Tunit)).
Context (Htloc : forall Gamma Sigma l h bt a ofs, 
                 l.(ltype) = (Reftype h bt a) ->
                 Pt Gamma Sigma (Addr l ofs) empty_effect l.(ltype)). 
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
(* Valof *)
+ move=> Gamma Sigma e t hte h. by apply Htvalof. 
(* ConsInt *)
+ move=> Gamma Sigma t sz s a i. by apply Htconti.
(* ConsLong *)
+ move=> Gamma Sigma t s a i ht; subst. by apply Htcontl with s a.
(* App *)
+ move=> Gamma Sigma e es rt efs ts ef efs' ht hi ht' hi'.  
  by apply Htapp with ts.
(* Ref *)
+ move=> Gamma Sigma e ef h bt hte ht hp.
  by apply Htref.
(* Deref *)
+ move=> Gamma Sigma e ef h bt hte ht.
  by apply Htderef.
(* Massgn *)
+ move=> Gamma Sigma e e' h bt ef a ef' hte ht hte' ht'.
  by apply Htmassgn with bt a. 
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
+ move=> Gamma Sigma e1 e2 e3 tb t ef1 ef2 ef3 hte1 ht1 hte2 ht2 hte3 ht3.
  by apply Htcond with tb.
(* Addr *)
+ move=> Gamma Sigma l ofs h t a hteq; subst. by apply Htloc with h (Bprim t) a.
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
+ by move=> Gamma Sigma ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma i sz s a ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma i s a ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma h t l ofs a ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma e t hi ef' t' ht; inversion ht; subst.
+ move=> Gamma Sigma x t htx ht ef' t' het; subst. by inversion het; subst.
+ move=> Gamma Sigma t sz s i a ht ef' t' ht'; subst. by inversion ht'; subst.
+ move=> Gamma Sigma t s i a ht ef' t' ht'; subst. by inversion ht'; subst.
+ move=> Gamma Sigma t ht ef' t' ht'; subst. by inversion ht'; subst.
+ move=> Gamma Sigma e es rt ef efs ts efs' ih ih' ef' t' ht; subst.
  inversion ht; subst. move: (ih ef0 (Ftype ts0 efs0 t') H6)=> 
  [] [] h1 h2 h3; subst. by move: (ih'  efs'0 ts0 H7)=> [] h1 h2; subst.
+ move=> Gamma Sigma e ef h bt a ih ef' t' ht; inversion ht; subst.
  by move: (ih ef0 (Ptype bt) H7)=> [] h1 h2; subst.
+ move=> Gamma Sigma e ef h bt a ih ef' t' ht; inversion ht; subst.
  by move: (ih ef0 (Reftype h0 (Bprim bt) a0) H5)=> [] [] h1 h2 h3; subst.
+ move=> Gamma Sigma e1 e2 ef1 ef2 h bt a ih ih' ef' t' ht; inversion ht; subst.
  move: (ih' ef'0 (Ptype bt0) H6)=> [] h1 h2; subst.
  by move: (ih ef (Reftype h0 (Bprim bt0) a0) H3)=> [] [] h1' h2' h3' h4'; subst.
+ move=> Gamma Sigma op e ef t ih ef' t' ht; inversion ht; subst.
  by move: (ih ef' t' H6)=> [] h1 h2; subst.
+ move=> Gamma Sigma op e1 e2 ef t tr ih ih' ef' t' ht; inversion ht; subst.
  by move: (ih ef' t0 H7)=> [] h1 h2; subst.
+ move=> Gamma Sigma x t e e' t' ef ef' ih ih' ef'' t'' ht; inversion ht; subst.
  move: (ih ef0 t H8)=> [] h1 h2; subst.
  by move: (ih' ef'0 t'' H9)=> [] h1' h2'; subst.
+ move=> Gamma Sigma e1 e2 e3 ef1 ef2 ef3 tb t ih1 hb ih2 ih3 ef' t' ht; inversion ht; subst.
  move: (ih1 ef0 tb0 H5)=> [] h1 h2; subst. move: (ih2 ef4 t' H9)=> [] h1' h2'; subst.
  by move: (ih3 ef5 t' H10)=> [] h1'' h2''; subst.
+ by move=> Gamma Sigma efs' ts' ht; inversion ht; subst.
+ by move=> Gamma Sigma l h bt a ofs hl ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma efs' ts' ht; inversion ht; subst.
move=> Gamma Sigma e es t ef ts efs ih ih' efs' ts' ht; inversion ht; subst.
move: (ih ef0 t0 H3)=> [] h1 h2; subst. by move: (ih' efs0 ts0 H6)=> [] h1 h2; subst.
Qed.

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
+ case: t=> //= p. case: p=> //=.
  case: t'=> //= p'. by case: p'=> //=.
+ case: t=> //= p. case: p=> //=.
  case: t'=> //= p. by case: p=> //=.
+ case: t=> //= p. 
  + case: p=> //=; case: t'=> //= p. by case: p=> //=.
  + by case: Twptr=> //=; case: t'=> //= p'; case: p'=> //=.
  by case: Twptr=> //=; case: t'=> //= p'; case: p'=> //=.
case: t=> //= p.
+ case: p=> //=; case: t'=> //= p.
  by case: p=> //=.
+ by case: Twptr=> //=; case: t'=> //= p'; case: p'=> //=.
by case: Twptr=> //=; case: t'=> //= p'; case: p'=> //=.
Qed.

Lemma eq_type_rel : forall v t t',
eq_type t t' ->
typeof_value v t' ->
typeof_value v t.
Proof.
move=> v t t'. case: t=> //=.
+ move=> p. case: t'=> //= p'.
  case:p=> //=.
  + by case: p'=> //=.
  + by case: p'=> //=.
  by case: p'=> //=.
+ by case: t'=> //=. 
by case: t'=> //=.
Qed.

(* Complete Me *) (* Difficult *)
(**** Substitution preserves typing ****)
(* Substitution preserve typing says that suppose we
   have an expression [e] with a free variable [x], and suppose we've been
   able to assign a type [t'] to [e] under the assumption that [x] has
   some type [t].  Also, suppose that we have some other term [e'] and
   that we've shown that [e'] has type [t].  Then, since [e'] satisfies
   the assumption we made about [x] when typing [e], we should be
   able to substitute [e'] for each of the occurrences of [x] in [e]
   and obtain a new expression that still has type [t]. *)
Lemma subst_preservation : forall Gamma Sigma vm hm hm' x t v e ef t' e'', 
type_expr (extend_context Gamma x.(vname) t) Sigma e ef t' ->
typeof_value v t ->
subst vm hm x.(vname) v e hm' e'' ->
type_expr Gamma Sigma e'' ef t'.
Proof.
Admitted.

(* Complete Me *)
Lemma extend_ty_context_deterministic : forall Gamma Sigma x x' t1 t2 e ef t,
(x =? x')%positive = false ->
type_expr (extend_context (extend_context Gamma x t1) x' t2) Sigma e ef t ->
type_expr (extend_context Gamma x t1) Sigma e ef t. 
Proof.
  intros Gamma Sigma x x' t1 t2 e ef t Hneq Htype.
  induction Htype.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
    assumption.
  - constructor.
    + unfold extend_context in *.
      destruct (PTree.get (vname x0) (PTree.set x' t2 (PTree.set x t1 Gamma))) eqn:Hget;
      apply PTree.gss.
    + assumption.
  - eapply Ty_constint with (Gamma := extend_context Gamma x t1).
    apply H.
  - eapply Ty_constlong with (Gamma := extend_context Gamma x t1).
    apply H.
  - eapply Ty_constunit with (Gamma := extend_context Gamma x t1).
    apply H.
  - eapply Ty_app with (Gamma := extend_context Gamma x t1).
    apply IHHtype.
  - admit.
  - eapply Ty_prim_ref with (Gamma := extend_context Gamma x t1).
    apply IHHtype.
  - eapply Ty_prim_deref with (Gamma := extend_context Gamma x t1).
    apply IHHtype.
  - eapply Ty_prim_massgn with (Gamma := extend_context Gamma x t1).
    + apply IHHtype1.
    + apply IHHtype2.
  - eapply Ty_prim_uop with (Gamma := extend_context Gamma x t1).
    apply IHHtype.
  - eapply Ty_prim_bop with (Gamma := extend_context Gamma x t1).
    + apply IHHtype1.
    + apply IHHtype2.
  - eapply Ty_bind with (Gamma := extend_context Gamma x t1).
    + apply IHHtype1.
    + admit.
  - eapply Ty_cond with (Gamma := extend_context Gamma x t1).
    + apply IHHtype1.
    + apply H.
    + apply IHHtype2.
    + apply IHHtype3.
  - constructor.
  - eapply Ty_addr with (Gamma := extend_context Gamma x t1).
    apply H.
Admitted.

(* Complete Me *)
Lemma deref_addr_val_ty : forall ty m addr ofs v,
deref_addr ty m addr ofs Full v ->
typeof_value v ty.
Proof.
Admitted.

(* Value typing *)
(* A value does not produce any effect *)
Lemma value_typing : forall Gamma Sigma ef t v,
type_expr Gamma Sigma (Val v t) ef t ->
ef = empty_effect.
Proof.
move=> Gamma Sigma ef t v ht. elim: v ht=> //=.
(* unit *)
+ move=> ht. by inversion ht.
(* int *)
+ move=> i ht. by inversion ht.
(* long *)
+ move=> i ht. by inversion ht.
move=> l ofs ht. by inversion ht.
Qed.

(* Subject reduction *)
(* A well-typed expression remains well-typed under top-level lreduction *)
Lemma sreduction_lreduction : forall Gamma Sigma genv ef t vm e m e' m', 
type_expr Gamma Sigma e ef t ->
is_top_level e = true /\ is_lv e = true ->
lreduction genv vm e m e' m' ->
type_expr Gamma Sigma e' ef t.
Proof.
move=> Gamma Sigma genv ef t vm e m e' m'.
elim: e=> //=.
(* val *)
+ by move=> v t' ht [] //=.
(* valof *)
+ by move=> e hi t' ht [] //=.
(* var *)
+ move=> v ht _ hl. inversion hl; subst.
  (* local *)
  + inversion ht; subst. rewrite H1. 
    by apply Ty_addr with h t0 a. 
  (* global *)
  + inversion ht; subst. rewrite H1.
    by apply Ty_addr with h t0 a. 
(* const *)
+ by move=> c t' ht [] //=.
(* app *)
+ by move=> e hi es t' ht [] //=.
(* prim *)
+ move=> [] //=.
  (* ref *)
  + by move=> es t' ht [] //=.
  (* deref *)
  + move=> es t' ht [] hes _ hl. inversion ht; subst.
    inversion ht; subst. inversion hl; subst.
    rewrite /is_vals in hes. move: hes.
    move=> /andP [] hc _.
    have [h1 h2] := val_cannot_be_reduced genv vm e m e'0 m' hc.
    move: h1. by move=> [].
  (* massgn *)
  + by move=> es t' ht [] h1 //=. 
  (* uop *)
  + by move=> u es t' ht [] //=.
  (* bop *)
  + by move=> b es t' ht [] //=.
  (* run *)
  by move=> m'' es t' ht [] //=.
(* bind *)
+ by move=> x t' e hi e'' ht t'' ht' [] //=.
(* cond *)
+ by move=> e he1 e1 he2 e3 he3 t' ht [] //=.
(* unit *)
+ by move=> t' ht [] //=.
(* addr *)
+ by move=> l ofs ht [] //=.
by move=> m'' e hi t' ht [] //=.
Qed.
    
(**** Progress ****) 

(* A well-typed top-level program always makes progress or is a value *)
(* Take small-step semantics into consideration *) 
Lemma progress_lreduction : forall Gamma Sigma genv ef t vm e m, 
type_expr Gamma Sigma e ef t ->
is_top_level e = true /\ is_lv e = true ->
is_val e \/ exists e' m', lreduction genv vm e m e' m'.
Proof.
move=> Gamma Sigma genv ef t vm e m ht [] hc1 hc2.
induction ht=> //=.
(* var *)
+ inversion H; subst. right. rewrite /= in hc1. 
admit. (* how to get the location as it can be only obtained from vm *)
(* deref *)
rewrite /is_top_level /= in hc1. 
elim: e ht hc2 IHht hc1=> //=.
Admitted.

(* A well-typed top-level program always makes progress or is a value *)
(* Take small-step semantics into consideration *) 
Lemma progress_rreduction : forall Gamma Sigma genv ef t vm e m, 
type_expr Gamma Sigma e ef t ->
is_val e \/ exists e' m', rreduction genv vm e m e' m'.
Proof.
Admitted.

(**** Preservation ****)
Lemma preservation_lreduction : forall Gamma Sigma genv ef t vm e m e' m', 
type_expr Gamma Sigma e ef t ->
is_top_level e = true /\ is_lv e = true ->
lreduction genv vm e m e' m' ->
type_expr Gamma Sigma e' ef t.
Proof.
Admitted.

Lemma preservation_rreduction : forall Gamma Sigma genv ef t vm e m e' m', 
type_expr Gamma Sigma e ef t ->
is_top_level e = true /\ is_rv e = true ->
rreduction genv vm e m e' m' ->
type_expr Gamma Sigma e' ef t.
Proof.
Admitted.

    
    
