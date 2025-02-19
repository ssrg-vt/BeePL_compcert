Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Coqlib Memory Ctypes Memtype.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL BeePL_auxlemmas BeePL_sem_proofs BeePL_compiler_proofs.
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
| Ty_prim_bop : forall Gamma Sigma op e ef t e',
                type_expr Gamma Sigma e ef t ->
                type_expr Gamma Sigma e' ef t ->
                type_expr Gamma Sigma (Prim (Bop op) (e::e'::nil) t) ef t 
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
(* fix me : Add typing rule for external function *)
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
Context (Htbop : forall Gamma Sigma op e1 e2 ef t, 
                 Pt Gamma Sigma e1 ef t ->
                 Pt Gamma Sigma e2 ef t ->
                 Pt Gamma Sigma (Prim (Bop op) (e1 :: e2 :: nil) t) ef t).
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
+ move=> Gamma Sigma bop e ef e' hte ht hte' ht' heq.
  by apply Htbop.
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
+ move=> Gamma Sigma op e1 e2 ef t ih ih' ef' t' ht; inversion ht; subst.
  by move: (ih ef' t' H7)=> [] h1 h2; subst.
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

Lemma eq_type_rel : forall v t t',
eq_type t t' ->
typeof_value v (wtype_of_type t') ->
typeof_value v (wtype_of_type t).
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

(* Complete Me *) (* Difficult level *)
(**** Substitution preserves typing ****)
(* Substitution preserve typing says that suppose we
   have an expression [e] with a free variable [x], and suppose we've been
   able to assign a type [t'] to [e] under the assumption that [x] has
   some type [t].  Also, suppose that we have some other term [e'] and
   that we've shown that [e'] has type [t].  Then, since [e'] satisfies
   the assumption we made about [x] when typing [e], we should be
   able to substitute [e'] for each of the occurrences of [x] in [e]
   and obtain a new expression that still has type [t]. *)
Lemma subst_preservation : forall Gamma Sigma bge vm hm hm' x t v e ef t' e'', 
type_expr (extend_context Gamma x.(vname) t) Sigma e ef t' ->
typeof_value v (wtype_of_type t) ->
subst bge vm hm x.(vname) v e hm' e'' ->
type_expr Gamma Sigma e'' ef t'.
Proof.
Admitted.

(* Complete Me *) (* Difficult level *)
Lemma extend_ty_context_deterministic : forall Gamma Sigma x x' t1 t2 e ef t,
(x =? x')%positive = false ->
type_expr (extend_context (extend_context Gamma x t1) x' t2) Sigma e ef t ->
type_expr (extend_context Gamma x t1) Sigma e ef t. 
Proof.
Admitted.

Lemma cty_chunk_rel : forall (ty: Ctypes.type) chunk v,
Ctypes.access_mode ty = By_value chunk ->
Values.Val.has_type v (type_of_chunk chunk) ->
Values.Val.has_type v (typ_of_type ty).
Proof.
move=> ty chunk v ha hv. case: chunk ha hv=> //=.
(* Mbool *)
+ case: ty=> //= f a. by case: f=> //=.
(* Mint8signed *)
+ case: ty=> //= f a. by case: f=> //=.
(* Mint8unsigned *)
+ case: ty=> //= f a. by case: f=> //=.
(* Mint16signed *)
+ case: ty=> //= f a. by case: f=> //=.
(* Mint16unsigned *)
+ case: ty=> //= f a. by case: f=> //=.
(* Mint32 *)
+ case: ty=> //= f a. by case: f=> //=.
(* Mint64 *)
+ case: ty=> //= i s a. 
  + case: i=> //=.
    + by case: s=> //=.
    by case: s=> //=.
  by case: i a=> //=.
(* Mfloat32 *)
+ case: ty=> //= f s a. 
  + case: f=> //=.
    + by case: s=> //=.
    by case: s=> //=.
  by case: f a=> //=.
(* Mfloat64 *)
+ case: ty=> //= f s a. 
  + case: f=> //=.
    + by case: s=> //=.
    by case: s=> //=.
  by case: f a=> //=.
(* Many32 *)
+ case: ty=> //=.
  + move=> i s a. case: i=> //=.
    + by case: s=> //=.
    by case: s=> //=.
  move=> f a. by case: f=> //=.
case: ty=> //=. 
+ move=> i s a. case: i=> //=.
  + by case: s=> //=.
  by case: s=> //=.
move=> f. by case: f=> //=.
Qed.

Lemma bty_chunk_rel : forall (ty: type) chunk,
access_mode ty = By_value (transl_bchunk_cchunk chunk) ->
(wtype_of_type ty) = (typeof_chunk chunk).
Proof.  
move=> ty chunk. case: chunk=> //=; case: ty=> //= p; case: p=> //=.
move=> i s a. case: i=> //=.
+ by case: s=> //=.
case: s=> //=.
Qed.

(*Lemma bty_chunk_rel' : forall (ty: type) chunk,
access_mode ty = By_value (transl_memory_chunk chunk) ->
ty = (typeof_chunk chunk).
Proof.  
move=> ty chunk. case: chunk=> //=; case: ty=> //= p; case: p=> //=.
move=> i s a. case: i=> //=.
+ by case: s=> //=.
case: s=> //=.
Qed.*)

Lemma cval_bval_type_chunk : forall v chunk v',
Values.Val.has_type v (type_of_chunk (transl_bchunk_cchunk chunk)) ->
transC_val_bplvalue v = Errors.OK v' ->
typeof_value v' (typeof_chunk chunk). 
Proof.
move=> v chunk v'. by case: chunk=> //=; case: v=> //=; case: v'=> //=. 
Qed.

(* Complete me *) (* Medium level *)
Lemma cval_bval_type_eq : forall v ct v' bt g g' i,
Values.Val.has_type v (typ_of_type ct) ->
transC_val_bplvalue v = Errors.OK v' ->
transBeePL_type bt g = SimplExpr.Res ct g' i ->
typeof_value v' (wtype_of_type bt). 
Proof.
Admitted.
 
(* Complete me *) (* Medium level *)
Lemma deref_addr_val_ty : forall bge ty m l ofs bf v,
deref_addr bge ty m l ofs bf v ->
typeof_value v (wtype_of_type ty).
Proof.
move=> bge ty m l ofs bf v hd. inversion hd; subst.
+ rewrite /Mem.loadv /= in H2.
  have hvt := Mem.load_type m (transl_bchunk_cchunk chunk) l 
              (Ptrofs.unsigned ofs) v0 H1.
  have hwt := bty_chunk_rel ty chunk H.
  rewrite /typeof_value /= hwt /typeof_chunk /=. 
  by case: chunk H H1 hvt hwt=> //=; case: v hd H2=> //=; case: v0=> //=.
+ admit. (* complete me for the case of volatile load *)
case: ty hd H=> //= p. case: p=> //= i s a.
by case: i=> //=;case: s=> //=.
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

(* Complete Me *)
Lemma uop_type_preserve : forall uop v ct m v',
Cop.sem_unary_operation uop v ct m = Some v' ->
Values.Val.has_type v' (typ_of_type ct).
Proof.
Admitted.

Lemma eq_uop_types : forall uop t g g' i v ct m v' v'',
transBeePL_type t g = SimplExpr.Res ct g' i ->
Cop.sem_unary_operation uop v ct m = Some v' ->
Values.Val.has_type v' (typ_of_type ct) ->
transC_val_bplvalue v' = Errors.OK v'' -> 
typeof_value v'' (wtype_of_type t).
Proof.
Admitted.

(* Complete Me *)
Lemma bop_type_preserve : forall bge bop v1 ct1 v2 ct2 m v,
Cop.sem_binary_operation bge bop v1 ct1 v2 ct2 m = Some v ->
Values.Val.has_type v (typ_of_type ct1) /\
Values.Val.has_type v (typ_of_type ct2).
Proof.
Admitted.

Lemma eq_bop_types : forall cenv v1 t1 g g' i v2 t2 g'' i' ct1 ct2 op m v v',
transBeePL_type t1 g = SimplExpr.Res ct1 g' i ->
transBeePL_type t2 g' = SimplExpr.Res ct2 g'' i' ->
Cop.sem_binary_operation cenv op v1 ct1 v2 ct2 m = Some v ->
transC_val_bplvalue v = Errors.OK v' ->
Values.Val.has_type v (typ_of_type ct1) ->
Values.Val.has_type v (typ_of_type ct2) ->
typeof_value v' (wtype_of_type t1) /\ typeof_value v' (wtype_of_type t2).
Proof.
Admitted.

Lemma subject_reduction_bsem_expr_exprs: 
(forall Gamma Sigma es efs ts bge vm m vm' m' vs, type_exprs Gamma Sigma es efs ts ->
                                                  bsem_exprs bge vm m es m' vm' vs ->
                                                  typeof_values vs (wtypes_of_types ts)) /\
(forall Gamma Sigma e ef t bge vm m vm' m' v, type_expr Gamma Sigma e ef t ->
                                              bsem_expr bge vm m e m' vm' v ->
                                              typeof_value v (wtype_of_type t)).
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall bge vm m vm' m' vs, bsem_exprs bge vm m es m' vm' vs ->
                                                                 typeof_values vs (wtypes_of_types ts)) /\
       (forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                                   forall bge vm m vm' m' v, bsem_expr bge vm m e m' vm' v ->
                                                             typeof_value v (wtype_of_type t)).
+ move=> [] ih ih'. split=> //=.
  + move=> Gamma Sigma es efs ts bge vm m m' vm' vs hts hes. 
    by move: (ih Gamma Sigma es efs ts hts bge vm m m' vm' vs hes).
  move=> Gamma Sigma e ef t bge vm m m' vm' v ht he.
  by move: (ih' Gamma Sigma e ef t ht bge vm m m' vm' v he).
apply type_expr_indP => //=.
(* val unit *)
+ move=> Gamma Sigma bge vm m vm' m' v hv. by inversion hv; subst.
(* val int *)
+ move=> Gamma Sigma i sz s a bge vm m vm' m' v hv. by inversion hv; subst.
(* val long *)
+ move=> Gamma Sigma i s a bge vm m vm' m' v hv. by inversion hv; subst.
(* val loc *)
+ move=> Gamma Sigma h t l ofs a bge vm m vm' m' v hv. by inversion hv; subst.
(* var *)
+ move=> Gamma Sigma x t ht hteq bge vm m vm' m' v hv. inversion hv; subst.
  (* local *)
  + by have := deref_addr_val_ty bge (vtype x) m' l ofs Full v H3.
  (* global *)
  + by have := deref_addr_val_ty bge (vtype x) m' l ofs Full v H4.
(* const int *)
+ move=> Gamma Sigma t sz s i a hteq bge vm m vm' m' v hv. by inversion hv; subst.
(* const long *)
+ move=> Gamma Sigma t s i a hteq bge vm m vm' m' v hv. by inversion hv; subst.
(* const unit *)
+ move=> Gamma Sigma t hteq bge vm m vm' m' v hv. by inversion hv; subst.
(* app *)
+ move=> Gamma Sigma e es rt ef ef' ts ef'' hie hies bge vm m vm' m' v hv.
  inversion hv; subst. move: (hie bge vm m vm2 m2 (Vloc l Ptrofs.zero) H2)=> het.
  move: (hies bge vm3 m3 vm4 m4 vs H7)=> hest. by inversion H4; subst.
(* ref *)
+ move=> Gamma Sigma e ef h bt a hi bge vm m vm' m' v hv. by inversion hv; subst.
(* deref *)
+ move=> Gamma Sigma e ef h bt a hi bge vm m vm' m' v hv. inversion hv; subst.
  move: (hi bge vm m vm' m' (Vloc l ofs) H3)=> hlt. 
  have hvt := deref_addr_val_ty bge (typeof_expr e) m l ofs bf v H7.
  by rewrite H0 /= in hvt.
(* massgn *)
+ move=> Gamma Sigma e1 e2 ef1 ef2 h bt a hi1 hi2 bge vm m vm' m' v hv.
  by inversion hv; subst. 
(* uop *)
+ move=> Gamma Sigma op e ef t he bge vm m vm' m' v hv. inversion hv; subst.
  have hvt' := uop_type_preserve op (transBeePL_value_cvalue v0) ct m' v' H9.
  by have := eq_uop_types op (typeof_expr e) g g' i (transBeePL_value_cvalue v0) ct m' v' v
             H5 H9 hvt' H10.
(* bop *)
+ move=> Gamma Sigma op e1 e2 ef t he1 he2 bge vm m vm' m' v hv. inversion hv; subst.
  have [hvt0 hvt0'] := bop_type_preserve cenv op (transBeePL_value_cvalue v1) ct1 
                       (transBeePL_value_cvalue v2) ct2 m' v0 H12.
  by have [hvt hvt'] := eq_bop_types cenv (transBeePL_value_cvalue v1) (typeof_expr e1) g g' i
          (transBeePL_value_cvalue v2) (typeof_expr e2) g'' i' ct1 ct2 op m' v0 v H7 H11 H12 H13 hvt0 hvt0'.
(* bind *)
+ move=> Gamma Sigma x t e e' t' ef ef' hie hie' bge vm m vm' m' v hv. inversion hv; subst.
  move: (hie bge vm m vm'0 m'0 v0 H9)=> hvt0. admit.
(* cond *)
+ move=> Gamma Sigma e1 e2 e3 ef1 ef2 ef3 tb t het1 hb het2 het3 bge vm m vm' m' v hv.
  inversion hv; subst.
  (* true *)
  + by move: (het2 bge vm'0 m'0 vm' m' v H11).
  (* false *)
  by move: (het3 bge vm'0 m'0 vm' m' v H11).
(* unit *)
+ move=> Gamma Sigma bge vm m vm' m' v he. by inversion he; subst.
(* addr *)
+ move=> Gamma Sigma l h bt a ofs ht bge vm m vm' m' v he. 
  rewrite ht /=. by inversion he; subst.
(* nil *)
+ move=> Gamma Sigma bge vm m vm' m' vs hv. by inversion hv; subst.
(* cons *)
move=> Gamma Sigma e es t ef ts efs hi his bge vm m vm' m' vs hv.
inversion hv; subst. move: (hi bge vm m vm'0 m'0 v H3) => hvt.
move: (his bge vm'0 m'0 vm' m' vs0 H7)=> hvts. by rewrite /typeof_values.
Admitted.  


Section Subject_Reduction.

Variable (bge : genv).
Variable (benv : vmap).

(* Subject reduction : Big step semantics *) 
Lemma subject_lredcution : forall m e l ofs Gamma Sigma ef t,
bsem_expr_slv bge benv m e l ofs ->
type_expr Gamma Sigma e ef t ->
l.(ltype) = t.
Proof.
move=> m e l ofs Gamma Sigma ef t hl. 
by induction hl=> //= ht; subst; inversion ht; subst; symmetry.
Qed.

Lemma subject_rreduction : forall m e v Gamma Sigma ef t, 
bsem_expr_srv bge benv m e v ->
type_expr Gamma Sigma e ef t ->
typeof_value v (wtype_of_type t).
Proof.
move=> m e v Gamma Sigma ef t hr. move: Gamma Sigma ef t.
induction hr=> //=. 
(* Val *)
+ move=> Gamma Sigma ef t' ht. 
  by inversion ht; subst; rewrite /typeof_value /wtype_of_type.
(* Deref *)
+ move=> Gamma Sigma ef t' ht.
  inversion ht; subst. rewrite H7.
  have := subject_lredcution hm e l ofs Gamma Sigma ef0 (Reftype h (Bprim bt) a) H H9=> hlt.
  by have := deref_addr_val_ty bge (typeof_expr e) hm l.(lname) ofs l.(lbitfield) v H0.
(* Uop *)
+ move=> Gamma Sigma ef t' ht. inversion ht; subst.
  move: (IHhr Gamma Sigma ef (typeof_expr e) H10)=> hvt.
  have hvt' := uop_type_preserve uop (transBeePL_value_cvalue v) ct hm v' H1.
  by have := eq_uop_types uop (typeof_expr e) g g' i (transBeePL_value_cvalue v) ct hm v'
          v'' H H1 hvt' H2.
(* Bop *)
+ move=> Gamma Sigma ef t' ht; subst. inversion ht; subst.
  move: (IHhr1 Gamma Sigma ef t' H12)=> hvt1. move: (IHhr2 Gamma Sigma ef t' H13)=> hvt2.
  have [hvt hvt'] := bop_type_preserve bge bop (transBeePL_value_cvalue v1) ct1 
     (transBeePL_value_cvalue v2) ct2 hm v H2.
  by have := cval_bval_type_eq v ct1 v' (typeof_expr e1) g g' i hvt H3 H; case: H1=> [] h1 h2; subst.
Qed.

(*Lemma subject_bstep_exprst : forall Gamma Sigma e ef t f k vm m e' k' vm' m',
type_expr Gamma Sigma e ef t ->
((Smallstep.plus bstep bge benv (ExprState f e k vm m) (ExprState f e' k' vm' m')) \/
(Smallstep.star bstep bge benv (ExprState f e k vm m) (ExprState f e' k' vm' m'))) ->
type_expr Gamma Sigma e' ef t.
Proof.
apply leftcontext_leftcontextlist_ind.
move=> Gamma Sigma e ef t f k vm m e' k' vm' m' hte he.
move: Gamma Sigma ef t f k vm m e' k' vm' m' he hte.
elim: e=> //=.
(* val *)
+ move=> v t Gamma Sigma ef t' f k vm m e' k' vm' m' he hte.
  inversion he; subst.
  (* val *)
  + by inversion H9.
  (* deref *)
  + 
  inversion hte; subst. inversion he; subst.
  (* .. *)
  + by inversion H9.
  + inversion H5*)

End Subject_Reduction.

(* Subject reduction : Small step semantics *)
(* A well-typed expression remains well-typed under top-level lreduction *)
Lemma slreduction : forall Gamma Sigma genv ef t vm e m e' m', 
type_expr Gamma Sigma e ef t ->
lreduction genv vm e m e' m' ->
type_expr Gamma Sigma e' ef t.
Proof.
move=> Gamma Sigma genv ef t vm e m e' m' ht he.
induction he=> //=.
+ inversion ht; subst. rewrite H0. by apply Ty_addr with h t0 a. 
+ inversion ht; subst. rewrite H0. by apply Ty_addr with h t0 a.
Qed.


    
    
