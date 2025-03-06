Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Globalenvs Coqlib Memory. 
Require Import Csyntax Csem SimplExpr Ctypes Memtype.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL BeePL_auxlemmas BeePL_sem BeePL_compiler_proofs Errors.
From mathcomp Require Import all_ssreflect. 

Definition empty_effect : effect := nil. 

Definition type_bool (t : type) : Prop :=
classify_bool t <> bool_default. 

Inductive type_expr : ty_context -> store_context -> expr -> effect -> type -> Prop :=
(*For all value expression, we can assume any effect type, including the empty effect *)
| ty_valu : forall Gamma Sigma ef,
            type_expr Gamma Sigma (Val Vunit (Ptype Tunit)) ef (Ptype Tunit)
| ty_vali : forall Gamma Sigma ef i sz s a,
            type_expr Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) ef (Ptype (Tint sz s a))
| ty_vall : forall Gamma Sigma ef i s a,
            type_expr Gamma Sigma (Val (Vint64 i) (Ptype (Tlong s a))) ef (Ptype (Tlong s a))
| ty_valloc : forall Gamma Sigma ef l ofs h t a,
              PTree.get l Sigma = Some (Reftype h t a) ->
              type_expr Gamma Sigma (Val (Vloc l ofs) (Reftype h t a)) ef (Reftype h t a)
| ty_var : forall Gamma Sigma x t, 
           PTree.get x (extend_context Gamma x t) = Some t ->
           type_expr Gamma Sigma (Var x t) empty_effect t
| ty_constint : forall Gamma Sigma t sz s a i,
                t = (Ptype (Tint sz s a)) ->
                type_expr Gamma Sigma (Const (ConsInt i) t) empty_effect t
| ty_constlong : forall Gamma Sigma t s a i,
                 t = (Ptype (Tlong s a)) ->
                 type_expr Gamma Sigma (Const (ConsLong i) t) empty_effect t
| ty_constunit : forall Gamma Sigma t,
                 t = (Ptype Tunit) ->
                 type_expr Gamma Sigma (Const (ConsUnit) t) empty_effect t
(* Fix me *)
| ty_app : forall Gamma Sigma e es rt efs ts ef efs', 
           type_expr Gamma Sigma e ef (Ftype ts efs rt) -> 
           type_exprs Gamma Sigma es efs' ts -> 
           type_expr Gamma Sigma (App e es rt) (ef ++ efs ++ efs') rt
| ty_prim_ref : forall Gamma Sigma e ef h bt a, 
                type_expr Gamma Sigma e ef (Ptype bt) ->
                type_expr Gamma Sigma (Prim Ref (e::nil) (Reftype h (Bprim bt) a)) (ef ++ (Alloc h :: nil)) (Reftype h (Bprim bt) a) 
| ty_prim_deref : forall Gamma Sigma e ef h bt a, (* inner expression should be unrestricted as it will be used later *)
                  type_expr Gamma Sigma e ef (Reftype h (Bprim bt) a) -> 
                  type_expr Gamma Sigma (Prim Deref (e::nil) (Ptype bt)) (ef ++ (Read h :: nil)) (Ptype bt)
| ty_prim_massgn : forall Gamma Sigma e e' h bt ef a ef', 
                   type_expr Gamma Sigma e ef (Reftype h (Bprim bt) a) ->
                   type_expr Gamma Sigma e' ef' (Ptype bt) ->
                   type_expr Gamma Sigma (Prim Massgn (e::e'::nil) (Ptype Tunit)) (ef ++ ef' ++ (Write h :: nil)) (Ptype Tunit)
| ty_prim_uop : forall Gamma Sigma op e ef t,
                is_reftype t = false ->
                is_unittype t = false ->
                type_expr Gamma Sigma e ef t ->
                (*type_expr Gamma Sigma e (ef ++ ef') t ->*)
                type_expr Gamma Sigma (Prim (Uop op) (e::nil) t) ef t
                (*type_expr Gamma Sigma (Prim (Uop op) (e::nil) t) (ef ++ ef') t*)
| ty_prim_bop : forall Gamma Sigma op e ef t e',
                is_reftype t = false ->
                is_unittype t = false ->
                type_expr Gamma Sigma e ef t ->
                type_expr Gamma Sigma e' ef t ->
                type_expr Gamma Sigma (Prim (Bop op) (e::e'::nil) t) ef t 
| ty_bind : forall Gamma Sigma x t e e' t' ef ef',
            type_expr Gamma Sigma e ef t ->
            type_expr (extend_context Gamma x t) Sigma e' ef' t' ->
            type_expr Gamma Sigma (Bind x t e e' t') (ef ++ ef') t'
| ty_cond : forall Gamma Sigma e1 e2 e3 tb t ef1 ef2 ef3, 
            type_expr Gamma Sigma e1 ef1 tb ->
            type_bool tb ->
            type_expr Gamma Sigma e2 ef2 t ->
            type_expr Gamma Sigma e3 ef3 t ->
            type_expr Gamma Sigma (Cond e1 e2 e3 t) (ef1 ++ ef2 ++ ef3) t
| ty_unit : forall Gamma Sigma,
            type_expr Gamma Sigma (Unit (Ptype Tunit)) empty_effect (Ptype Tunit)
| ty_addr : forall Gamma Sigma l ofs t',
            PTree.get l.(lname) Sigma = Some t' ->
            (*t' = (Reftype h t a) ->*)
            type_expr Gamma Sigma (Addr l ofs t') empty_effect t' 
(* fix me : Run *)
(* fix me : Hexpr *)
(*| ty_hexpr : forall Gamma Sigma m e h ef t a, 
             type_expr Gamma Sigma e ef (Reftype h (Bprim t) a) ->
             type_expr Gamma Sigma (Hexpr m e (Reftype h (Bprim t) a)) ef (Reftype h (Bprim t) a)*)
(* fix me : Add typing rule for external function *)
with type_exprs : ty_context -> store_context -> list expr -> effect -> list type -> Prop :=
| ty_nil : forall Gamma Sigma,
           type_exprs Gamma Sigma nil nil nil
| ty_cons : forall Gamma Sigma e es ef efs t ts,
            type_expr Gamma Sigma e ef t ->
            type_exprs Gamma Sigma es efs ts ->
            type_exprs Gamma Sigma (e :: es) (ef ++ efs) (t :: ts).
           
Scheme type_expr_ind_mut := Induction for type_expr Sort Prop
  with type_exprs_ind_mut := Induction for type_exprs Sort Prop.
Combined Scheme type_exprs_type_expr_ind_mut from type_exprs_ind_mut, type_expr_ind_mut.

(* The (EXTEND) rule states that we can always assume a worse effect; 
   this rule is not part of the inference rules but
   we need it to show subject reduction of stateful computations. : Leijen's koka paper *)
(* This hypothesis makes the type system non-deterministic *)
(*Hypothesis ty_extend : forall Gamma Sigma e t ef, 
                        type_expr Gamma Sigma e empty_effect t ->
                        type_expr Gamma Sigma e (ef ++ empty_effect) t.*)

Section type_expr_ind.
Context (Pts : ty_context -> store_context -> list expr -> effect -> list type -> Prop).
Context (Pt : ty_context -> store_context -> expr -> effect -> type -> Prop).
Context (Htvalu : forall Gamma Sigma ef,
                  Pt Gamma Sigma (Val Vunit (Ptype Tunit)) ef (Ptype Tunit)).
Context (Htvali : forall Gamma Sigma ef i sz s a,
                  Pt Gamma Sigma (Val (Vint i) (Ptype (Tint sz s a))) ef (Ptype (Tint sz s a))).
Context (Htvall : forall Gamma Sigma ef i s a,
                  Pt Gamma Sigma (Val (Vint64 i) (Ptype (Tlong s a))) ef (Ptype (Tlong s a))).
Context (Htvalloc : forall Gamma Sigma ef l ofs h t a,
                    PTree.get l Sigma = Some (Reftype h t a) ->
                    Pt Gamma Sigma (Val (Vloc l ofs) (Reftype h t a)) ef (Reftype h t a)).
Context (Htval : forall Gamma Sigma v ef t,
                 Pt Gamma Sigma (Val v t) ef t).
Context (Htvar : forall Gamma Sigma x t,
                 PTree.get x (extend_context Gamma x t) = Some t ->
                 Pt Gamma Sigma (Var x t) empty_effect t).
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
                is_reftype t = false ->
                is_unittype t = false ->
                Pt Gamma Sigma e ef t ->
                Pt Gamma Sigma (Prim (Uop op) (e :: nil) t) ef t).
Context (Htbop : forall Gamma Sigma op e1 e2 ef t, 
                 is_reftype t = false ->
                 is_unittype t = false ->
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
Context (Htloc : forall Gamma Sigma l ofs t', 
                 PTree.get l.(lname) Sigma = Some t'  ->
                 (*t' = (Reftype h t a) ->*)
                 Pt Gamma Sigma (Addr l ofs t') empty_effect t'). 
(*Context (Htheap : forall Gamma Sigma m e h ef t a, 
                  Pt Gamma Sigma e ef (Reftype h (Bprim t) a) ->
                  Pt Gamma Sigma (Hexpr m e (Reftype h (Bprim t) a)) ef (Reftype h (Bprim t) a)).*)
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
+ move=> Gamma Sigma op e ef t hte hte' ht.
  by apply Htop.
(* Mbop *)
+ move=> Gamma Sigma bop e ef e' hte ht hte' hte'' ht' heq.
  by apply Htbop.
(* Bind *)
+ move=> Gamma Sigma h t e e' t' ef hte ht hte' ht'.
  by apply Htbind.
(* Cond *)
+ move=> Gamma Sigma e1 e2 e3 tb t ef1 ef2 ef3 hte1 ht1 hte2 ht2 hte3 ht3.
  by apply Htcond with tb.
(* Addr *)
(*+ move=> Gamma Sigma l ofs ef. hteq; subst. by apply Htloc.*)
(* Hexpr 
+ move=> Gamma Sigma m e h ef t a hte ht. by apply Htheap.*)
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
+ admit. (*by move=> Gamma Sigma v ef t ef' t' ht; inversion ht; subst.*)
+ admit.
+ admit.
+ admit.
+ move=> Gamma Sigma x t ht ef' t' het; subst. by inversion het; subst.
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
+ move=> Gamma Sigma op e ef t hf hf' ih ef' t' ht; inversion ht; subst.
  by move: (ih ef' t' H8)=> [] h1 h2; subst.
+ move=> Gamma Sigma op e1 e2 ef t hf hf' ih ih' ef' t' ht; inversion ht; subst.
  by move: (ih ef' t' H9)=> [] h1 h2; subst.
+ move=> Gamma Sigma x t e e' t' ef ef' ih ih' ef'' t'' ht; inversion ht; subst.
  move: (ih ef0 t H8)=> [] h1 h2; subst.
  by move: (ih' ef'0 t'' H9)=> [] h1' h2'; subst.
+ move=> Gamma Sigma e1 e2 e3 ef1 ef2 ef3 tb t ih1 hb ih2 ih3 ef' t' ht; inversion ht; subst.
  move: (ih1 ef0 tb0 H5)=> [] h1 h2; subst. move: (ih2 ef4 t' H9)=> [] h1' h2'; subst.
  by move: (ih3 ef5 t' H10)=> [] h1'' h2''; subst.
+ by move=> Gamma Sigma efs' ts' ht; inversion ht; subst.
+ by move=> Gamma Sigma l ofs t' hl ef' t'' ht; inversion ht; subst.
+ by move=> Gamma Sigma efs' ts' ht; inversion ht; subst.
move=> Gamma Sigma e es t ef ts efs ih ih' efs' ts' ht; inversion ht; subst.
move: (ih ef0 t0 H3)=> [] h1 h2; subst. by move: (ih' efs0 ts0 H6)=> [] h1 h2; subst.
Admitted.

Lemma type_rel_typeof : forall Gamma Sigma e ef t,
type_expr Gamma Sigma e ef t ->
typeof_expr e = t.
Proof.
by move=> Gamma Sigma e ef t ht; inversion ht; subst; rewrite /typeof_expr /=; auto.
Qed.

Lemma eq_type_rel : forall v t t',
eq_type t t' ->
wtypeof_value v (wtype_of_type t') ->
wtypeof_value v (wtype_of_type t).
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
Lemma wsubst_preservation : forall Gamma Sigma x t v e ef t' e'', 
type_expr (extend_context Gamma x t) Sigma e ef t' ->
wtypeof_value v (wtype_of_type t) ->
subst x (Val v t) e = e'' ->
type_expr Gamma Sigma e'' ef t'.
Proof.
Admitted.

Lemma subst_preservation : forall Gamma Sigma x t se e ef' ef t' e', 
type_expr (extend_context Gamma x t) Sigma e ef' t' ->
type_expr Gamma Sigma se ef t ->
subst x se e = e' ->
type_expr Gamma Sigma e' ef' t'.
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

Lemma wbty_chunk_rel : forall (ty: type) chunk,
access_mode ty = By_value (transl_bchunk_cchunk chunk) ->
(wtype_of_type ty) = (wtypeof_chunk chunk).
Proof.  
move=> ty chunk. case: chunk=> //=; case: ty=> //= p; case: p=> //=.
move=> i s a. case: i=> //=.
+ by case: s=> //=.
case: s=> //=.
Qed.

Lemma cval_bval_type_chunk : forall v chunk v',
Values.Val.has_type v (type_of_chunk (transl_bchunk_cchunk chunk)) ->
transC_val_bplvalue v = Errors.OK v' ->
wtypeof_value v' (wtypeof_chunk chunk). 
Proof.
move=> v chunk v'. by case: chunk=> //=; case: v=> //=; case: v'=> //=. 
Qed.

(* Value typing *)
(* A value does not produce any effect *)
Lemma value_typing : forall Gamma Sigma ef t v,
type_expr Gamma Sigma (Val v t) ef t ->
type_expr Gamma Sigma (Val v t) empty_effect t. 
Proof.
move=> Gamma Sigma ef t v ht. inversion ht.
+ by apply ty_valu.
+ by apply ty_vali.
+ by apply ty_vall.
by apply ty_valloc.  
Qed.

(* Value type same *)
Lemma type_val_reflx : forall Gamma Sigma v t ef t',
type_expr Gamma Sigma (Val v t) ef t' -> 
t = t'.
Proof.
move=> Gamma Sigma v t ef t' ht. by inversion ht; subst.
Qed.


(* Complete Me: Easy *)
(* There always exists a C type for BeePL type which is 
   inferred from the typing rules. *)
Lemma well_typed_success: 
(forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                               exists cts g i, transBeePL_types transBeePL_type ts g = Res cts g i) /\
(forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                            exists ct g i, transBeePL_type t g = Res ct g i).
Proof.
apply type_exprs_type_expr_ind_mut=> //=.
+ move=> Gamma Sigma ef. exists Tvoid. eexists. by eexists.
+ move=> Gamma Sigma ef i sz s a. exists (Ctypes.Tint sz s a). eexists. by eexists.
+ move=> Gamma Sigma ef l s a. exists (Ctypes.Tlong s a). eexists. by eexists.
+ move=> Gamma Sigma ef l ofs h t a hs. case: t hs=> //= p. case: p=> //=.
  + exists (Tpointer Tvoid a). eexists. by eexists.
  + move=> sz s a'. exists (Tpointer (Ctypes.Tint sz s a') a). eexists. by eexists.
  move=> s a'. exists (Tpointer (Ctypes.Tlong s a') a). eexists. by eexists.
+ move=> Gamma Sigma x t ht. case: t ht=> //=.
  + move=> p. case: p=> //=.
    + exists Tvoid.
Admitted.

(**** Well formedness ****)
(** Well-Typed Store **)
(* A store st is well-typed with respect to a store typing context Sigma if the
   term at each location l in vm has the type at location l in store typing context
   and there exists a value in the memory at that location. *)
Definition store_well_typed (Sigma : store_context) (bge : genv) (vm : vmap) (m : Memory.mem) :=
((forall l t, 
 exists l' ofs v, vm! l = Some(l', t) /\
                  PTree.get l Sigma = Some t /\ 
                  deref_addr bge t m l' ofs Full v) \/
(forall l t, vm! l = None /\ 
             exists l' ofs v, Genv.find_symbol bge l = Some l' /\ 
                              deref_addr bge t m l' ofs Full v)) /\
(forall l ofs h t a, PTree.get l Sigma = Some (Reftype h (Bprim t) a) ->
                     exists v, deref_addr bge (Ptype t) m l ofs Full v /\  
                               Mem.valid_pointer m l (Ptrofs.unsigned ofs)) /\
(forall l ofs h t a v, PTree.get l Sigma = Some (Reftype h (Bprim t) a) ->
                       exists bf m', assign_addr bge (Ptype t) m l ofs bf v m' v /\
                                     Mem.valid_pointer m l (Ptrofs.unsigned ofs)).
  
(* A well-typed uop always has a semantics that leads to a value. *)
Lemma well_typed_uop : forall Gamma Sigma bge vm v ef t uop m ct g i,
type_expr Gamma Sigma (Prim (Uop uop) ((Val v t) :: nil) t) ef t ->
transBeePL_type t g = Res ct g i ->
store_well_typed Sigma bge vm m ->
exists v', Cop.sem_unary_operation uop (transBeePL_value_cvalue v) ct m = Some v'.
Proof.
move=> Gamma Sigma bge vm v ef t uop m ct g i htv. case: v htv=> //=. 
(* unit *)
+ move=> htv. inversion htv; subst. inversion H8; subst.
  rewrite /transBeePL_type /=. move=> [] hct hw; subst.
  by case: uop htv=> //=.
(* int *)
+ move=> i' hvt. inversion hvt; subst. inversion H8; subst. 
  rewrite /transBeePL_type. move=> [] hct; subst.
  case: uop hvt=> //=.
  (* sem_notbool *)
  + rewrite /Cop.sem_notbool /option_map /=. 
    case hop: (Cop.bool_val (Values.Vint i') (Ctypes.Tint sz s a) m)=> [ vo | ] //=.
    by exists (Values.Val.of_bool (~~ vo)).
  move: hop. rewrite /Cop.bool_val /=. case hc: (Cop.classify_bool (Ctypes.Tint sz s a))=> //=.
  + rewrite /Cop.classify_bool /= in hc. move: hc. by case: sz H4 H6 H7 H8=> //=.
  + rewrite /Cop.classify_bool /= in hc. move: hc. by case: sz H4 H6 H7 H8=> //=.
  + rewrite /Cop.classify_bool /= in hc. move: hc. by case: sz H4 H6 H7 H8=> //=.
  rewrite /Cop.classify_bool /= in hc. move: hc. by case: sz H4 H6 H7 H8=> //=.
  (* sem_notint *)
  + rewrite /Cop.sem_notint /Cop.classify_notint. case: sz H4 H6 H7 H8=> //=.
    + move=> hvt. by exists (Values.Vint (Int.not i')).
    + move=> hvt. by exists  (Values.Vint (Int.not i')).
    + case: s=> //=.
      + by exists (Values.Vint (Int.not i')).
      by exists (Values.Vint (Int.not i')).
    by exists (Values.Vint (Int.not i')).
  (* sem_neg *)
  + rewrite /Cop.sem_neg /Cop.classify_neg. case: sz H4 H6 H7 H8=> //=.
    + by exists (Values.Vint (Int.neg i')).
    + by exists (Values.Vint (Int.neg i')).
    + case: s=> //=. + by exists (Values.Vint (Int.neg i')).
      by exists (Values.Vint (Int.neg i')).
    by exists (Values.Vint (Int.neg i')).
  (* sem_absfloat *)
  + rewrite /Cop.sem_absfloat /Cop.classify_neg /=. case: sz H4 H6 H7 H8=> //=.
    + by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_int i'))).
    + by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_int i'))).
    + case: s=> //=. + by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_int i'))).
      by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_intu i'))).
    by exists (Values.Vfloat (Floats.Float.abs (Floats.Float.of_int i'))).
(* long *)
+ move=> i' hvt. inversion hvt; subst. inversion H8; subst. 
  rewrite /transBeePL_type. move=> [] hct; subst.
  case: uop hvt=> //=.
  (* sem_notbool *)
  + rewrite /Cop.sem_notbool /option_map /=. 
    by exists (Values.Val.of_bool (~~ ~~ Int64.eq i' Int64.zero)).
  (* sem_notint *)
  + rewrite /Cop.sem_notint /Cop.classify_notint. by exists (Values.Vlong (Int64.not i')).
  (* sem_neg *)
  + rewrite /Cop.sem_neg /Cop.classify_neg. by exists (Values.Vlong (Int64.neg i')).
  (* sem_absfloat *)
  + rewrite /Cop.sem_absfloat /Cop.classify_neg /=. 
    by exists (Values.Vfloat (Floats.Float.abs (Cop.cast_long_float s i'))).
(* ptr *)
move=> p ofs hvt. inversion hvt; subst. inversion H8; subst. case: uop hvt=> //=.
Qed.

(* Complete Me : Easy *)
Lemma trans_value_uop_success : forall Gamma Sigma ef t uop v ct g g' i m v', 
type_expr Gamma Sigma (Val v t) ef t ->
transBeePL_type t g = Res ct g' i ->
Cop.sem_unary_operation uop (transBeePL_value_cvalue v) ct m = Some v' ->
exists v'', transC_val_bplvalue v' = OK v''.
Proof.
Admitted.

(* Complete Me : Medium *) (* Hint : Follow similar proof style like well_typed_uop *)
(* A well-typed bop always has a semantics that leads to a value. *)
Lemma well_typed_bop : forall Gamma Sigma bge vm bcmp v1 v2 ef t bop m ct g i,
type_expr Gamma Sigma (Prim (Bop bop) ((Val v1 t) :: (Val v2 t) :: nil) t) ef t ->
transBeePL_type t g = Res ct g i ->
store_well_typed Sigma bge vm m ->
exists v', Cop.sem_binary_operation bcmp bop (transBeePL_value_cvalue v1) ct 
                                             (transBeePL_value_cvalue v2) ct m = Some v'.
Proof.
Admitted.

(* Complete Me : Easy *)
Lemma trans_value_bop_success : forall Gamma Sigma bcmp bop v1 v2 ef t ct g g' i m v', 
type_expr Gamma Sigma (Val v1 t) ef t ->
type_expr Gamma Sigma (Val v2 t) ef t ->
transBeePL_type t g = Res ct g' i ->
Cop.sem_binary_operation bcmp bop (transBeePL_value_cvalue v1) ct 
                                  (transBeePL_value_cvalue v2) ct m = Some v' ->
exists v'', transC_val_bplvalue v' = OK v''.
Proof.
Admitted.

Lemma type_uop_inject : forall Gamma Sigma e t ef op,
is_reftype t = false ->
is_unittype t = false ->
type_expr Gamma Sigma e ef t ->
type_expr Gamma Sigma (Prim (Uop op) [::e] t) ef t. 
Proof.
move=> Gamma Sigma e t ef op hte. by apply ty_prim_uop.
Qed.

Lemma type_bop_inject : forall Gamma Sigma e1 e2 t ef op,
is_reftype t = false ->
is_unittype t = false ->
type_expr Gamma Sigma e1 ef t ->
type_expr Gamma Sigma e2 ef t ->
type_expr Gamma Sigma (Prim (Bop op) [::e1; e2] t) ef t. 
Proof.
move=> Gamma Sigma e1 e2 t ef op hte. by apply ty_prim_bop.
Qed.

Lemma type_bool_val : forall Gamma Sigma v t ef ct m b,
type_expr Gamma Sigma (Val v t) ef t ->
type_bool t ->
Cop.bool_val (transBeePL_value_cvalue v) ct m = Some b.
Proof.
move=> Gamma Sigma v t ef ct m b hte.
Admitted.

(* A well typed value and expression can always lead to substitution *)
(*Lemma subst_success:  
(*(forall Gamma Sigma es efs ts Gamma x t bge vm m v, type_exprs Gamma' Sigma es efs ts ->
                                                     Gamma = (extend_context Gamma x t) ->
                                                     type_expr Gamma Sigma (Val v t) efs t ->
                                                     store_well_typed Sigma bge vm m ->
                                                     exists m' es', substs bge vm m x v es m' es') /\*)
forall Gamma Sigma ef t x se t' bge vm m e, type_expr Gamma Sigma (Bind x t' se e t) ef t ->
                                            store_well_typed Sigma bge vm m ->
                                            exists e', subst x se e e'.
Proof.
move=> Gamma Sigma ef t x se t' bge vm m e hte hw. inversion hte; subst.
elim: e hte H9=> //=.
(* val *)
+ move=> v1 t1 hte htv. exists (Val v1 t1). by apply val_subst.
(* var *)
+ move=> y t1 hte hty. inversion hty; subst. rewrite /extend_context in H5.
  rewrite PTree.gsspec in H5. move: H5. destruct (peq x y).
  + destruct (peq y y).
    + move=> _. rewrite e /= in hty. inversion hty; subst.
      exists se. apply var_subst1. by apply POrderedType.Positive_as_OT.eqb_refl.
    move: n. by move=> [].
  destruct (peq y y).
  + move=> _. exists (Var y t). apply var_subst2. have [h1 h2] := Pos.eqb_neq x y.
    by move: (h2 n).
  by case: n0.
(* const *)
+ move=> c tc hte ht. exists (Const c tc). by apply const_subst.
(* App *)
+ move=> e hin es ts hte hta.

Admitted. *)

(*** Proving theorems related to type system for small step semantics of BeePL ***)

(* Progress for small step semantics *)
(* A well typed expression is never stuck,
   it either evaluates to a value or can continue executing. *)
Lemma progress_ssem_expr_exprs:
(forall Gamma Sigma es efs ts bge vm m, type_exprs Gamma Sigma es efs ts ->
                                        store_well_typed Sigma bge vm m ->
                                        is_values es \/ exists m' vm' es',
                                                        ssem_exprs bge vm m es m' vm' es') /\
(forall Gamma Sigma e ef t bge vm m, type_expr Gamma Sigma e ef t ->
                                     store_well_typed Sigma bge vm m ->
                                     is_value e \/ exists m' vm' e', 
                                                   ssem_expr bge vm m e m' vm' e').
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall bge vm m, store_well_typed Sigma bge vm m ->
                                                       is_values es \/ exists m' vm' es',
                                                       ssem_exprs bge vm m es m' vm' es') /\
(forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                            forall bge vm m, store_well_typed Sigma bge vm m ->
                                             is_value e \/ exists m' vm' e', 
                                                           ssem_expr bge vm m e m' vm' e').
+ move=> [] hwt1 hwt2. split=> //=.
  + move=> Gamma Sigma es efs ts bge vm m htes hw.
    by move: (hwt1 Gamma Sigma es efs ts htes bge vm m hw).
  move=> Gamma Sigma e ef t bge vm m hte hw. 
  by move: (hwt2 Gamma Sigma e ef t hte bge vm m hw).
apply type_exprs_type_expr_ind_mut=> //=.
(* val unit *)
+ move=> Gamma Sigma ef bge vm m hw. by left.
(* val int *)
+ move=> Gamma Sigma ef i sz s a bge vm m hw. by left.
(* val long *)
+ move=> Gamma Sigma ef i s a bge vm m hw. by left.
(* val loc *)
+ move=> Gamma Sigma ef l ofs h t a bge vm m hw. by left.
(* var *)
+ move=> Gamma Sigma v t hteq bge vm m hw; subst. right.
  rewrite /store_well_typed in hw. case: hw=> hw hw'.
  case: hw=> hw.
  (* lvar *)
  + move:(hw v t)=> [] l [] ofs [] v' [] hvm [] hs hd.
    exists m. exists vm. exists (Val v' t). eapply ssem_lvar.
    + by apply hvm. 
    by apply hd.  
  (* gvar *)
  move: (hw v t)=> [] hvm [] l' [] ofs [] v' [] hbge hd.
  exists m. exists vm. exists (Val v' t). apply ssem_gbvar with l' ofs.
  + by apply hvm.
  + by apply hbge.
  by apply hd.
(* const int *)
+ move=> Gamma Sigma t sz s a i ht bge vm m hw. right.
  exists m. exists vm. exists (Val (Vint i) t). by apply ssem_consti.
(* const long *)
+ move=> Gamma Sigma t s a i ht bge vm m hw. right.
  exists m. exists vm. exists (Val (Vint64 i) t). by apply ssem_constl.
(* const uint *)
+ move=> Gamma Sigma t hteq bge vm m. right; subst.
  exists m. exists vm. exists (Val (Vunit) (Ptype Tunit)). by apply ssem_constu.
(* app *)
+ admit.
(* ref *)
+ move=> Gamma Sigma e ef h bt a hte hin bge vm m hw. 
  move: (hin bge vm m hw)=> [] he.
  (* is value *)
  + admit. (* need to evolve well formedness for store typing more *)
  (* step *)
  right. move: he. move=> [] m' [] vm' [] e' he. exists m'.
  exists vm'. exists (Prim Ref [:: e'] (Reftype h (Bprim bt) a)). by apply ssem_ref1.
(* deref *)
+ move=> Gamma Sigma e ef h bt a hte hin bge vm m hw.
  move: (hin bge vm m hw)=> [].
  (* is value *)
  + move=> hv. right. rewrite /is_value in hv. case: e hv hte hin=> v t //= _. case: v=> //=.
    (* unit *)
    + move=> hte hin. by inversion hte; subst. 
    (* int *)
    + move=> i hte hin. by inversion hte; subst.
    (* long *)
    + move=> l hte hin. by inversion hte; subst.
    (* loc *)
    move=> l ofs hte hin. rewrite /store_well_typed in hw. case: hw=> //= hw [] hw' hw''. 
    inversion hte; subst.
    move: (hw' l ofs h bt a H5) => [] v hd. exists m. exists vm.
    exists (Val v (Ptype bt)). apply ssem_deref2 with Full. by apply hd.
  (* step *)
  + move: (hin bge vm m hw)=> hin'. move=> [] m' [] vm' [] e' he. right.
    exists m'. exists vm'. exists (Prim Deref [:: e'] (Ptype bt)). apply ssem_deref1. 
    by apply he.
(* massgn *)
+ move=> Gamma Sigma e e' h bt ef a ef' hte hin hte' hin' bge vm m hw. right.
  move: (hin bge vm m hw)=> [].
  (* value e *)
  + move=> hv. case: e hte hin hv=> //= v t. case: v=> //=.
    (* unit *)
    + move=> hte. by inversion hte.
    (* int *)
    + move=> i hte. by inversion hte.
    (* long *)
    + move=> l hte. by inversion hte.
    (* loc *)
    move=> l ofs hte hin _. move: (hin' bge vm m hw)=> [] hv'.
    (* value e' *)
    + case: e' hte' hin' hv'=> //= v' t' hte' hin' _. rewrite /store_well_typed in hw.
      case: hw=> hw1 [] hw2 hw3. inversion hte; subst. 
      move: (hw3 l ofs h bt a v' H5)=> [] bf [] m' ha.
      exists m'. exists vm. exists (Val Vunit (Ptype Tunit)). 
      have hteq := type_val_reflx Gamma Sigma v' t' ef' (Ptype bt) hte'; subst. 
      apply ssem_massgn3 with bf. by apply ha.
    (* e' steps *)
    move: hv'. move=> [] m' [] vm' [] e'' he''. exists m'. exists vm'.
    exists (Prim Massgn [:: Val (Vloc l ofs) t; e''] (Ptype Tunit)).
    have hteq := type_val_reflx Gamma Sigma (Vloc l ofs) t ef 
                 (Reftype h (Bprim bt) a) hte; subst. apply ssem_massgn2. by apply he''.
  (* e steps *)
  move=> [] m' [] vm' [] e'' he''. exists m'. exists vm'.
  exists (Prim Massgn [:: e''; e'] (Ptype Tunit)). apply ssem_massgn1. by apply he''.
(* uop *)
+ move=> Gamma Sigma op e ef t hf hf' hte hin bge vm m hw. right.
  move: (hin bge vm m hw)=> [] hv.
  (* value e *)
  + case: e hte hin hv=> //= v t' hte hin _. exists m. exists vm.
    have [hwts hwt] := well_typed_success. 
    have hteq := type_val_reflx Gamma Sigma v t' ef t hte; subst.
    have htuop := type_uop_inject Gamma Sigma (Val v t) t ef op hf hf' hte.
    move: (hwt Gamma Sigma (Val v t) ef t hte)=> [] ct [] g [] i hct.
    have [v' hsop] := well_typed_uop Gamma Sigma bge vm v ef t op m ct g i htuop hct hw.
    have [v'' hbv] := trans_value_uop_success Gamma Sigma ef t op v ct g g i m v' hte hct hsop. 
    exists (Val v'' t). apply ssem_uop2 with v' ct g g i. + by apply hct.
    + by apply hsop. by apply hbv.
  (* step *)
  move: hv. move=> [] m' [] vm' [] e' he'. exists m'. exists vm'.
  exists (Prim (Uop op) [:: e'] t). 
  have hteq := type_rel_typeof Gamma Sigma e ef t hte; subst. by apply ssem_uop1.
(* bop *)
+ move=> Gamma Sigma op e ef t e' hf hf' hte hin hte' hin' bge vm m hw. right.
  move: (hin bge vm m hw)=> [] hv.
  (* value e *)
  + case: e hte hin hv=> //= v t' hte hin _. move:(hin' bge vm m hw)=> [] hv'.
    (* value e' *)
    + case: e' hte' hin' hv'=> //= v' t'' hte' hin' _.
      have hteq := type_val_reflx Gamma Sigma v t' ef t hte; subst.
      have hteq' := type_val_reflx Gamma Sigma v' t'' ef t hte'; subst.
      have [hwt1 hwt2] := well_typed_success. 
      move: (hwt2 Gamma Sigma (Val v t) ef t hte)=> [] ct1 [] g [] i hct1.
      move: (hwt2 Gamma Sigma (Val v' t) ef t hte')=> [] ct2 [] g' [] i' hct2.
      have htop := type_bop_inject Gamma Sigma (Val v t) (Val v' t) t ef op hf hf' hte hte'.
      have [v'' hsop] := well_typed_bop Gamma Sigma bge vm (genv_cenv bge) v v' ef t op 
                         m ct1 g i htop hct1 hw.
      have [v''' htv] := trans_value_bop_success Gamma Sigma (genv_cenv bge) op v v' ef t
                             ct1 g g i m v'' hte hte' hct1 hsop.
      exists m. exists vm. exists (Val v''' t). 
      apply ssem_bop3 with (genv_cenv bge) v'' ct1 ct1 g g i g i. + by apply hct1.
      + by apply hct1. + by apply hsop. by apply htv.
    (* e' steps *)
    move: hv'. move=> [] m' [] vm' [] e'' he''. exists m'. exists vm'. 
    have hteq := type_val_reflx Gamma Sigma v t' ef t hte; subst.
    exists (Prim (Bop op) [:: Val v t; e''] t). apply ssem_bop2. by apply he''.
  (* e steps *)
  move: hv. move=> [] m' [] vm' [] e'' he''. exists m'. exists vm'. 
  have hteq := type_rel_typeof Gamma Sigma e ef t hte; subst.
  exists (Prim (Bop op) [:: e''; e'] (typeof_expr e)). apply ssem_bop1. by apply he''.
(* bind *)
+ move=> Gamma Sigma x t e e' t' ef ef' hte hin hte' hin' bge vm m hw. right.
  move: (hin bge vm m hw)=> [] hv.
  (* value e *)
  + case: e hte hin hv=> //= v tv hte hin _. exists m. exists vm. exists (subst x (Val v tv) e').
    have hteq := type_rel_typeof (extend_context Gamma x t) Sigma e' ef' t' hte'; subst. 
    have hteq' := type_rel_typeof Gamma Sigma (Val v tv) ef t hte; subst.
    by apply ssem_bind2.
  (* e steps *)
  move: hv. move=> [] m' [] vm' [] e'' he''. exists m'. exists vm'. exists (Bind x t e'' e' t').
  have hteq := type_rel_typeof (extend_context Gamma x t) Sigma e' ef' t' hte'; subst. 
  by apply ssem_bind1.
(* cond *)
+ move=> Gamma Sigma e1 e2 e3 tb t ef1 ef2 ef3 hte1 hin htb hte2 hin' hte3 hin'' bge vm m hw.
  right. move: (hin bge vm m hw)=> [] hv.
  (* value e1 *)
  + case: e1 hte1 hin hv=> //= v t' hte1 hin _. exists m. exists vm. exists e2.
    have hteq := type_rel_typeof Gamma Sigma e2 ef2 t hte2; subst. 
    have [hwt1 hwt2] := well_typed_success. move: (hwt2 Gamma Sigma (Val v t') ef1 tb hte1).
    move=> [] ct [] g [] i hct.
    apply ssem_ctrue with g ct g i. 
    + by have hteq := type_val_reflx Gamma Sigma v t' ef1 tb hte1; subst.
    have hteq := type_val_reflx Gamma Sigma v t' ef1 tb hte1; subst.
    by have := type_bool_val Gamma Sigma v tb ef1 ct m true hte1 htb.
  (* e1 steps *) 
  move: hv. move=> [] m' [] vm' [] e1' he1'. exists m'. exists vm'.
  exists (Cond e1' e2 e3 t). have hteq := type_rel_typeof Gamma Sigma e2 ef2 t hte2; subst.
  by apply ssem_cond.
(* unit *)
+ move=> Gamma Sigma bge vm m hw. right. exists m. exists vm. exists (Val Vunit (Ptype Tunit)).
  by apply ssem_ut.
(* addr *)
+ move=> Gamma Sigma l ofs t' hs bge vm m hw. right.
  exists m. exists vm. exists (Val (Vloc l.(lname) ofs) t'). by apply ssem_adr.
(* nil *)
+ move=> Gamma Sigma bge vm m hw. by left.
(* cons *)
move=> Gamma Sigma e es ef efs t ts hte hin htes hins bge vm m hw.
move: (hin bge vm m hw)=> [] hv.
(* value e *)
+ move: (hins bge vm m hw)=> [] hvs.
  (* value es *)
  + left. by rewrite /andb hv. 
  (* es steps *)
  move: hvs. move=> [] m' [] vm' [] es' hes. right.
  case: e hte hin hv=> //= v t' hte hin _. exists m'. exists vm'.
  exists (Val v t' :: es'). by apply ssem_cons2.
move: hv. move=> [] m' [] vm' [] e' he'. right.
exists m'. exists vm'. exists (e' :: es). by apply ssem_cons1.
Admitted.


(*** Preservation for small-step semantics ***)
(* If a program starts well-typed, it remains well-typed throughout execution,
   an evaluation does not produce type errors.*)
Lemma preservation_ssem_expr_exprs: 
(forall Gamma Sigma es efs ts bge vm m vm' m' es', type_exprs Gamma Sigma es efs ts ->
                                                   ssem_exprs bge vm m es m' vm' es' ->
                                                   type_exprs Gamma Sigma es' efs ts) /\
(forall Gamma Sigma e ef t bge vm m vm' m' e', type_expr Gamma Sigma e ef t ->
                                               ssem_expr bge vm m e m' vm' e' ->
                                               type_expr Gamma Sigma e' ef t).
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall bge vm m vm' m' es', ssem_exprs bge vm m es m' vm' es' ->
                                                                  type_exprs Gamma Sigma es' efs ts) /\
       (forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                                   forall bge vm m vm' m' e', ssem_expr bge vm m e m' vm' e' ->
                                                             type_expr Gamma Sigma e' ef t).
+ move=> [] ih ih'. split=> //=.
  + move=> Gamma Sigma es efs ts bge vm m vm' m' es' hts hes.
    by move: (ih Gamma Sigma es efs ts hts bge vm m vm' m' es' hes).
  move=> Gamma Sigma e ef t bge vm m vm' m' e' ht he.
  by move: (ih' Gamma Sigma e ef t ht bge vm m vm' m' e' he).
apply type_exprs_type_expr_ind_mut=> //=.
(*
(* val *)
+ move=> Gamma Sigma v ef t bge vm m vm' m' e' he.
  inversion he; subst. by apply ty_val.
(* var *)
+ move=> Gamma Sigma x t ht hteq bge vm m vm' m' e' he.
  by inversion he; subst; apply ty_val. 
(* const int *)
+ move=> Gamma Sigma t sz s i a hteq bge vm m vm' m' e' he.
  inversion he; subst. by apply ty_val.
(* const long *)
+ move=> Gamma Sigma t s i a hteq bge vm m vm' m' e' he.
  inversion he; subst. by apply ty_val.
(* const unit *)
+ move=> Gamma Sigma t hteq bge vm m vm' m' e' he.
  inversion he; subst. by apply ty_val.
(* app *)
+ move=> Gamma Sigma e es rt ef efs ts efs' hie hies bge vm m vm' m' e' he.
  inversion he; subst.
  (* fd location e and es takes step *) 
  + apply ty_app with ts.   
    + by move: (hie bge vm m vm' m' e'0 H7). admit.
  (* takes step to body of function *)
  admit.
(* ref *)
+ move=> Gamma Sigma e ef h bt a hie bge vm m vm' m' e' he.
  inversion he; subst.
  + apply ty_prim_ref. by move: (hie bge vm m vm' m' e'0 H8).
  have heq : (ef ++ [:: Alloc h]) = (ef ++ [:: Alloc h] ++ empty_effect).
  + rewrite /empty_effect. by rewrite cats0. rewrite heq.
  by apply ty_val.
  (*have hl : type_expr Gamma Sigma (Val (Vloc l ofs) (Reftype h (Bprim bt) a)) empty_effect
     (Reftype h (Bprim bt) a). + by apply ty_val.
  have het := ty_extend Gamma Sigma (Val (Vloc l ofs) (Reftype h (Bprim bt) a)) 
          (Reftype h (Bprim bt) a) (ef ++ [:: Alloc h]) hl. by rewrite catA.*)
(* deref *)
+ move=> Gamma Sigma e ef h bt a hie bge vm m vm' m' e' he.
  inversion he; subst.
  (* e takes step *)
  + apply ty_prim_deref with a. by move: (hie bge vm m vm' m' e'0 H6).
  (* e is a value *)
  by apply ty_val.
  (*have heq : (ef ++ [:: Read h]) = (ef ++ [:: Read h] ++ empty_effect).
  + rewrite /empty_effect. by rewrite cats0. rewrite heq.
  have hl : type_expr Gamma Sigma (Val v (Ptype bt)) empty_effect
     (Ptype bt). + by apply ty_val.
  have het := ty_extend Gamma Sigma (Val v (Ptype bt))
              (Ptype bt) (ef ++ [:: Read h]) hl. by rewrite catA.*)
(* massgn *)
+ move=> Gamma Sigma e1 e2 ef1 ef2 h bt a hie1 hie2 bge vm m vm' m' e' he.
  inversion he; subst.
  (* e1 takes step *)
  + apply ty_prim_massgn with bt a.
    + by move: (hie1 bge vm m vm' m' e1' H6).
    admit. (* why we don't have hypothesis for type of e2 *)
  (* e2 takes step *)
  + apply ty_prim_massgn with bt a0.  admit.
    by move : (hie2 bge vm m vm' m' e2' H6)=> ht2.
  have hvt : type_expr Gamma Sigma (Val Vunit (Ptype Tunit))
  empty_effect (Ptype Tunit). + by apply ty_val.
  have het := ty_extend Gamma Sigma (Val Vunit (Ptype Tunit)) (Ptype Tunit) ((ef1 ++ ef2) ++ [:: Write h]) hvt.
  rewrite /empty_effect cats0 in het. by rewrite catA.
(* uop *)
+ move=> Gamma Sigma op e ef t hie bge vm m vm' m' e' he. inversion he; subst.
  + apply ty_prim_uop. by move: (hie bge vm m vm' m' e'0 H7).
    have hvt : type_expr Gamma Sigma (Val v'' t) empty_effect t. + by apply ty_val.
    have := ty_extend Gamma Sigma (Val v'' t) t ef.
Admitted.*)
Admitted.


(* Stateful effects cannot be discarded :
   Expressions like ref, deref, massgn cannot discard the stateful effect even in the case 
   where it reduces to value *)
Lemma stateful_effects_preserved : 
(forall Gamma Sigma es efs ts bge vm m vm' m' es' efs' ts', 
        type_exprs Gamma Sigma es efs ts ->
        is_stateful_exprs es = true /\ is_stateful_effect efs = true ->
        ssem_exprs bge vm m es m' vm' es' ->
        type_exprs Gamma Sigma es' efs' ts' ->
        is_stateful_effect efs') /\
(forall Gamma Sigma e ef t bge vm m vm' m' e' ef' t', 
        type_expr Gamma Sigma e ef t ->
        is_stateful_expr e = true /\ is_stateful_effect ef = true ->
        ssem_expr bge vm m e m' vm' e' ->
        type_expr Gamma Sigma e' ef' t' ->
        is_stateful_effect ef').
Proof.
suff : (forall Gamma Sigma es efs ts, 
        type_exprs Gamma Sigma es efs ts ->
        forall bge vm m vm' m' es' efs' ts', 
        is_stateful_exprs es = true /\ is_stateful_effect efs = true ->
        ssem_exprs bge vm m es m' vm' es' ->
        type_exprs Gamma Sigma es' efs' ts' ->
        is_stateful_effect efs') /\
        (forall Gamma Sigma e ef t, 
        type_expr Gamma Sigma e ef t ->
        forall bge vm m vm' m' e' ef' t', 
        is_stateful_expr e = true /\ is_stateful_effect ef = true ->
        ssem_expr bge vm m e m' vm' e' ->
        type_expr Gamma Sigma e' ef' t' ->
        is_stateful_effect ef').
+ move=> [] ih ih'. admit.
apply type_expr_indP=> //=.
Admitted.

(***** With respect to big step semantics *****)

(* Complete me *) (* Medium level *)
Lemma cval_bval_type_eq : forall v ct v' bt g g' i,
Values.Val.has_type v (typ_of_type ct) ->
transC_val_bplvalue v = Errors.OK v' ->
transBeePL_type bt g = SimplExpr.Res ct g' i ->
wtypeof_value v' (wtype_of_type bt). 
Proof.
Admitted.
 
(* Complete me *) (* Medium level *)
Lemma wderef_addr_val_ty : forall bge ty m l ofs bf v,
deref_addr bge ty m l ofs bf v ->
wtypeof_value v (wtype_of_type ty).
Proof.
move=> bge ty m l ofs bf v hd. inversion hd; subst.
+ rewrite /Mem.loadv /= in H2.
  have hvt := Mem.load_type m (transl_bchunk_cchunk chunk) l 
              (Ptrofs.unsigned ofs) v0 H1.
  have hwt := wbty_chunk_rel ty chunk H.
  rewrite /wtypeof_value /= hwt /wtypeof_chunk /=. 
  by case: chunk H H1 hvt hwt=> //=; case: v hd H2=> //=; case: v0=> //=.
+ admit. (* complete me for the case of volatile load *)
case: ty hd H=> //= p. case: p=> //= i s a.
by case: i=> //=;case: s=> //=.
Admitted.

(* Complete Me *)
Lemma uop_type_preserve : forall uop v ct m v',
Cop.sem_unary_operation uop v ct m = Some v' ->
Values.Val.has_type v' (typ_of_type ct).
Proof.
Admitted.

(* Complete Me *)
Lemma eq_uop_types : forall uop t g g' i v ct m v' v'',
transBeePL_type t g = SimplExpr.Res ct g' i ->
Cop.sem_unary_operation uop v ct m = Some v' ->
Values.Val.has_type v' (typ_of_type ct) ->
transC_val_bplvalue v' = Errors.OK v'' -> 
wtypeof_value v'' (wtype_of_type t).
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
wtypeof_value v' (wtype_of_type t1) /\ wtypeof_value v' (wtype_of_type t2).
Proof.
Admitted.

Lemma type_to_wtype : forall v t,
typeof_value v t ->
wtypeof_value v (wtype_of_type t).
Proof.
move=> v t. case: t=> //=.
+ move=> p. case: p=> //=.
  + move=> i s a. by case: v=> //=.
  move=> s a. by case: v=> //=.
+ move=> h b a. by case: v=> //=.
move=> es e t. by case: v=> //=.
Qed.
  
(*** Proving theorems related to type system for big step semantics of BeePL *)
Lemma subject_reduction_bsem_expr_exprs: 
(forall Gamma Sigma es efs ts bge vm m vm' m' vs, type_exprs Gamma Sigma es efs ts ->
                                                  bsem_exprs bge vm m es m' vm' vs ->
                                                  wtypeof_values vs (wtypes_of_types ts)) /\
(forall Gamma Sigma e ef t bge vm m vm' m' v, type_expr Gamma Sigma e ef t ->
                                              bsem_expr bge vm m e m' vm' v ->
                                              wtypeof_value v (wtype_of_type t)).
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall bge vm m vm' m' vs, bsem_exprs bge vm m es m' vm' vs ->
                                                                 wtypeof_values vs (wtypes_of_types ts)) /\
       (forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                                   forall bge vm m vm' m' v, bsem_expr bge vm m e m' vm' v ->
                                                             wtypeof_value v (wtype_of_type t)).
+ move=> [] ih ih'. split=> //=.
  + move=> Gamma Sigma es efs ts bge vm m m' vm' vs hts hes. 
    by move: (ih Gamma Sigma es efs ts hts bge vm m m' vm' vs hes).
  move=> Gamma Sigma e ef t bge vm m m' vm' v ht he.
  by move: (ih' Gamma Sigma e ef t ht bge vm m m' vm' v he).
apply type_expr_indP => //=.
(* val unit *)
+ move=> Gamma Sigma ef bge vm m vm' m' v he. by inversion he; subst.
(* 
(* val *)
+ move=> Gamma Sigma v ef t bge vm m vm' m' v' he. inversion he; subst.
  case: t he H6=> //=.
  + move=> p. case: p=> //=.
    + move=> he hw. case: v' he hw=> //=.
      + move=> i he hw. by inversion hw.
      + move=> i he hw. by inversion hw.
      move=> l ofs he hw. by inversion hw.
    + move=> i s a he hw. case: v' he hw=> //=.
      + move=> i' he hw. by inversion hw.
      move=> l ofs he hw. by inversion hw.
    + move=> s a he hw. case: v' he hw=> //=.
      move=> i he hw. by inversion hw.
    move=> i h a he hw. case: v' he hw=> //= i' he hw. by inversion hw.
  move=> es e t he hw. case: v' he hw=> //= i he hw. by inversion hw.
(* var *)
+ move=> Gamma Sigma x t ht bge vm m vm' m' v hv. inversion hv; subst.
  (* local *)
  + have := wderef_addr_val_ty bge (Ptype t) m' l ofs Full v H7.
    by case: t ht hv H3 H7=> //=.
  (* global *)
  + have := wderef_addr_val_ty bge (Ptype t) m' l ofs Full v H8.
    by case: t ht hv H8=> //=.
(* const int *)
+ move=> Gamma Sigma t sz s i a hteq bge vm m vm' m' v hv. by inversion hv; subst.
(* const long *)
+ move=> Gamma Sigma t s i a hteq bge vm m vm' m' v hv. by inversion hv; subst.
(* const unit *)
+ move=> Gamma Sigma t hteq bge vm m vm' m' v hv. by inversion hv; subst.
(* app *)
+ move=> Gamma Sigma e es rt ef ef' ts ef'' hie hies bge vm m vm' m' v hv.
  inversion hv; subst. move: (hie bge vm m vm2 m2 (Vloc l Ptrofs.zero) H2)=> het.
  move: (hies bge vm3 m3 vm4 m4 vs H7)=> hest. inversion H4; subst.
  by have := type_to_wtype v (get_rt_fundef (Internal fd)) H16.
(* ref *)
+ move=> Gamma Sigma e ef h bt a hi bge vm m vm' m' v hv. by inversion hv; subst.
(* deref *)
+ move=> Gamma Sigma e ef h bt a hi bge vm m vm' m' v hv. inversion hv; subst.
  move: (hi bge vm m vm' m' (Vloc l ofs) H3)=> hlt. 
  have hvt := wderef_addr_val_ty bge (typeof_expr e) m l ofs bf v H7.
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
+ move=> Gamma Sigma l h t a ofs t' ht hteq bge vm m vm' m' v he.
  rewrite hteq /=. by inversion he; subst.
(* nil *)
+ move=> Gamma Sigma bge vm m vm' m' vs hv. by inversion hv; subst.
(* cons *)
move=> Gamma Sigma e es t ef ts efs hi his bge vm m vm' m' vs hv.
inversion hv; subst. move: (hi bge vm m vm'0 m'0 v H3) => hvt.
move: (his bge vm'0 m'0 vm' m' vs0 H7)=> hvts. by rewrite /typeof_values.*)
Admitted.  


(*Section Subject_Reduction.

Variable (bge : genv).
Variable (benv : vmap).

(* Subject reduction : Big step semantics *) 
Lemma subject_lredcution : forall m e l ofs Gamma Sigma ef t h a,
bsem_expr_slv bge benv m e l ofs ->
type_expr Gamma Sigma e ef (Reftype h t a) ->
PTree.get l.(lname) Sigma = Some (Reftype h t a).
Proof.
move=> m e l ofs Gamma Sigma ef t h a hl.
induction hl=> //= ht; subst; inversion ht; subst; symmetry.
by case: H7=> h1 h2 h3; subst.
Qed.

Lemma subject_rreduction : forall m e v Gamma Sigma ef t, 
bsem_expr_srv bge benv m e v ->
type_expr Gamma Sigma e ef t ->
wtypeof_value v (wtype_of_type t).
Proof.
move=> m e v Gamma Sigma ef t hr ht. move: Gamma Sigma ef t ht.
induction hr=> //=. 
(* Val *)
+ move=> Gamma Sigma ef t' ht. 
  inversion ht; subst; rewrite /wtypeof_value /= /wtype_of_type.
  case: t' ht H=> //=.  
  + move=> p. case: p=> //=.
    + case: v=> //=.
      + move=> i ht hw. by inversion hw.
      + move=> i ht hw. by inversion hw.
      move=> l ofs ht hw. by inversion hw.
    + move=> i s a ht hw. case: v ht hw=> //=.
      + move=> l ht hw. by inversion hw.
      move=> l ofs ht hw. by inversion hw. 
    + move=> s a ht hw. case: v ht hw=> //=.
      move=> l ht hw. by inversion hw.
    move=> h b a. case: v=> //= i ht hw. by inversion hw. 
  move=> h b a ht hw. case: v ht hw=> //= i ht hw. by inversion hw. 
(* Deref *)
+ move=> Gamma Sigma ef t' ht.
  inversion ht; subst. rewrite H7.
  have := subject_lredcution hm e l ofs Gamma Sigma ef0 (Bprim bt) h a H H9=> hlt. 
  by have := wderef_addr_val_ty bge (typeof_expr e) hm l.(lname) ofs l.(lbitfield) v H0.
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

End Subject_Reduction.

(* Subject reduction : Small step semantics *)
(* A well-typed expression remains well-typed under top-level lreduction *)
(* Add invariant for well formedness for the store *)
Lemma slreduction : forall Gamma Sigma genv ef t vm e m e' m', 
type_expr Gamma Sigma e ef t ->
lreduction genv vm e m e' m' ->
type_expr Gamma Sigma e' ef t.
Proof.
(*move=> Gamma Sigma genv ef t vm e m e' m' ht he.
induction he=> //=.
+ inversion ht; subst. rewrite H0. apply ty_addr with h t0 a.
  rewrite /=. Print lreduction.
+ inversion ht; subst. rewrite H0. by apply ty_addr with h t0 a.
Qed.*) Admitted.
*)

    
    
