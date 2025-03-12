Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Globalenvs Coqlib Memory. 
Require Import Csyntax Csem SimplExpr Ctypes Memtype.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL BeePL_auxlemmas Errors.
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
| ty_cond : forall Gamma Sigma e1 e2 e3 tb t ef1 ef2 ef3 ef1' ef2' ef3', 
            type_expr Gamma Sigma e1 ef1 tb ->
            sub_effect ef1 ef1' ->
            type_bool tb ->
            type_expr Gamma Sigma e2 ef2 t ->
            sub_effect ef2 ef2' = true ->
            type_expr Gamma Sigma e3 ef3 t ->
            sub_effect ef3 ef3' = true ->
            type_expr Gamma Sigma (Cond e1 e2 e3 t) (ef1' ++ ef2' ++ ef3') t
| ty_unit : forall Gamma Sigma,
            type_expr Gamma Sigma (Unit (Ptype Tunit)) empty_effect (Ptype Tunit)
| ty_addr : forall Gamma Sigma l ofs h t a,
            PTree.get l.(lname) Sigma = Some (Reftype h t a) ->
            (*t' = (Reftype h t a) ->*)
            type_expr Gamma Sigma (Addr l ofs (Reftype h t a)) empty_effect (Reftype h t a) 
(* return type, arg types, and effect must agree with the signature *)
| ty_ext : forall Gamma Sigma exf ts es ef rt,
           rt = get_rt_eapp exf ->
           ts = get_at_eapp exf ->
           type_exprs Gamma Sigma es ef ts ->
           type_expr Gamma Sigma (Eapp exf ts es rt) ((get_ef_eapp exf) ++ ef) rt
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

(* Complete Me: Easy *)
Lemma sub_effect_refl : forall ef, 
sub_effect ef ef = true.
Proof.
Admitted.

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
Context (Htcond : forall Gamma Sigma e1 e2 e3 ef1 ef2 ef3 tb t ef1' ef2' ef3', 
                  Pt Gamma Sigma e1 ef1 tb ->
                  sub_effect ef1 ef1' ->
                  type_bool tb ->
                  Pt Gamma Sigma e2 ef2 t ->
                  sub_effect ef2 ef2' = true ->
                  Pt Gamma Sigma e3 ef3 t ->
                  sub_effect ef3 ef3' = true ->
                  Pt Gamma Sigma (Cond e1 e2 e3 t) (ef1' ++ ef2' ++ ef3') t).
Context (Htunit : forall Gamma Sigma, 
                  Pt Gamma Sigma (Unit (Ptype Tunit)) empty_effect (Ptype Tunit)).
Context (Htloc : forall Gamma Sigma l ofs h t a, 
                 PTree.get l.(lname) Sigma = Some (Reftype h t a)  ->
                 (*t' = (Reftype h t a) ->*)
                 Pt Gamma Sigma (Addr l ofs (Reftype h t a)) empty_effect (Reftype h t a)). 
Context (Htext :  forall Gamma Sigma exf ts es ef rt,
                  rt = get_rt_eapp exf ->
                  ts = get_at_eapp exf ->
                  Pts Gamma Sigma es ef ts ->
                  Pt Gamma Sigma (Eapp exf ts es rt) ((get_ef_eapp exf) ++ ef) rt).
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
+ move=> Gamma Sigma e1 e2 e3 tb t ef1 ef2 ef3 ef1' ef2' ef3' 
  hte1 ht1 hs1 htb hte2 ht2 hs2 hte3 ht3 hs3. 
  apply Htcond with ef1 ef2 ef3 tb; auto. 
(* Ext *)
+ move=> Gamma Sigma exf ts es ef rt hrt hts tes hts'.
  by apply Htext.
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
                                        ts = ts') /\
(forall Gamma Sigma e ef t ef' t', type_expr Gamma Sigma e ef t ->
                                   type_expr Gamma Sigma e ef' t' ->
                                   t = t').
Proof.
suff : (forall Gamma Sigma es efs ts, type_exprs Gamma Sigma es efs ts ->
                                      forall efs' ts', type_exprs Gamma Sigma es efs' ts' ->
                                      ts = ts') /\
       (forall Gamma Sigma e ef t, type_expr Gamma Sigma e ef t ->
                                   forall ef' t', type_expr Gamma Sigma e ef' t' ->
                                   t = t').
+ move=> [] ih ih'. split=> //=.
  + move=> Gamma Sigma es efs ts efs' ts' hes hes'. 
    by move: (ih Gamma Sigma es efs ts hes efs' ts' hes').
  move=> Gamma Sigma e ef t ef' t' he he'.
  by move: (ih' Gamma Sigma e ef t he ef' t' he').
apply type_expr_indP => //=.
+ by move=> Gamma Sigma ef ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma ef i sz s a ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma ef i s a ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma ef l ofs h t a hs ef' t' ht; inversion ht; subst.
+ move=> Gamma Sigma x t ht ef' t' het; subst. by inversion het; subst.
+ move=> Gamma Sigma t sz s i a ht ef' t' ht'; subst. by inversion ht'; subst.
+ move=> Gamma Sigma t s i a ht ef' t' ht'; subst. by inversion ht'; subst.
+ move=> Gamma Sigma t ht ef' t' ht'; subst. by inversion ht'; subst.
+ move=> Gamma Sigma e es rt ef efs ts efs' ih ih' ef' t' ht; subst.
  by inversion ht; subst. 
+ by move=> Gamma Sigma e ef h bt a ih ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma e ef h bt a ih ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma e1 e2 ef1 ef2 h bt a ih ih' ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma op e ef t hf hf' ih ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma op e1 e2 ef t hf hf' ih ih' ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma x t e e' t' ef ef' ih ih' ef'' t'' ht; inversion ht; subst.
+ move=> Gamma Sigma e1 e2 e3 ef1 ef2 ef3 tb t ef1' ef2' ef3' hin1 hs1 htb hin3
  hs2 ht2 hs3 ef' t' htc. by inversion htc; subst.
+ by move=> Gamma Sigma ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma l ofs h t a hl ef' t'' ht; inversion ht; subst.
+ by move=> Gamma Sigma exf ts es ef rt hrt hts hin ef' t' ht; inversion ht; subst.
+ by move=> Gamma Sigma efs' ts' ht; inversion ht; subst.
move=> Gamma Sigma e es t ef ts efs ih ih' efs' ts' ht; inversion ht; subst.
move: (ih ef0 t0 H3)=> h1; subst. by move: (ih' efs0 ts0 H6)=> h1; subst.
Qed.

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

(* Not provable due to C treating pointer as int in terms of 
   value stored in memory *)
Lemma wbty_chunk_rel : forall (ty: type) chunk,
access_mode ty = By_value (transl_bchunk_cchunk chunk) ->
(wtype_of_type ty) = (wtypeof_chunk chunk).
Proof.  
move=> ty chunk. case: chunk=> //=; case: ty=> //= p; case: p=> //=.
move=> i s a. case: i=> //=.
+ by case: s=> //=.
case: s=> //=.
Admitted.

(* Not provable due to C treating pointer as int in terms of 
   value stored in memory *)
Lemma cval_bval_type_chunk : forall v chunk v',
Values.Val.has_type v (type_of_chunk (transl_bchunk_cchunk chunk)) ->
transC_val_bplvalue v = Errors.OK v' ->
wtypeof_value v' (wtypeof_chunk chunk). 
Proof.
move=> v chunk v'. case: chunk=> //=; case: v=> //=; case: v'=> //=. 
Admitted.

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

