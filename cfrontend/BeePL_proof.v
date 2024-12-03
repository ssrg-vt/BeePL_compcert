Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep SimplExpr.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Csyntax Clight Globalenvs BeePL_Csyntax SimplExpr.
Require Import compcert.common.Errors Initializersproof Cstrategy BeePL_auxlemmas.

From mathcomp Require Import all_ssreflect. 

(***** Correctness proof for the Clight generation from BeePL using 
       composition of BeePL and CompCert compiler *****)

(***** Specification for types *****) 
Inductive rel_type : BeeTypes.type -> Ctypes.type -> Prop :=
| rel_tunit : rel_type Tunit (Ctypes.Tvoid)
| rel_tint : forall sz s a, 
             rel_type (Tint sz s a) (Ctypes.Tint sz s a)
| rel_tlong : forall s a, 
              rel_type (Tlong s a) (Ctypes.Tlong s a)
| rel_reftype : forall h bt ct a, 
                rel_type bt ct ->
                rel_type (Reftype h bt a) (Tpointer ct a)
| rel_ftype : forall ts ef t cts ct,
              rel_types ts cts ->
              rel_type t ct -> 
              length ts = length (typelist_list_type cts) ->
              rel_type (Ftype ts ef t) (Tfunction cts ct 
                                        {| cc_vararg := Some (Z.of_nat(length(ts))); cc_unproto := false; cc_structret := false |}) 
with rel_types : list BeeTypes.type -> Ctypes.typelist -> Prop :=
| rel_tnil : rel_types nil Tnil
| rel_tcons : forall bt bts ct cts,
              rel_type bt ct ->
              rel_types bts cts ->
              rel_types (bt :: bts) (Tcons ct cts).

Scheme rel_type_ind2 := Minimality for rel_type Sort Prop
  with rel_typelist_ind2 := Minimality for rel_types Sort Prop.
Combined Scheme rel_type_typelist_ind from rel_type_ind2, rel_typelist_ind2.

(*Scheme rel_beety_ind2 := Minimality for BeeTypes.type Sort Prop
  with rel_beetys_ind2 := Minimality for (list BeeTypes.type) Sort Prop.
Combined Scheme rel_type_typelist_ind from rel_type_ind2, rel_typelist_ind2.*)

(***** Proof for correctness of type transformation *****)
Fixpoint type_translated bt: 
(forall ct, 
transBeePL_type bt = OK ct ->
rel_type bt ct) /\ (forall bts cts, 
transBeePL_types transBeePL_type bts = OK cts ->
rel_types bts cts).
Proof.
Admitted.

(***** Translation proof for expr to expr *****)
Fixpoint expr_no_assgn_func (e : BeePL.expr) : Prop :=
match e with 
| Var vi => True 
| Const c t => True 
| App o e es t => False
| Prim b es t => match b with 
                 | Ref => match es with 
                          | [:: e1] => expr_no_assgn_func e1
                          | _ => False 
                          end 
                 | Deref => match es with 
                            | [:: e1] => expr_no_assgn_func e1
                            | _ => False
                            end
                 | Massgn => false 
                 | Uop o => match es with 
                            | [:: e1] => expr_no_assgn_func e1
                            | _ => False 
                            end
                 | Bop o => match es with 
                            | [:: e1; e2] => expr_no_assgn_func e1 /\ 
                                             expr_no_assgn_func e2
                            | _ => False 
                          end
                 | Run h => false (* Fix me *)
                 end 
| Bind x t e e' t' => False
| Cond e1 e2 e3 t => expr_no_assgn_func e1 /\
                     expr_no_assgn_func e2 /\ 
                     expr_no_assgn_func e3
| Addr l => True 
| Hexpr h e t => False (* Fix me *)
end.

Fixpoint is_rval_expr (e : BeePL.expr) : Prop :=
match e with 
| Var vi => False 
| Const c t => True
| App o e es t => True  
| Prim b es t => match b with 
                 | Ref => True 
                 | Deref => True 
                 | Massgn => True 
                 | Uop o => True 
                 | Bop o => True
                 | Run h => False (* Fix me *)
                end
| Bind x t e e' t' => True
| Cond e1 e2 e3 t => True
| Addr l => False
| Hexpr h e t => False (* Fix me *)
end.

Fixpoint is_lval_expr (e : BeePL.expr) : Prop :=
match e with 
| Var vi => True 
| Const c t => False
| App o e es t => False 
| Prim b es t => match b with 
                 | Ref => False 
                 | Deref => True 
                 | Massgn => False 
                 | Uop o => False 
                 | Bop o => False
                 | Run h => False (* Fix me *)
                end
| Bind x t e e' t' => False
| Cond e1 e2 e3 t => False
| Addr l => True 
| Hexpr h e t => False (* Fix me *)
end.

(***** Expressions *****) 
(* Fix me: Define specification 
           Relate value v with something 
           Should we prove it for existential? *)
(*Lemma transl_expr_lvalue : forall genv e ce st st' v cge cenv m,
is_lval_expr e ->
sem_expr genv st e st' v ->
transBeePL_expr_expr e = OK ce -> 
exists b pofs bf, eval_simple_lvalue cge cenv m ce b pofs bf.
Proof.
move=> genv [].
(* var *)
+ move=> vi ce st st' v cge cenv m hl he /= h. 
  monadInv h. inversion he; subst. exists (vname vi).
  exists Ptrofs.zero. exists Full. apply esl_var_local.
Admitted.*)
