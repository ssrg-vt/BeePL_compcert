Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers Maps Globalenvs Coqlib Memory. 
Require Import Csyntax Csem SimplExpr Ctypes Memtype BeePL_values.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL BeePL_auxlemmas BeePL_sem Errors BeePL_typesystem.
From mathcomp Require Import all_ssreflect.

(** Safety conditions **)

 Definition is_not_zero_expr (e : expr) (bge : genv) (vm : vmap) (m : Memory.mem) :=
forall e v t m' vm', 
ssem_expr bge vm m e m' vm' (Val v t) -> 
v <> (Vint (Int.repr 0)) /\ v <> (Vint (Int.repr 0)).

(* -128/-1 = 128 which will lead to overflow in div and mod *)
Definition no_overflow_div (e1 : expr) (e2 : expr) (bge : genv) (vm : vmap) (m : Memory.mem) :=
forall e1 vm m v1 t m1 vm1 v2 m2 vm2,
ssem_expr bge vm m e1 m1 vm1 (Val v1 t) ->
ssem_expr bge vm m e2 m2 vm2 (Val v2 t) ->
is_primtype_notunit t ->
match t with 
| Ptype (Tint sz s a) => match s with 
                         | Signed => match v1, v2 with 
                                     | Vint i1, Vint i2 => Int.eq i1 (Int.repr Int.min_signed) && 
                                                           Int.eq i2 Int.mone
                                     | _, _ => False
                                     end
                         | Unsigned => True 
                         end
| Ptype (Tlong s a) => match s with 
                       | Signed => match v1, v2 with 
                                     | Vint64 i1, Vint64 i2 => Int64.eq i1 (Int64.repr Int64.min_signed) && 
                                                               Int64.eq i2 Int64.mone
                                     | _, _ => False
                                     end
                       | Unsigned => True
                       end
| _ => False
end.

Definition no_overflow_shift (e1 : expr) (e2 : expr) (bge : genv) (vm : vmap) (m : Memory.mem) :=
forall e1 vm m v1 t m1 vm1 v2 m2 vm2,
ssem_expr bge vm m e1 m1 vm1 (Val v1 t) ->
ssem_expr bge vm m e2 m2 vm2 (Val v2 t) ->
is_primtype_notunit t ->
match t with 
| Ptype (Tint sz s a) => match s with 
                         | Signed => match v1, v2 with 
                                     | Vint i1, Vint i2 => not (Int.ltu i2 Int.iwordsize)
                                     | _, _ => False
                                     end
                         | Unsigned => True 
                         end
| Ptype (Tlong s a) => match s with 
                       | Signed => match v1, v2 with 
                                     | Vint64 i1, Vint64 i2 => not (Int64.ltu i2 Int64.iwordsize)
                                     | _, _ => False
                                     end
                       | Unsigned => True
                       end
| _ => False
end.

(* Mem.valid_pointer ensures that the location l with ofset ofs is nonempty in memory m *)
Definition is_valid_pointer (bge : genv) (vm : vmap) (m : Memory.mem) (e: expr) :=
forall m' vm' l ofs t, ssem_expr bge vm m e m' vm' (Val (Vloc l ofs) t) -> 
Mem.valid_pointer m l (Ptrofs.unsigned ofs).

(* A deref of a location should always produce a value *)
Definition valid_deref (Sigma : store_context) (bge : genv) (vm : vmap) (m : Memory.mem) (e : expr) := 
if is_pointer e 
then forall l ofs t h a, PTree.get l Sigma = Some (Reftype h (Bprim t) a) /\
                         is_valid_pointer bge vm m e /\ 
                         exists v, is_vloc v = false /\ deref_addr bge (Ptype t) m l ofs Full v 
else false.

(* A value of the same type can be always assigned to a valid location in memory *)
Definition valid_assgn (Sigma : store_context) (bge : genv) (vm : vmap) (m : Memory.mem) (e1 e2 : expr) :=
if is_pointer e1 && is_value e2 
then forall l ofs h t a v, PTree.get l Sigma = Some (Reftype h (Bprim t) a) /\
                           is_valid_pointer bge vm m e1 /\ 
                           exists bf m', is_vloc v = false /\ assign_addr bge (Ptype t) m l ofs bf v m' v
else false.

(* checks that a variable is defined in the memory *)
Definition is_defined_var (x : positive) (t : type) (vm : vmap) (m : Memory.mem) (Sigma : store_context) (bge : genv) : Prop :=
match vm ! x with 
| Some (l', t') => t = t' /\ PTree.get x Sigma = Some t /\ exists ofs v, is_vloc v = false /\ deref_addr bge t m l' ofs Full v
| None => PTree.get x Sigma = Some t  /\ exists l' ofs v, Genv.find_symbol bge x = Some l' /\ is_vloc v = false 
                                         /\ deref_addr bge t m l' ofs Full v
end.

Inductive safe_cond : Type :=
| Defined_var : positive -> type -> safe_cond
| Not_zero : expr -> expr -> safe_cond
| No_overflowd : expr -> expr -> safe_cond
| No_overflows : expr -> expr -> safe_cond
| Valid_pointer : expr -> safe_cond
| Valid_deref : expr -> safe_cond
| Valid_assgn : expr -> expr -> safe_cond.

(* checks the safety condition for operations: except division, modulo and shift, 
   rest of the operations are safe without any explicit condition *)  
Definition gen_safe_cond_bop (op : Cop.binary_operation) (e1 e2 : expr) : seq safe_cond :=
match op with 
| Cop.Odiv => [:: Not_zero e1 e2; No_overflowd e1 e2]
| Cop.Omod => [:: Not_zero e1 e2; No_overflowd e1 e2]
| Cop.Oshl => [:: No_overflows e1 e2]
| Cop.Oshr => [:: No_overflows e1 e2]
| _ => [::]
end.

(* Interpretation of safety condition *)
Definition interp_safe_cond_bop (op : Cop.binary_operation) (e1 e2: expr) (bge : genv) 
                                (vm : vmap) (m : Memory.mem) (sc : seq safe_cond) :=
match sc with 
| nil => True 
| [:: sc1] => no_overflow_shift e1 e2 bge vm m 
| [:: sc1; sc2] => is_not_zero_expr e2 bge vm m /\ no_overflow_div e1 e2 bge vm m
| _ => False
end.

Fixpoint gen_safe_cond_expr (e : expr) : seq safe_cond :=
match e with 
| Val v t => [::]
| Var x t => [:: Defined_var x t]
| Const c t => [::]
| App e es t => gen_safe_cond_expr e ++ flatten (map gen_safe_cond_expr es) 
| Prim b es t => match b with 
                 | Ref => [::] (* fix me *)
                 | Deref => match es with 
                            | [:: e1] => gen_safe_cond_expr e1 ++
                                         [:: Valid_deref e1] 
                            | _ => [::]
                            end 
                 | Massgn => match es with 
                             | [:: e1; e2] => gen_safe_cond_expr e1 ++
                                              gen_safe_cond_expr e2 ++
                                              [:: Valid_assgn e1 e2]
                             | _ => [::] 
                             end
                 | Uop op => match es with 
                             | [:: e] => gen_safe_cond_expr e
                             | _ => [::]
                             end
                 | Bop op => match es with 
                             | [:: e1; e2] => gen_safe_cond_expr e1 ++
                                              gen_safe_cond_expr e2 ++
                                              gen_safe_cond_bop op e1 e2
                             | _ => [::]
                             end
                 | _ => [::] (* fix me for run *)
                 end
| Bind x xt e1 e2 t => gen_safe_cond_expr e1 ++ gen_safe_cond_expr e2
| Cond e1 e2 e3 t => gen_safe_cond_expr e1 ++ gen_safe_cond_expr e2 ++ gen_safe_cond_expr e3
| Unit t => [::]
| Addr l ofs t => [::]
| Eapp ef ts es t => flatten (map gen_safe_cond_expr es)
| Hexpr h e t => [::] (* fix me *)
end.

(* Defines the interpretation of safety condition *) 
Definition interp_safe_cond (sc : safe_cond) (Sigma : store_context) (bge : genv) (vm : vmap) (m : Memory.mem) :=
match sc with 
| Defined_var x t => is_defined_var x t vm m Sigma bge
| Not_zero e1 e2 => is_not_zero_expr e2 bge vm m
| No_overflowd e1 e2 => no_overflow_div e1 e2 bge vm m
| No_overflows e1 e2 => no_overflow_shift e1 e2 bge vm m
| Valid_pointer e => is_valid_pointer bge vm m e
| Valid_deref e => valid_deref Sigma bge vm m e
| Valid_assgn e1 e2 => valid_assgn Sigma bge vm m e1 e2
end.

Fixpoint interp_safe_conds (sc : seq safe_cond) (Sigma : store_context) (bge : genv) (vm : vmap) (m : Memory.mem) :=
match sc with 
| nil => True
| sc1 :: sc2 => interp_safe_cond sc1 Sigma bge vm m /\ interp_safe_conds sc2 Sigma bge vm m
end. 


(* Proofs related to safety condition generator *)
(* Complete Me : Easy *)
Lemma interp_safe_conds_concat : forall sc1 sc2 Sigma bge vm m,
interp_safe_conds (sc1 ++ sc2) Sigma bge vm m ->
interp_safe_conds sc1 Sigma bge vm m /\ interp_safe_conds sc2 Sigma bge vm m.
Proof.
Admitted.

(* A well-typed uop always has a semantics that leads to a value. *)
Lemma well_typed_safe_uop : forall Gamma Sigma bge vm v ef t uop m ct g i,
type_expr Gamma Sigma (Prim (Uop uop) ((Val v t) :: nil) t) ef t ->
transBeePL_type t g = Res ct g i ->
interp_safe_conds (gen_safe_cond_expr (Val v t)) Sigma bge vm m ->
exists v', Cop.sem_unary_operation uop (transBeePL_value_cvalue v) ct m = Some v'.
Proof.
(*move=> Gamma Sigma bge vm v ef t uop m ct g i htv. case: v htv=> //=. 
(* unit *)
+ move=> htv. inversion htv; subst. inversion H8; subst.
  rewrite /transBeePL_type /=. move=> [] hct hw; subst.
  by case: uop htv=> //=.
(* int *)
+ move=> hvt _. inversion hvt; subst. inversion H8; subst. 
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
Qed.*)
Admitted.


(* Complete Me : Medium *) (* Hint : Follow similar proof style like well_typed_uop 
(* A well-typed bop always has a semantics that leads to a value. *)
Lemma well_typed_safe_bop : forall Gamma Sigma bge vm bcmp v1 v2 ef t bop m ct g i,
type_expr Gamma Sigma (Prim (Bop bop) (Val v1 t:: Val v2 t :: nil) t) ef t ->
transBeePL_type t g = Res ct g i ->
interp_safe_conds (gen_safe_cond_expr (Prim (Bop bop) (Val v1 t:: Val v2 t :: nil) t)) Sigma bge vm m ->
exists v', Cop.sem_binary_operation bcmp bop (transBeePL_value_cvalue v1) ct 
                                             (transBeePL_value_cvalue v2) ct m = Some v'.
Proof.
Admitted.*)

(* Complete Me : Medium 
Lemma trans_value_bop_success : forall Gamma Sigma bge bcmp vm bop v1 v2 ef t ct g i m v', 
type_expr Gamma Sigma (Prim (Bop bop) (Val v1 t:: Val v2 t :: nil) t) ef t ->
transBeePL_type t g = Res ct g i ->
interp_safe_conds (gen_safe_cond_expr (Prim (Bop bop) (Val v1 t:: Val v2 t :: nil) t)) Sigma bge vm m ->
Cop.sem_binary_operation bcmp bop (transBeePL_value_cvalue v1) ct 
                                  (transBeePL_value_cvalue v2) ct m = Some v' ->
exists v'', transC_val_bplvalue v' = OK v''.
Proof.
Admitted.*)
