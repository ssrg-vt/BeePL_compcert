Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Globalenvs Coqlib Memory. 
Require Import Csyntax Csem SimplExpr Ctypes Memtype.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL BeePL_auxlemmas BeePL_sem Errors.
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
                                         exists v, deref_addr bge (Ptype t) m l ofs Full v 
else false.

(* A value of the same type can be always assigned to a valid location in memory *)
Definition valid_assgn (Sigma : store_context) (bge : genv) (vm : vmap) (m : Memory.mem) (e1 e2 : expr) :=
if is_pointer e1 && is_value e2 
then forall l ofs h t a v, PTree.get l Sigma = Some (Reftype h (Bprim t) a) /\
                           is_valid_pointer bge vm m e1 /\ 
                           exists bf m', assign_addr bge (Ptype t) m l ofs bf v m' v
else false.

(* checks that a variable is defined in the memory *)
Definition is_defined_var (x : positive) (t : type) (vm : vmap) (m : Memory.mem) (Sigma : store_context) (bge : genv) : Prop :=
match vm ! x with 
| Some (l', t') => t = t' /\ PTree.get x Sigma = Some t /\ exists ofs v, deref_addr bge t m l' ofs Full v
| None => PTree.get x Sigma = Some t  /\ exists l' ofs v, Genv.find_symbol bge x = Some l' /\ deref_addr bge t m l' ofs Full v
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

(**** Well formedness ****)
(** Well-Typed Store **)
(* A store st is well-typed with respect to a store typing context Sigma if the
   term at each location l in vm has the type at location l in store typing context
   and there exists a value in the memory at that location. *)
(* It is more evolved due to two maps used in CompCert for retrieving data from the memory *)
(* Since we only allow pointers through references, it is safe to say that if there exists a 
   location in memory then it is also safe to deref that location *)
(* Mem.valid_pointer ensures that the location l with ofset ofs is nonempty in memory m *)
(*Definition store_well_typed (Sigma : store_context) (bge : genv) (vm : vmap) (m : Memory.mem) :=
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
                                     Mem.valid_pointer m l (Ptrofs.unsigned ofs)).*)
