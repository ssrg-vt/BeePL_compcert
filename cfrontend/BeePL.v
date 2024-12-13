Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Globalenvs compcert.lib.Coqlib Ctypes.
Require Import BeePL_aux BeeTypes Axioms Memory Int Cop Memtype Errors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Inductive constant : Type :=
| ConsInt : int -> constant
| ConsLong : int64 -> constant
| ConsUnit : constant.

Record vinfo : Type := mkvar { vname : ident; vtype : BeeTypes.type }.
Record linfo : Type := mkloc { lname : ident; ltype : BeeTypes.type; lbitfield : bitfield }.

Inductive value : Type :=
| Vunit : value
| Vint : int -> value
| Vint64 : int64 -> value
| Vloc : positive -> ptrofs -> value.

(* Pointer will be stores in a 64 bit value or 32 bit value *) 
Definition default_attr (t : type) := {| attr_volatile := false;  
                                         attr_alignas := (attr_alignas (attr_of_type t)) |}.

Definition typeof_value (v : value ) (t : type) : Prop :=
let t := wtype_of_type t in 
match v with 
| Vunit => match t with 
           | Twunit => True 
           | _ => False 
           end
| Vint i => match t with 
            | Twint => True 
            | _ => False 
            end 
| Vint64 i => match t with 
              | Twlong => True 
              | _ => False 
              end 
| Vloc p ptrofs => match t with 
                   | Twlong => Archi.ptr64 = true
                   | Twint => Archi.ptr64 = false 
                   | _ => False
                   end                              
end.

Definition vals := list value.

Definition of_int (i : int) : value := Vint i.

Fixpoint typeof_values (vs : list value) (ts : list BeeTypes.type) : Prop :=
match vs, ts with 
| nil, nil => True
| v :: vs, t :: ts => typeof_value v t /\ typeof_values vs ts
| _, _ => False
end.

Fixpoint extract_types_vinfos (vs : list vinfo) : list BeeTypes.type :=
match vs with 
| nil => nil
| v :: vs => v.(vtype) :: extract_types_vinfos vs
end.

Fixpoint extract_types_linfos (vs : list linfo) : list BeeTypes.type :=
match vs with 
| nil => nil
| v :: vs => v.(ltype) :: extract_types_linfos vs
end.

Fixpoint extract_vars_vinfos (vs : list vinfo) : list ident :=
match vs with 
| nil => nil
| v :: vs => v.(vname) :: extract_vars_vinfos vs
end.

Fixpoint extract_locs_linfos (vs : list linfo) : list ident :=
match vs with 
| nil => nil
| v :: vs => v.(lname) :: extract_locs_linfos vs
end.

Fixpoint extract_list_rvtypes (l : list vinfo) : list (ident * BeeTypes.type) :=
match l with 
| nil => nil
| x :: xs => (x.(vname), x.(vtype)) :: extract_list_rvtypes xs
end.

Definition eq_vinfo (v1 : vinfo) (v2 : vinfo) : bool :=
if (v1.(vname) =? v2.(vname))%positive && (eq_type (vtype v1) (vtype v2)) then true else false.

Definition eq_linfo (v1 : linfo) (v2 : linfo) : bool :=
if (v1.(lname) =? v2.(lname))%positive && (eq_type v1.(ltype) v2.(ltype)) then true else false.

Inductive builtin : Type :=
| Ref : builtin              (* allocation : ref t e allocates e of type t 
                                and returns the fresh address *)
| Deref : builtin            (* dereference : deref t e returns the value of type t 
                                present at location e *)
| Massgn : builtin           (* assign value at a location l (l := e) 
                                assigns the evaluation of e to the reference cell l *)
| Uop : Cop.unary_operation -> builtin       (* unary operator *)
| Bop : Cop.binary_operation -> builtin       (* binary operator *)
| Run : mem -> builtin      (* eliminate heap effect : [r1-> v1, ..., ern->vn] e 
                                reduces to e captures the essence of state isolation 
                                and reduces to a value discarding the heap *).


(* The source language never exposes the heap binding construct hpφ.e directly to the user 
   but during evaluation the reductions on heap operations create heaps and use them. *)
Inductive expr : Type :=
| Val : value -> type -> expr                                      (* value *)
| Var : vinfo -> expr                                              (* variable *)
| Const : constant -> type -> expr                                 (* constant *)
| App : option ident -> expr -> list expr -> type -> expr          (* function application: option ident represents 
                                                                      return variable *)
| Prim : builtin -> list expr -> type -> expr                      (* primitive functions: arrow : 
                                                                      for now I want to treat them not like functions
                                                                      during the semantics of App, we always make sure that
                                                                      the fist "e" is evaluated to a location  *)
| Bind : ident -> type -> expr -> expr -> type -> expr             (* let binding: type of continuation *)
| Cond : expr -> expr -> expr -> type -> expr                      (* if e then e else e *) 
| Unit : type -> expr                                                      (* unit *)
(* not intended to be written by programmers:
   Only should play role in operational semantics *)
| Addr : linfo -> ptrofs -> expr                                   (* address *)
| Hexpr : mem -> expr -> type -> expr                              (* heap effect *).

Definition is_value (e : expr) : bool :=
match e with 
| Val v t => true 
| _ => false
end.
 
Definition typeof_expr (e : expr) : BeeTypes.type :=
match e with 
| Val v t => t
| Var x => x.(vtype)
| Const x t => t
| App x e ts t => t
| Prim b es t => t
| Bind x t e e' t' => t'
| Cond e e' e'' t => t
| Unit t => t
| Addr l p => l.(ltype) 
| Hexpr h e t => t
end.

Record function : Type := mkfunction { fn_return: type;
                                       fn_callconv: calling_convention;
                                       fn_args: list vinfo;
                                       fn_vars: list vinfo;
                                       fn_body: expr }.

Inductive fundef : Type :=
| Internal : function -> fundef
| External : fundef. (* Fix me: add later *)

Inductive init_data : Set :=
| Init_int8 : int -> init_data
| Init_int16 : int -> init_data
| Init_int32 : int -> init_data
| Init_int64 : int64 -> init_data.

Record globvar : Type := mkglobvar { gvar_info : type;
                                     gvar_init : list init_data;
                                     gvar_readonly : bool;
                                     gvar_volatile : bool }.

Inductive globdef : Type :=
| Gfun : fundef -> globdef
| Gvar : globvar -> globdef.


Record program : Type := mkprogam { prog_defs : list (ident * globdef);
                                    prog_public : list ident;
                                    prog_main : ident;
                                    prog_types : list composite_definition;
                                    prog_comp_env : composite_env;
                                    prog_comp_env_eq : build_composite_env prog_types = OK prog_comp_env }.

(* Global environments are a component of the dynamic semantics of
   BeePL language.  A global environment maps symbol names 
   (names of functions and of global variables)
   to the corresponding function declarations. *) 
Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }.

(************************** Operation Semantics **************************************)
(***** Virtual map *****) 

(** The local environment maps local variables to references/locations and types.
  The current value of the variable is stored in the associated memory
  location. *)
Definition vmap := PTree.t (positive * type). (* map variable -> location & type *)

Definition empty_vmap: vmap  := (PTree.empty (positive * type)).

Definition bool_to_int (b : bool) : int :=
match b with 
| true => (Int.repr 1)
| false => (Int.repr 0)
end.

(* Convets BeePL value to C value *) 
Definition transBeePL_value_cvalue (v : value) : Values.val :=
match v with 
| Vunit => Values.Vint (Int.repr 0) (* Fix me *)
| Vint i => Values.Vint i
| Vint64 i => Values.Vlong i 
| Vloc p ofs => Values.Vptr p ofs
end.

(* Converts C value to BeePL value *) 
(* we don't want to allow int i and then read i to get garbage value *) 
(* Reading uninitialized memory is not allowed in eBPF as it might leak sensitive information *)
(* A function stores secret data in stack and later it is not cleared and then other function 
   is called, the secret data from older function can be leaked *)
Definition transC_val_bplvalue (v : Values.val) : res value :=
match v with 
| Values.Vundef => Error (MSG "Undef values are not allowed" :: nil)
| Values.Vint i => OK (Vint i)
| Values.Vlong i => OK (Vint64 i)
| Values.Vptr b ofs => OK (Vloc b ofs)
| _ => Error (MSG "Float values are not allowed" :: nil)
end.

Definition not_undef_or_float (v : Values.val) : Prop :=
match v with 
| Values.Vundef => v <> Values.Vundef
| Values.Vfloat f => v <> Values.Vfloat f
| Values.Vsingle f => v <> Values.Vsingle f
| _ => True
end.


(* Operational Semantics *)

(* [deref_addr ty m addr ofs] computes the value of type [ty] residing in 
    memory [m] at address [addr], offset [ofs] and bitfield designation [bf]:
    if the access mode is by value then the value is returned by performing memory load 
    if the access mode is by reference then the pointer [Vloc addr ofs] is returned *)
(* Add rest like copy, bitfield, volatile, etc once we add arrays and structs *)
Inductive deref_addr (ty : type) (m : mem) (addr : Values.block) (ofs : ptrofs) : bitfield -> value -> Prop :=
| deref_addr_value : forall chunk v v',
  access_mode ty = By_value chunk ->
  Mem.loadv chunk m (transBeePL_value_cvalue (Vloc addr ofs)) = Some v ->
  transC_val_bplvalue v = OK v' ->
  deref_addr ty m addr ofs Full v'
| deref_addr_reference:
  access_mode ty = By_reference ->
  deref_addr ty m addr ofs Full (Vloc addr ofs).

(* [assign_addr ty m addr ofs v] returns the updated memory after storing the value v at address [addr] and offset 
   [ofs] *)
Inductive assign_addr (ty : type) (m : mem) (addr : Values.block) (ofs : ptrofs) : bitfield -> value -> mem -> value -> Prop :=
| assign_addr_value : forall v chunk m' v',
  access_mode ty = By_value chunk ->
  Mem.storev chunk m (transBeePL_value_cvalue (Vloc addr ofs)) v = Some m' ->
  transC_val_bplvalue v = OK v' ->
  assign_addr ty m addr ofs Full v' m' v'. 

(* Allocation of function local variables *)
(* [alloc_variables vm1 m1 vars vm2 m2] allocates one memory block for each variable
   declared in [vars], and associates the variable name with this block. 
   [vm1] and [m1] are the initial local environment and memory state.
   [e2] and [m2] are the final local environment and memory state *) 
Inductive alloc_variables : vmap -> mem -> list vinfo -> vmap -> mem -> Prop :=
| alloc_variables_nil : forall vm hm, 
                        alloc_variables vm hm nil vm hm
| alloc_variables_con : forall e m id ty vars m1 l1 m2 e2,
      Mem.alloc m 0 (sizeof_type ty) = (m1, l1) ->
      alloc_variables (PTree.set id (l1, ty) e) m1 vars e2 m2 ->
      alloc_variables e m ({| vname := id; vtype := ty |} :: vars) e2 m2.
                  

(** Initialization of local variables that are parameters to a function.
  [bind_parameters e m1 params args m2] stores the values [args]
  in the memory blocks corresponding to the variables [params].
  [m1] is the initial memory state and [m2] the final memory state. *)
Inductive bind_parameters (e: vmap): mem -> list vinfo -> list value -> mem -> Prop :=
| bind_parameters_nil: forall m,
                       bind_parameters e m nil nil m
| bind_parameters_cons: forall m id ty params v1 vl v1' b m1 m2,
                        PTree.get id e = Some(b, ty) ->
                        assign_addr ty m b Ptrofs.zero Full v1 m1 v1' ->
                        bind_parameters e m1 params vl m2 ->
                        bind_parameters e m ({| vname := id; vtype := ty|} :: params) (v1 :: vl) m2.

(* Substitution *)
Inductive subst : vmap -> mem -> ident -> value -> expr -> mem -> expr -> Prop :=
| var_subst1 : forall vm hm x v y l hm',
               (x =? y.(vname))%positive = true ->
               vm!(y.(vname)) = Some (l, y.(vtype)) ->
               assign_addr y.(vtype) hm l Ptrofs.zero Full v hm' v ->
               subst vm hm x v (Var y) hm' (Var y)
| var_subst2 : forall vm hm x v y,
               (x =? y.(vname))%positive = false -> 
               subst vm hm x v (Var y) hm (Var y)
| const_subst : forall vm hm x v c t,
                subst vm hm x v (Const c t) hm (Const c t)
| app_subst : forall vm hm r x v e es t e' hm' hm'' es',
              subst vm hm x v e hm' e' ->
              substs vm hm' x v es hm'' es' ->
              subst vm hm x v (App r e es t) hm'' (App r e' es' t)
| prim_subst : forall vm hm hm' x v b es es' t,
               substs vm hm x v es hm' es' ->
               subst vm hm x v (Prim b es t) hm' (Prim b es' t)
| bind_subst1 : forall vm hm x v y t e1 e2 t',
                (x =? y)%positive = true ->
                subst vm hm x v (Bind y t e1 e2 t') hm (Bind y t e1 e2 t')
| bind_subst2 : forall vm hm x v y t e1 e2 t' e2' hm',
                (x =? y)%positive = false ->
                subst vm hm x v e2 hm' e2' ->
                subst vm hm x v (Bind y t e1 e2 t') hm (Bind y t e1 e2' t')
| cond_subst : forall vm hm x v e1 hm' e1' e2 hm'' e2' e3 hm''' e3' t,
               subst vm hm x v e1 hm' e1' ->
               subst vm hm' x v e2 hm'' e2' ->
               subst vm hm'' x v e3 hm''' e3' ->
               subst vm hm x v (Cond e1 e2 e3 t) hm''' (Cond e1' e2' e3' t)
| unit_subst : forall vm hm x v,
               subst vm hm x v (Unit (Ptype Tunit)) hm (Unit (Ptype Tunit))
| addr_subst : forall vm hm x v l p,
               subst vm hm x v (Addr l p) hm (Addr l p)
| hexpr_subst : forall vm hm x v h e t hm' e', 
                subst vm hm x v e hm' e' ->
                subst vm hm x v (Hexpr h e t) hm' (Hexpr h e' t)
with substs : vmap -> mem -> ident -> value -> list expr -> mem -> list expr -> Prop :=
| substs_nil : forall vm hm x v, 
               substs vm hm x v nil hm nil
| substs_cons : forall vm hm hm' hm'' x v e es e' es',
                subst vm hm x v e hm' e' ->
                substs vm hm' x v es hm'' es' -> 
                substs vm hm x v (e :: es) hm'' (e' :: es').

Section Big_step_semantics.

Variable ge : genv.

(* Would be useful in proving equivalence with Cstrategy for simpl expressions *)
Inductive bsem_expr : vmap -> mem -> expr -> mem -> value -> Prop :=
| bsem_val : forall vm hm v t,
             bsem_expr vm hm (Val v t) hm v
| bsem_var : forall vm hm x v t l, 
             vm!(x.(vname)) = Some (l, t) ->
             t = x.(vtype) ->
             deref_addr t hm l Ptrofs.zero Full v ->
             bsem_expr vm hm (Var x) hm v
| bsem_gvar : forall vm hm x v t l, 
              vm!(x.(vname)) = None ->
              Genv.find_symbol ge x.(vname) = Some l ->
              t = x.(vtype) ->
              deref_addr t hm l Ptrofs.zero Full v ->
              bsem_expr vm hm (Var x) hm v
| bsem_const_int : forall vm hm i t, 
                   bsem_expr vm hm (Const (ConsInt i) t) hm (Vint i)
| bsem_const_int64 : forall vm hm i t, 
                     bsem_expr vm hm (Const (ConsLong i) t) hm (Vint64 i)
| bsem_const_unit : forall vm hm,
                    bsem_expr vm hm (Const (ConsUnit) (Ptype Tunit)) hm (Vunit)
| bsem_appr : forall vm1 hm1 e es t l fd hm2 hm3 hm4 hm5 hm6 vm2 vs rv r hm7,
              bsem_expr vm1 hm1 e hm2 (Vloc l Ptrofs.zero) ->
              Genv.find_funct ge (transBeePL_value_cvalue (Vloc l Ptrofs.zero)) = Some (Internal fd) ->
              list_norepet (fd.(fn_args) ++ fd.(fn_vars)) ->
              alloc_variables vm1 hm2 (fd.(fn_args) ++ fd.(fn_vars)) vm2 hm3 -> 
              bsem_exprs vm2 hm3 es hm4 vs ->
              typeof_values vs (extract_types_vinfos fd.(fn_args)) ->
              bind_parameters vm1 hm4 fd.(fn_args) vs hm5  ->
              bsem_expr vm1 hm5 fd.(fn_body) hm6 rv -> 
              bind_parameters vm1 hm6 (r::nil) (rv::nil) hm7 ->
              typeof_value rv (fd.(fn_return)) ->
              bsem_expr vm1 hm1 (App (Some r.(vname)) e es t) hm7 rv 
| bsem_app : forall vm1 hm1 e es t l fd hm2 hm3 hm4 hm5 hm6 vm2 vs rv,
             bsem_expr vm1 hm1 e hm2 (Vloc l Ptrofs.zero) ->
             Genv.find_funct ge (transBeePL_value_cvalue (Vloc l Ptrofs.zero)) = Some (Internal fd) ->
             list_norepet (fd.(fn_args) ++ fd.(fn_vars)) ->
             alloc_variables vm1 hm2 (fd.(fn_args) ++ fd.(fn_vars)) vm2 hm3 -> 
             bsem_exprs vm2 hm3 es hm4 vs ->
             typeof_values vs (extract_types_vinfos fd.(fn_args)) ->
             bind_parameters vm1 hm4 fd.(fn_args) vs hm5  ->
             bsem_expr vm1 hm5 fd.(fn_body) hm6 rv -> 
             typeof_value rv (fd.(fn_return)) ->
             bsem_expr vm1 hm1 (App None e es t) hm6 rv 
| bsem_prim_uop : forall vm hm e v uop hm' v' t ct v'',
                  bsem_expr vm hm e hm' v ->
                  transBeePL_type (typeof_expr e) = OK ct ->
                  sem_unary_operation uop (transBeePL_value_cvalue v) ct hm' = Some v' ->
                  transC_val_bplvalue v' = OK v'' ->
                  bsem_expr vm hm (Prim (Uop uop) (e :: nil) t) hm' v''
| bsem_prim_bop : forall vm hm cenv e1 e2 t v1 v2 bop hm' hm'' v ct1 ct2 v',
                  bsem_expr vm hm e1 hm' v1 ->
                  bsem_expr vm hm e2 hm'' v2 ->
                  transBeePL_type (typeof_expr e1) = OK ct1 ->
                  transBeePL_type (typeof_expr e2) = OK ct2 ->
                  sem_binary_operation cenv bop (transBeePL_value_cvalue v1) ct1 (transBeePL_value_cvalue v2) ct2 hm'' = Some v ->
                  transC_val_bplvalue v = OK v' ->
                  bsem_expr vm hm (Prim (Bop bop) (e1 :: e2 :: nil) t) hm'' v'
| bsem_prim_ref : forall vm hm e t ct hm' v l, 
                  bsem_expr vm hm e hm' v ->
                  transBeePL_type (typeof_expr e) = OK ct ->
                  Mem.alloc hm 0 (sizeof_type t) = (hm', l) ->
                  bsem_expr vm hm (Prim Ref (e :: nil) t) hm' (Vloc l Ptrofs.zero)
| bsem_prim_deref : forall vm hm e t l ofs hm' v, 
                    bsem_expr vm hm e hm' (Vloc l ofs) ->
                    deref_addr t hm l ofs Full v ->
                    bsem_expr vm hm (Prim Deref (e :: nil) t) hm' v
| bsem_prim_massgn : forall vm hm e1 e2 l ofs v hm' hm'' hm''' ct1 ct2 bf v', (* Fix me *)
                     bsem_expr vm hm e1 hm' (Vloc l ofs) -> 
                     bsem_expr vm hm' e2 hm'' v ->
                     transBeePL_type (typeof_expr e1) = OK ct1 ->
                     transBeePL_type (typeof_expr e2) = OK ct2 ->
                     sem_cast (transBeePL_value_cvalue v) ct2 ct1 hm'' = Some (transBeePL_value_cvalue v') ->
                     assign_addr (typeof_expr e1) hm'' l ofs bf v' hm''' v' ->
                     bsem_expr vm hm (Prim Massgn (e1 :: e2 :: nil) (typeof_expr e1)) hm''' Vunit
| bsem_bind : forall vm hm x t e e' t' hm1 v e'' v' hm2 hm3,
              bsem_expr vm hm e hm1 v ->
              subst vm hm1 x v e' hm2 e'' ->
              bsem_expr vm hm2 e'' hm3 v' ->
              bsem_expr vm hm (Bind x t e e' t') hm3 v'
| bsem_cond_true : forall vm hm e1 hm' e2 hm'' e3 t vb v ct1, 
                   bsem_expr vm hm e1 hm' vb -> 
                   transBeePL_type (typeof_expr e1) = OK ct1 ->
                   bool_val (transBeePL_value_cvalue vb) ct1 hm = Some true ->
                   bsem_expr vm hm' e2 hm'' v ->
                   bsem_expr vm hm (Cond e1 e2 e3 t) hm'' v
| bsem_cond_false : forall vm hm e1 hm' e2 hm'' e3 t vb v ct1, 
                    bsem_expr vm hm e1 hm' vb -> 
                    transBeePL_type (typeof_expr e1) = OK ct1 ->
                    bool_val (transBeePL_value_cvalue vb) ct1 hm = Some false ->
                    bsem_expr vm hm' e3 hm'' v ->
                    bsem_expr vm hm (Cond e1 e2 e3 t) hm'' v
| bsem_unit : forall vm hm, 
              bsem_expr vm hm (Unit (Ptype Tunit)) hm Vunit
| bsem_addr : forall vm hm l ofs,
              bsem_expr vm hm (Addr l ofs) hm (Vloc l.(lname) ofs)
with bsem_exprs : vmap -> mem -> list expr -> mem -> list value -> Prop :=
| bsem_nil : forall vm hm,
             bsem_exprs vm hm nil hm nil
| bsem_cons : forall vm hm hm' hm'' v vs e es,
              bsem_expr vm hm e hm' v ->
              bsem_exprs vm hm' es hm'' vs ->
              bsem_exprs vm hm' (e :: es) hm'' (v :: vs).

End Big_step_semantics.

Section Small_step_semantics.

Variable ge : genv. 

(*** Small step semantics ***) 
Inductive sem_expr : vmap -> mem -> expr -> mem -> expr -> Prop :=
| sem_val_unit : forall vm hm,
                 sem_expr vm hm (Val Vunit (Ptype Tunit)) hm (Val Vunit (Ptype Tunit))
| sem_val_int : forall vm hm i t,
                 sem_expr vm hm (Val (Vint i) t) hm (Val (Vint i) t)
| sem_val_int64 : forall vm hm i t,
                  sem_expr vm hm (Val (Vint64 i) t) hm (Val (Vint64 i) t)
| sem_val_loc : forall vm hm t v l,
                deref_addr t hm l Ptrofs.zero Full v ->
                sem_expr vm hm (Val (Vloc l Ptrofs.zero) t) hm (Val v t)
| sem_var : forall vm hm x t l,
            vm!(x.(vname)) = Some (l, t) ->
            t = x.(vtype) ->
            sem_expr vm hm (Var x) hm (Val (Vloc l Ptrofs.zero) t)
| sem_gvar : forall vm hm x t l,
             vm!(x.(vname)) = None ->
             Genv.find_symbol ge x.(vname) = Some l ->
             sem_expr vm hm (Var x) hm (Addr {| lname := l; ltype := t; lbitfield := Full |}  Ptrofs.zero)
| sem_const_int : forall vm hm i t, 
                  sem_expr vm hm (Const (ConsInt i) t) hm (Val (Vint i) t)
| sem_const_int64 : forall vm hm i t, 
                    sem_expr vm hm (Const (ConsLong i) t) hm (Val (Vint64 i) t)
| sem_const_unit : forall vm hm,
                   sem_expr vm hm (Const (ConsUnit) (Ptype Tunit)) hm (Val (Vunit) (Ptype Tunit))
| sem_prim_uop : forall vm hm uop e e' hm' t,
                 sem_expr vm hm e hm' e' -> 
                 sem_expr vm hm (Prim (Uop uop) (e :: nil) t) hm' (Prim (Uop uop) (e' :: nil) t)
| sem_prim_uopv : forall vm hm uop e v hm' t ct v' v'',
                  transBeePL_type (typeof_expr e) = OK ct ->
                  sem_unary_operation uop (transBeePL_value_cvalue v) ct hm' = Some v' -> 
                  transC_val_bplvalue v' = OK v'' ->
                  sem_expr vm hm (Prim (Uop uop) ((Val v (typeof_expr e)) :: nil) t) hm (Val v'' t)
| sem_prim_bop1 : forall vm hm uop e1 e1' e2 hm' t,
                 sem_expr vm hm e1 hm' e1' -> 
                 sem_expr vm hm (Prim (Bop uop) (e1 :: e2 :: nil) t) hm' (Prim (Bop uop) (e1' :: e2 :: nil) t)
| sem_prim_bop2 : forall vm hm uop e2 e2' hm' tv t v,
                  sem_expr vm hm e2 hm' e2' -> 
                  sem_expr vm hm (Prim (Bop uop) ((Val v tv) :: e2 :: nil) t) hm' (Prim (Bop uop) ((Val v t) :: e2' :: nil) t)
| sem_prim_bopv : forall cenv vm hm bop v1 t1 v2 t2 hm' ct1 ct2 t v v',
                  transBeePL_type t1 = OK ct1 ->
                  transBeePL_type t2 = OK ct2 ->
                  sem_binary_operation cenv bop (transBeePL_value_cvalue v1) ct1 (transBeePL_value_cvalue v2) ct2 hm' = Some v ->
                  transC_val_bplvalue v = OK v' ->
                  sem_expr vm hm (Prim (Bop bop) ((Val v1 t1) :: (Val v2 t2) :: nil) t) hm' (Val v' t)
| sem_prim_ref : forall vm hm e e' t hm',
                 sem_expr vm hm e hm' e' ->
                 sem_expr vm hm (Prim Ref (e :: nil) t) hm' (Prim Ref (e' :: nil) t)
| sem_prim_refv : forall vm hm v tv t ct hm' l,
                  transBeePL_type tv = OK ct ->
                  Mem.alloc hm 0 (sizeof_type t) = (hm', l) ->
                  sem_expr vm hm (Prim Ref ((Val v tv) :: nil) t) hm' (Val (Vloc l Ptrofs.zero) t)
| sem_prim_deref : forall vm hm e t hm' e',
                   sem_expr vm hm e hm' e' ->
                   sem_expr vm hm (Prim Deref (e :: nil) t) hm' (Prim Deref (e' :: nil) t)
| sem_prim_derefv : forall vm hm v tv t ofs l,
                    deref_addr t hm l ofs Full v ->
                    sem_expr vm hm (Prim Deref (Val (Vloc l ofs) tv:: nil) t) hm (Val v t)
| sem_prim_massgn1 : forall vm hm e1 e2 t e1' hm',
                     sem_expr vm hm e1 hm' e1' ->
                     sem_expr vm hm (Prim Massgn (e1 :: e2 :: nil) t) hm' (Prim Massgn (e1' :: e2 :: nil) t) 
| sem_prim_massgn2 : forall vm hm l ofs e2 e2' t tv hm',
                     sem_expr vm hm e2 hm' e2' ->
                     sem_expr vm hm (Prim Massgn (Val (Vloc l ofs) tv :: e2 :: nil) t) hm' (Prim Massgn (Val (Vloc l ofs) tv :: e2' :: nil) t)
| sem_prim_massgnv : forall vm hm l ofs tv1 v tv2 ct1 ct2 t hm' v' bf,
                     transBeePL_type tv1 = OK ct1 ->
                     transBeePL_type tv2 = OK ct2 ->
                     sem_cast (transBeePL_value_cvalue v) ct2 ct1 hm = Some (transBeePL_value_cvalue v') ->
                     assign_addr tv1 hm l ofs bf v' hm' v' ->
                     sem_expr vm hm (Prim Massgn (Val (Vloc l ofs) tv1 :: Val v tv2 :: nil) t) hm' (Val Vunit (Ptype Tunit))
| sem_bind1 : forall vm hm x e1 e1' e2 t t' hm',
              sem_expr vm hm e1 hm' e1' ->
              sem_expr vm hm (Bind x t e1 e2 t') hm' (Bind x t e1' e2 t')
| sem_bind2 : forall vm hm x v e2 e2' t t' hm',
              subst vm hm x v e2 hm' e2' ->
              sem_expr vm hm (Bind x t (Val v t) e2 t') hm' e2'
| sem_condt : forall vm hm v tv e2 e3 ct t,
              transBeePL_type tv = OK ct ->
              bool_val (transBeePL_value_cvalue v) ct hm = Some true ->
              sem_expr vm hm (Cond (Val v tv) e2 e3 t) hm e2
| sem_condf : forall vm hm v tv e2 e3 ct t,
              transBeePL_type tv = OK ct ->
              bool_val (transBeePL_value_cvalue v) ct hm = Some false ->
              sem_expr vm hm (Cond (Val v tv) e2 e3 t) hm e3
| sem_cond : forall vm hm e1 e2 e3 t e1' hm',
             sem_expr vm hm e1 hm' e1' ->
             sem_expr vm hm (Cond e1 e2 e3 t) hm (Cond e1' e2 e3 t)
| sem_unit : forall vm hm,
             sem_expr vm hm (Unit (Ptype Tunit)) hm (Val Vunit (Ptype Tunit))
| sem_appr1 : forall vm hm r e es t v hm' ts ef rt,
              sem_expr vm hm e hm' (Val v (typeof_expr e)) ->
              sem_expr vm hm (App (Some r.(vname)) e es t) hm' (App (Some r.(vname)) (Val v (Ftype ts ef rt)) es t)
| sem_appr2 : forall vm hm v fd vm1 hm1 hm2 hm3 hm4 hm5 vs rv r ts ef rt es t, 
              Genv.find_funct ge (transBeePL_value_cvalue v) = Some (Internal fd) ->
              list_norepet (fd.(fn_args) ++ fd.(fn_vars)) ->
              alloc_variables vm hm (fd.(fn_args) ++ fd.(fn_vars)) vm1 hm1 -> 
              bsem_exprs ge vm1 hm1 es hm2 vs ->
              typeof_values vs (extract_types_vinfos fd.(fn_args)) ->
              bind_parameters vm1 hm2 fd.(fn_args) vs hm3  ->
              bsem_expr ge vm1 hm3 fd.(fn_body) hm4 rv ->
              bind_parameters vm1 hm4 (r::nil) (rv::nil) hm5 ->
              typeof_value rv (fd.(fn_return)) ->
              sem_expr vm hm (App (Some r.(vname)) (Val v (Ftype ts ef rt)) es t) hm5 (Val rv fd.(fn_return))
(* Fix me *)
| sem_addr : forall vm hm t l bf ofs v,
             deref_addr t hm l ofs bf v ->
             sem_expr vm hm (Addr {| lname := l; ltype := t; lbitfield := bf |} ofs) hm (Val v t).

End Small_step_semantics.
