Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Globalenvs compcert.lib.Coqlib Ctypes.
Require Import BeePL_aux BeeTypes Axioms Memory Int Cop Memtype Errors Csem SimplExpr.
From mathcomp Require Import all_ssreflect. 

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
                                and returns the fresh address *) (* rvalue *)
| Deref : builtin            (* dereference : deref t e returns the value of type t 
                                present at location e *) (* lvalue *)
| Massgn : builtin           (* assign value at a location l (l := e) 
                                assigns the evaluation of e to the reference cell l *)
| Uop : Cop.unary_operation -> builtin       (* unary operator *) (* rvalue *)
| Bop : Cop.binary_operation -> builtin       (* binary operator *) (* rvalue *)
| Run : Memory.mem -> builtin      (* eliminate heap effect : [r1-> v1, ..., ern->vn] e 
                                reduces to e captures the essence of state isolation 
                                and reduces to a value discarding the heap *).


(* The source language never exposes the heap binding construct hpφ.e directly to the user 
   but during evaluation the reductions on heap operations create heaps and use them. *)
Inductive expr : Type :=
| Val : value -> type -> expr                                      (* value *) (* rvalue *)
| Valof : expr -> type -> expr                                     (* not written by programmer, 
                                                                      but denotes read from a location at rvalue *)
| Var : vinfo -> expr                                              (* variable *) (* lvalue *)
| Const : constant -> type -> expr                                 (* constant *) (* rvalue *)
| App : expr -> list expr -> type -> expr                          (* function application *) (* rvalue *)
| Prim : builtin -> list expr -> type -> expr                      (* primitive operations *)
| Bind : ident -> type -> expr -> expr -> type -> expr             (* let binding: type of continuation *)
| Cond : expr -> expr -> expr -> type -> expr                      (* if e then e else e *) 
| Unit : type -> expr                                                      (* unit *)
(* not intended to be written by programmers:
   Only should play role in operational semantics *)
| Addr : linfo -> ptrofs -> expr                                   (* address *)
| Hexpr : Memory.mem -> expr -> type -> expr                       (* heap effect *).

Definition is_value (e : expr) : bool :=
match e with 
| Val v t => true 
| _ => false
end.
 
Definition typeof_expr (e : expr) : BeeTypes.type :=
match e with 
| Val v t => t
| Valof e t => t
| Var x => x.(vtype)
| Const x t => t
| App e ts t => t
| Prim b es t => t
| Bind x t e e' t' => t'
| Cond e e' e'' t => t
| Unit t => t
| Addr l p => l.(ltype) 
| Hexpr h e t => t
end.

Fixpoint typeof_exprs (e : list expr) : list BeeTypes.type :=
match e with 
| nil => nil
| e :: es => typeof_expr e :: typeof_exprs es
end.

Record function : Type := mkfunction { fn_return: type;
                                       fn_callconv: calling_convention;
                                       fn_args: list vinfo;
                                       fn_vars: list vinfo;
                                       fn_body: expr }.

Inductive fundef : Type :=
| Internal : function -> fundef
| External : fundef. (* Fix me: add later *)

(** Type of a function definition. *)

Definition type_of_function (f: function) (ef : effect) : type :=
  Ftype (extract_types_vinfos (fn_args f)) ef (fn_return f).

Definition type_of_fundef (f: fundef) (ef : effect) : type :=
  match f with
  | Internal fd => type_of_function fd ef
  | External  => (Ptype Tunit) (* Fix me: add later *)
  end.

Inductive init_data : Set :=
| Init_int8 : int -> init_data
| Init_int16 : int -> init_data
| Init_int32 : int -> init_data
| Init_int64 : int64 -> init_data.

Definition globvar (V : Type) := AST.globvar V.

Definition globdef (F V : Type) := AST.globdef F V.

Record program  : Type := mkprogam { prog_defs : list (ident * globdef fundef type);
                                     prog_public : list ident;
                                     prog_main : ident;
                                     prog_types : list composite_definition;
                                     prog_comp_env : composite_env;
                                     prog_comp_env_eq : build_composite_env prog_types = OK prog_comp_env }.

(************************** Operation Semantics **************************************)
(* Global environments are a component of the dynamic semantics of
   BeePL language.  A global environment maps symbol names 
   (names of functions and of global variables)
   to the corresponding function declarations. *) 
Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }. 

Definition trans_program_astprog (p : program) : AST.program fundef type :=
@mkprogram fundef type
   p.(prog_defs)
   p.(prog_public)
   p.(prog_main).

Definition globalenv (p: program) :=
  {| genv_genv := @Genv.globalenv fundef type (trans_program_astprog p); genv_cenv := p.(prog_comp_env) |}.

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

(* Converts list of BeePL value to list of C value *)
Fixpoint transBeePL_values_cvalues (vs : list value) : list Values.val :=
match vs with 
| nil => nil
| v :: vs => transBeePL_value_cvalue v :: transBeePL_values_cvalues vs
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
Inductive deref_addr (ty : type) (m : Memory.mem) (addr : Values.block) (ofs : ptrofs) : bitfield -> value -> Prop :=
| deref_addr_value : forall chunk v v',
  access_mode ty = By_value chunk ->
  type_is_volatile ty = false ->
  Mem.loadv chunk m (transBeePL_value_cvalue (Vloc addr ofs)) = Some v ->
  transC_val_bplvalue v = OK v' ->
  deref_addr ty m addr ofs Full v'
| deref_addr_reference:
  access_mode ty = By_reference ->
  deref_addr ty m addr ofs Full (Vloc addr ofs).

(* [assign_addr ty m addr ofs v] returns the updated memory after storing the value v at address [addr] and offset 
   [ofs] *)
Inductive assign_addr (ty : type) (m : Memory.mem) (addr : Values.block) (ofs : ptrofs) : bitfield -> value -> Memory.mem -> value -> Prop :=
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
Inductive alloc_variables : vmap -> Memory.mem -> list vinfo -> vmap -> Memory.mem -> Prop :=
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
Inductive bind_variables (e: vmap): Memory.mem -> list vinfo -> list value -> Memory.mem -> Prop :=
| bind_variables_nil: forall m,
                      bind_variables e m nil nil m
| bind_variables_cons: forall m id ty params v1 vl v1' b m1 m2,
                       PTree.get id e = Some(b, ty) ->
                       assign_addr ty m b Ptrofs.zero Full v1 m1 v1' ->
                       bind_variables e m1 params vl m2 ->
                       bind_variables e m ({| vname := id; vtype := ty|} :: params) (v1 :: vl) m2.

(* Substitution *)
Inductive subst : vmap -> Memory.mem -> ident -> value -> expr -> Memory.mem -> expr -> Prop :=
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
| valof_subst : forall x v e t e' vm hm hm',
                subst vm hm x v e hm' e' ->
                subst vm hm x v (Valof e t) hm' (Valof e' t)
| app_subst : forall vm hm x v e es t e' hm' hm'' es',
              subst vm hm x v e hm' e' ->
              substs vm hm' x v es hm'' es' ->
              subst vm hm x v (App e es t) hm'' (App e' es' t)
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
with substs : vmap -> Memory.mem -> ident -> value -> list expr -> Memory.mem -> list expr -> Prop :=
| substs_nil : forall vm hm x v, 
               substs vm hm x v nil hm nil
| substs_cons : forall vm hm hm' hm'' x v e es e' es',
                subst vm hm x v e hm' e' ->
                substs vm hm' x v es hm'' es' -> 
                substs vm hm x v (e :: es) hm'' (e' :: es').

Section Big_step_semantics.

Variable (ge : BeePL.genv).
Variable (vm : vmap).

(* Would be useful in proving equivalence with Cstrategy for simpl expressions *)
Inductive bsem_expr_slv : Memory.mem -> expr -> positive -> ptrofs -> bitfield -> Prop :=
| bsem_var : forall hm x t l, 
              vm!(x.(vname)) = Some (l, t) ->
              t = x.(vtype) ->
              bsem_expr_slv hm (Var x) l Ptrofs.zero Full
| bsem_gvar : forall hm x t l, 
              vm!(x.(vname)) = None ->
              Genv.find_symbol ge x.(vname) = Some l ->
              t = x.(vtype) ->
              bsem_expr_slv hm (Var x) l Ptrofs.zero Full
| bsem_addr : forall hm l ofs,
              bsem_expr_slv hm (Addr l ofs) l.(lname) ofs l.(lbitfield)
| bsem_prim_deref : forall hm e t l ofs, 
                    bsem_expr_srv hm e (Vloc l ofs) ->
                    bsem_expr_slv hm (Prim Deref (e :: nil) t) l ofs Full
with bsem_expr_srv : Memory.mem -> expr -> value -> Prop :=
| bsem_val : forall hm v t,
             bsem_expr_srv hm (Val v t) v
| bsem_const_int : forall hm i t, 
                   bsem_expr_srv hm (Const (ConsInt i) t) (Vint i)
| bsem_const_int64 : forall hm i t, 
                     bsem_expr_srv hm (Const (ConsLong i) t) (Vint64 i)
| bsem_const_uint : forall hm, 
                    bsem_expr_srv hm (Const (ConsUnit) (Ptype Tunit)) (Vunit)
| bsem_val_rv : forall hm e t l ofs bf v,
                bsem_expr_slv hm e l ofs bf ->
                deref_addr (typeof_expr e) hm l ofs bf v ->
                typeof_expr e = t ->
                BeeTypes.type_is_volatile t = false ->
                bsem_expr_srv hm (Valof e t) v
| bsem_prim_uop : forall hm e v uop  v' t ct v'' g g' i,
                  bsem_expr_srv hm e v ->
                  transBeePL_type (typeof_expr e) g = Res ct g' i ->
                  t = (typeof_expr e) ->
                  sem_unary_operation uop (transBeePL_value_cvalue v) ct hm = Some v' ->
                  transC_val_bplvalue v' = OK v'' ->
                  bsem_expr_srv hm (Prim (Uop uop) (e :: nil) t) v''
| bsem_prim_bop : forall hm e1 e2 t v1 v2 bop v ct1 ct2 v' g g' g'' i i',
                  bsem_expr_srv hm e1 v1 ->
                  bsem_expr_srv hm e2 v2 ->
                  transBeePL_type (typeof_expr e1) g = Res ct1 g' i ->
                  transBeePL_type (typeof_expr e2) g' = Res ct2 g'' i'->
                  sem_binary_operation ge bop (transBeePL_value_cvalue v1) ct1 (transBeePL_value_cvalue v2) ct2 hm = Some v ->
                  transC_val_bplvalue v = OK v' ->
                  bsem_expr_srv hm (Prim (Bop bop) (e1 :: e2 :: nil) t) v'
| bsem_unit : forall hm, 
              bsem_expr_srv hm (Unit (Ptype Tunit)) Vunit.

Scheme bsem_expr_slv_mut := Minimality for bsem_expr_slv Sort Prop
  with bsem_expr_srv_mut := Minimality for bsem_expr_srv Sort Prop.
Combined Scheme bsem_expr_slv_srv_mut from bsem_expr_slv_mut,bsem_expr_srv_mut.

Inductive bsem_expr_srvs : Memory.mem -> list expr -> list value -> Prop :=
| bsem_expr_srv_nil : forall hm, 
                      bsem_expr_srvs hm nil nil
| bsem_expr_srv_cons : forall hm e es v vs,
                       bsem_expr_srv hm e v ->
                       bsem_expr_srvs hm es vs ->
                       bsem_expr_srvs hm (e :: es) (v :: vs).

(* Big step semantics for expressions with effects *)
Inductive bsem_expr : vmap -> Memory.mem -> expr -> Memory.mem -> value -> Prop :=
| bsem_prim_ref : forall vm hm e v t hm' l, 
                  bsem_expr_srv hm e v ->
                  Mem.alloc hm 0 (sizeof_type (typeof_expr e)) = (hm', l) ->
                  assign_addr (typeof_expr e) hm' l Ptrofs.zero Full v hm' v ->
                  bsem_expr vm hm (Prim Ref (e :: nil) t) hm' (Vloc l Ptrofs.zero)
| bsem_prim_massgn : forall vm hm e1 e2 l ofs v hm' ct1 ct2 bf v' g g' g'' i i', (* Fix me *)
                     bsem_expr_slv hm e1 l ofs bf -> 
                     bsem_expr_srv hm e2 v ->
                     transBeePL_type (typeof_expr e1) g = Res ct1 g' i ->
                     transBeePL_type (typeof_expr e2) g' = Res ct2 g'' i' ->
                     sem_cast (transBeePL_value_cvalue v) ct2 ct1 hm = Some (transBeePL_value_cvalue v') ->
                     assign_addr (typeof_expr e1) hm l ofs bf v' hm' v' ->
                     bsem_expr vm hm (Prim Massgn (e1 :: e2 :: nil) (typeof_expr e1)) hm' Vunit
| bsem_bind : forall vm hm x t e e' t' hm1 v e'' v' hm2,
              bsem_expr_srv hm e v ->
              subst vm hm x v e' hm1 e'' ->
              bsem_expr vm hm1 e'' hm2 v' ->
              bsem_expr vm hm (Bind x t e e' t') hm2 v'
| bsem_cond_true : forall vm hm e1 e2 hm' e3 t vb v ct1 g i, 
                   bsem_expr_srv hm e1 vb -> 
                   transBeePL_type (typeof_expr e1) (initial_generator tt) = Res ct1 g i ->
                   bool_val (transBeePL_value_cvalue vb) ct1 hm = Some true ->
                   bsem_expr vm hm e2 hm' v ->
                   bsem_expr vm hm (Cond e1 e2 e3 t) hm' v
| bsem_cond_false : forall vm hm e1 hm' e2 e3 t vb v ct1 g i, 
                    bsem_expr_srv hm e1 vb -> 
                    transBeePL_type (typeof_expr e1) (initial_generator tt) = Res ct1 g i ->
                    bool_val (transBeePL_value_cvalue vb) ct1 hm = Some false ->
                    bsem_expr vm hm e3 hm' v ->
                    bsem_expr vm hm (Cond e1 e2 e3 t) hm' v
| bsem_app : forall vm1 hm1 e es t l fd hm2 hm3 hm4 hm5 vm2 vs rv,
              bsem_expr_srv hm1 e (Vloc l Ptrofs.zero) ->
              Genv.find_funct ge (transBeePL_value_cvalue (Vloc l Ptrofs.zero)) = Some (Internal fd) ->
              list_norepet (fd.(fn_args) ++ fd.(fn_vars)) ->
              alloc_variables vm1 hm2 (fd.(fn_args) ++ fd.(fn_vars)) vm2 hm3 -> 
              bsem_expr_srvs hm3 es vs ->
              typeof_values vs (extract_types_vinfos fd.(fn_args)) ->
              bind_variables vm1 hm3 fd.(fn_args) vs hm4  ->
              bsem_expr vm1 hm4 fd.(fn_body) hm5 rv -> 
              (*bind_variables vm1 hm5 (r::nil) (rv::nil) hm6 ->
              typeof_value rv (fd.(fn_return)) ->*)
              bsem_expr vm1 hm1 (App e es t) hm5 rv.             
               
End Big_step_semantics.

Section Bsem_expr_slv_srv_mut.

Variable (ge : genv).
Variable (vm : vmap).

Context (Plv : Memory.mem -> expr -> positive -> ptrofs -> bitfield -> Prop).
Context (Prv : Memory.mem -> expr -> value -> Prop).
Context (Plvar : forall hm x t l, 
                 vm!(x.(vname)) = Some (l, t) ->
                 t = x.(vtype) ->
                 Plv hm (Var x) l Ptrofs.zero Full).
Context (Pgvar : forall hm x t l,
                 vm!(x.(vname)) = None ->
                 Genv.find_symbol ge x.(vname) = Some l ->
                 t = x.(vtype) ->
                 Plv hm (Var x) l Ptrofs.zero Full).
Context (Paddr : forall hm l ofs,
                 Plv hm (Addr l ofs) l.(lname) ofs l.(lbitfield)).
Context (Pderef : forall hm e t l ofs,
                  Prv hm e (Vloc l ofs) ->
                  Plv hm (Prim Deref (e :: nil) t) l ofs Full).
Context (Pval : forall hm v t,
                 Prv hm (Val v t) v).
Context (Pci : forall hm i t, 
               Prv hm (Const (ConsInt i) t) (Vint i)).
Context (Pcl : forall hm i t, 
               Prv hm (Const (ConsLong i) t) (Vint64 i)).
Context (Pcu : forall hm, 
               Prv hm (Const (ConsUnit) (Ptype Tunit)) Vunit).
Context (Pvalof : forall hm e t l ofs bf v,
                  Plv hm e l ofs bf ->
                  deref_addr (typeof_expr e) hm l ofs bf v ->
                  typeof_expr e = t ->
                  BeeTypes.type_is_volatile t = false ->
                  Prv hm (Valof e t) v).
Context (Puop : forall hm e v uop  v' t ct v'' g g' i,
                Prv hm e v ->
                transBeePL_type (typeof_expr e) g = Res ct g' i ->
                t = (typeof_expr e) ->
                sem_unary_operation uop (transBeePL_value_cvalue v) ct hm = Some v' ->
                transC_val_bplvalue v' = OK v'' ->
                Prv hm (Prim (Uop uop) (e :: nil) t) v'').
Context (Pbop : forall hm e1 e2 t v1 v2 bop v ct1 ct2 v' g g' g'' i i',
                Prv hm e1 v1 ->
                Prv hm e2 v2 ->
                transBeePL_type (typeof_expr e1) g = Res ct1 g' i ->
                transBeePL_type (typeof_expr e2) g' = Res ct2 g'' i'->
                sem_binary_operation ge bop (transBeePL_value_cvalue v1) ct1 (transBeePL_value_cvalue v2) ct2 hm = Some v ->
                transC_val_bplvalue v = OK v' ->
                Prv hm (Prim (Bop bop) (e1 :: e2 :: nil) t) v').
Context (Punit : forall hm, 
                 Prv hm (Unit (Ptype Tunit)) Vunit).

Lemma bsem_expr_slv_rlv_ind : 
(forall hm e l ofs bf, bsem_expr_slv ge vm hm e l ofs bf -> Plv hm e l ofs bf) /\
(forall hm e v, bsem_expr_srv ge vm hm e v -> Prv hm e v).
Proof.
apply bsem_expr_slv_srv_mut=> //=.
+ move=> hm e t l ofs hr hp.
Admitted.

End Bsem_expr_slv_srv_mut.

Section Small_step_semantics.

Variable (ge: genv).
Variable (vm : vmap). 

Inductive is_list_val : list expr -> list value -> Prop :=
  | is_args_nil:
      is_list_val nil nil
  | is_args_cons: forall v ty vs vs',
      is_list_val vs vs' ->
      is_list_val (Val v ty :: vs) (v :: vs'). 

Inductive callreduction : expr -> Memory.mem -> fundef -> list value -> type -> Prop :=
| red_call : forall hm v fd ts ef rt vargs vargs' t, 
             Genv.find_funct ge (transBeePL_value_cvalue v) = Some (Internal fd) ->
             type_of_fundef (Internal fd) ef = (Ftype ts ef rt) ->
             is_list_val vargs vargs' ->
             callreduction (App (Val v (Ftype ts ef rt)) vargs t) hm (Internal fd) vargs' t.

Inductive lreduction : expr -> Memory.mem -> expr -> Memory.mem -> Prop :=
| lred_var_local : forall hm x t l,
                   vm!(x.(vname)) = Some (l, t) ->
                   t = x.(vtype) ->
                   lreduction (Var x) hm (Addr {| lname := l; ltype := t; lbitfield := Full |} Ptrofs.zero) hm
| lred_var_global : forall hm x t l,
                    vm!(x.(vname)) = None ->
                    t = x.(vtype) ->
                    Genv.find_symbol ge x.(vname) = Some l ->
                    lreduction (Var x) hm (Addr {| lname := l; ltype := t; lbitfield := Full |} Ptrofs.zero) hm
| lred_deref : forall hm l ofs tv t,
               lreduction (Prim Deref (Val (Vloc l ofs) tv:: nil) t) hm 
               (Addr {| lname := l; ltype := t; lbitfield := Full |} ofs) hm
| lred_deref1 : forall hm e e' t hm',
                rreduction e hm e' hm' ->
                lreduction (Prim Deref [:: e] t) hm  (Prim Deref [:: e'] t) hm'

with rreduction : expr -> Memory.mem -> expr -> Memory.mem -> Prop :=
| rred_valof : forall hm e t l ofs bf v,
               deref_addr (typeof_expr e) hm l ofs bf v ->
               typeof_expr e = t ->
               BeeTypes.type_is_volatile t = false ->
               rreduction (Valof (Addr {| lname := l; ltype := t; lbitfield := bf |} ofs) t) hm (Val v t) hm
| rred_valof1 : forall hm e t e' hm',
                lreduction e hm e' hm' ->
                rreduction (Valof e t) hm (Valof e' t) hm'
| rred_ref : forall hm v tv t hm' l, (* fix me *) (* stack allocation *)
             Mem.alloc hm 0 (sizeof_type tv) = (hm', l) ->
             assign_addr tv hm' l Ptrofs.zero Full v hm' v ->
             rreduction (Prim Ref [:: (Val v tv)] t) hm (Val (Vloc l Ptrofs.zero) tv) hm'
| rred_ref1 : forall hm e t e' hm', 
              rreduction e hm e' hm' ->
              rreduction (Prim Ref [:: e] t) hm (Prim Ref [:: e] t) hm'
| rred_uop : forall hm v t ct uop v' v'',
             transBeePL_type t = ret ct ->
             sem_unary_operation uop (transBeePL_value_cvalue v) ct hm = Some v' -> 
             transC_val_bplvalue v' = OK v'' ->
             rreduction (Prim (Uop uop) ((Val v t) :: nil) t) hm (Val v'' t) hm
| rred_uop1 : forall hm t uop e e' hm',
              rreduction e hm e' hm' ->
              rreduction (Prim (Uop uop) (e :: nil) t) hm (Prim (Uop uop) (e' :: nil) t) hm'
| rred_bop : forall hm bop v1 t1 v2 t2 ct1 ct2 t v v',
             transBeePL_type t1 = ret ct1 ->
             transBeePL_type t2 = ret ct2 ->
             sem_binary_operation ge bop (transBeePL_value_cvalue v1) ct1 (transBeePL_value_cvalue v2) ct2 hm = Some v ->
             transC_val_bplvalue v = OK v' ->
             rreduction (Prim (Bop bop) ((Val v1 t1) :: (Val v2 t2) :: nil) t) hm (Val v' t) hm
| rred_bop1 : forall hm t bop e1 e1' e2 hm',
              rreduction e1 hm e1' hm' ->
              rreduction (Prim (Bop bop) (e1 :: e2 :: nil) t) hm (Prim (Bop bop) (e1' :: e2 :: nil) t) hm'
| rred_bop2 : forall hm bop v1 t1 t e2 e2' hm',
              rreduction e2 hm e2' hm' ->
              rreduction (Prim (Bop bop) ((Val v1 t1) :: e2 :: nil) t) hm (Prim (Bop bop) ((Val v1 t1) :: e2' :: nil) t) hm'
| rred_cond : forall hm v e1 e2 tv t ctv b, 
              transBeePL_type tv = ret ctv ->
              bool_val (transBeePL_value_cvalue v) ctv hm = Some b ->
              rreduction (Cond (Val v tv) e1 e2 t) hm (if b then e1 else e2) hm
| rred_cond1 : forall hm e1 e2 e3 t e1' hm', 
               rreduction e1 hm e1' hm' ->
               rreduction (Cond e1 e2 e3 t) hm (Cond e1' e2 e3 t) hm
| rred_massgn : forall hm l ofs v tv2 ct1 ct2 t hm' v' bf,
                transBeePL_type t = ret ct1 ->
                transBeePL_type tv2 = ret ct2 ->
                sem_cast (transBeePL_value_cvalue v) ct2 ct1 hm = Some (transBeePL_value_cvalue v') ->
                assign_addr t hm l ofs bf v' hm' v' ->
                rreduction (Prim Massgn ((Addr {| lname := l; ltype := t; lbitfield := bf |} ofs) :: Val v tv2 :: nil) t) hm (Val v' t) hm'
| rred_massgn1 : forall hm e1 e2 t e1' hm',
                 rreduction e1 hm e1' hm' ->
                 rreduction (Prim Massgn (e1 :: e2 :: nil) t) hm (Prim Massgn (e1' :: e2 :: nil) t) hm'
| rred_massgn2 : forall hm l bf ofs e2 t e2' hm',
                 rreduction e2 hm e2' hm' ->
                 rreduction (Prim Massgn ((Addr {| lname := l; ltype := t; lbitfield := bf |} ofs) :: e2 :: nil) t) hm 
                            (Prim Massgn ((Addr {| lname := l; ltype := t; lbitfield := bf |} ofs) :: e2' :: nil) t)  hm'
| rred_bind : forall vm hm x v e2 e2' t t' hm',
              subst vm hm x v e2 hm' e2' ->
              rreduction (Bind x t (Val v t) e2 t') hm e2' hm'
| rred_bind1 : forall hm x e1 e2 e1' t t' hm',
               rreduction e1 hm e1' hm' ->
               rreduction (Bind x t e1 e2 t') hm (Bind x t e1' e2 t') hm'
| rred_app1 : forall hm e e' hm' es t,
              rreduction e hm e' hm' ->
              rreduction (App e es t) hm (App e' es t) hm'
| rred_app2 : forall hm v ts ef rt es hm' es' t,
              rreductions es hm es' hm' ->
              rreduction (App (Val v (Ftype ts ef rt)) es t) hm (App (Val v (Ftype ts ef rt)) es t) hm'
| rred_unit : forall hm,
              rreduction (Unit (Ptype Tunit)) hm (Val Vunit (Ptype Tunit)) hm

with rreductions : list expr -> Memory.mem -> list expr -> Memory.mem -> Prop :=
| nil_rs : forall hm, rreductions nil hm nil hm
| cons_rs : forall e es hm hm' hm'' e' es', 
            rreduction e hm e' hm' ->
            rreductions es hm' es' hm'' ->
            rreductions (e :: es) hm (e' :: es') hm''.

Scheme lreduction_mut := Minimality for lreduction Sort Prop
  with rreduction_mut := Minimality for rreduction Sort Prop
  with rreductions_mut := Minimality for rreductions Sort Prop.
Combined Scheme lreduction_rreduction_rreductions_mut from lreduction_mut, rreduction_mut, rreductions_mut.

(* Continuation describe the computations that remain to be performed 
   after the expression under consideration has evaluated completely *)
Inductive cont: Type :=
| Kstop : cont 
| Kdo : cont -> cont  (* after [x] in [x;] *)
| Kcall : function -> (* calling function *)
          vmap ->     (* local env of calling function *)
          type ->     (* type of call expression *)
          cont -> cont.          

(* Execution states of the program are grouped in 4 classes corresponding to the part of 
   the program we are currently executing. It can be an expression [ExprState], a transition 
   from a calling function to a called function [CallState], or the symmetrical transition
   from a function back to its caller [ReturnState] *)
Inductive state : Type :=
| ExprState (f : function)            (* reduction of an expression *)
            (e : expr)
            (k : cont)
            (vm : vmap)
            (m : Memory.mem) : state
| CallState (fd : fundef)             (* calling a function *)
            (args : list value)
            (k : cont)
            (m : Memory.mem) : state
| StuckState                          (* undefined behvaior occured *).

(* Reduction contexts *) 
Definition expr_kind (e: expr) : Csem.kind :=
match e with
| Val v t => RV 
| Valof e t => RV 
| Var v => LV
| Const c t => RV
| App e es t => RV
| Prim b es t => match b with 
                 | Ref => RV
                 | Deref => LV
                 | Massgn => RV 
                 | Uop o => RV
                 | Bop o => RV
                 | Run h => RV (* Fix me *)
                 end
| Bind x t e e' t' => RV
| Cond e1 e2 e3 t => RV
| Unit t => RV
| Addr l ofs => LV
| Hexpr _ _ _ => RV (* Fix me *)
end. 

Definition is_lv (e : expr) : bool :=
match e with 
| Val v t => false 
| Valof e t => false
| Var v => true 
| Const c t => false
| App e es t => false 
| Prim b es t => match b with 
                 | Ref => false 
                 | Deref => true 
                 | Massgn => false
                 | Uop o => false
                 | Bop o => false
                 | Run h => false (* fix me *)
                 end
| Bind x t e1 e2 t' => false
| Cond e1 e2 e3 t => false
| Unit t => false 
| Addr l ofs => false
| Hexpr m e t => false (* fix me *)
end.

Definition is_rv (e : expr) : bool :=
match e with 
| Val v t => false
| Valof e t => true
| Var v => false 
| Const c t => true
| App e es t => true 
| Prim b es t => match b with 
                 | Ref => true 
                 | Deref => false 
                 | Massgn => true
                 | Uop o => true
                 | Bop o => true
                 | Run h => false (* fix me *)
                 end
| Bind x t e1 e2 t' => true
| Cond e1 e2 e3 t => true
| Unit t => true
| Addr l ofs => false
| Hexpr m e t => false (* fix me *)
end.

Definition is_val (e : expr) : bool :=
match e with 
| Val v t => true 
| _ => false
end.

Definition is_addr (e : expr) : bool :=
match e with 
| Addr l t => true 
| _ => false
end.

Fixpoint is_vals (es : list expr) : bool :=
match es with 
| nil => true
| e :: es => is_val e && is_vals es
end.

Definition is_reduced_form (e : expr) : bool :=
match e with 
| Val v t => true 
| Valof e t => is_addr e
| Var v => true 
| Const c t => true 
| App e es t => false 
| Prim b es t => match b with 
                 | Ref => is_vals es 
                 | Deref => is_vals es
                 | Massgn => match es with 
                             | (e1 :: e2 :: nil) => is_addr e1 && is_val e2
                             | _ => false
                             end
                 | Uop o => is_vals es 
                 | Bop o => is_vals es 
                 | Run h => false (* fix me *)
                 end
| Bind x t e1 e2 t' => is_vals (e1 :: e2 :: nil)
| Cond e1 e2 e3 t => is_val e1
| Unit t => true 
| Addr l ofs => true
| Hexpr m e t => false (* fix me *)
end.

              
(* Relation representing safe execution of expressions *)
Inductive expr_safe : expr -> Memory.mem -> Prop :=
| expr_safe_lred : forall e m e' m',
                   lreduction e m e' m' ->
                   expr_safe e m
| expr_safe_rred : forall e m e' m',
                   rreduction e m e' m' ->
                   expr_safe e m
| expr_safe_call : forall e m fd args t,
                   callreduction e m fd args t ->
                   expr_safe e m.

Definition not_stuck (e : expr) (m : Memory.mem) : Prop :=
expr_safe e m.

(* Reduction semantics *) 
Inductive ssem : state -> state -> Prop :=
| s_lreduction : forall f e k e' m m',
                 lreduction e m e' m' ->
                 ssem (ExprState f e k vm m) (ExprState f e' k vm m')
| s_rreduction : forall f e k m e' m',
                 rreduction e m e' m' ->
                 ssem (ExprState f e k vm m) (ExprState f e' k vm m')
| s_call : forall f e k m fd args t,
           callreduction e m fd args t ->
           ssem (ExprState f e k vm m) (CallState fd args (Kcall f vm t k) m)
| s_stuck : forall f e k m,
            ~(expr_safe e m) ->
            ssem (ExprState f e k vm m) StuckState
| s_val : forall m k f v t,
          ssem (ExprState f (Val v t) (Kdo k) vm m) (ExprState f (Unit (Ptype Tunit)) k vm m)
| s_internal_fun : forall f vargs k m m' m'',
                   list_norepet (f.(fn_args) ++ f.(fn_vars)) ->
                   alloc_variables empty_vmap m (f.(fn_args) ++ f.(fn_vars)) vm m' -> 
                   bind_variables vm m' f.(fn_args) vargs m'' ->
                   ssem (CallState (Internal f) vargs k m) (ExprState f f.(fn_body) k vm m'').

Definition step (s : state) (s' : state) : Prop :=
ssem s s'.

End Small_step_semantics.


Section Lreduction_Rreduction_Mult.

Variable (ge : genv).
Variable (vm : vmap).

Context (Plred : expr -> Memory.mem -> expr -> Memory.mem -> Prop).
Context (Prred : expr -> Memory.mem -> expr -> Memory.mem -> Prop).
Context (Prreds : list expr -> Memory.mem -> list expr -> Memory.mem -> Prop).
Context (Plrvarl : forall hm x t l, 
                   vm!(x.(vname)) = Some (l, t) ->
                   t = x.(vtype) ->
                   Plred (Var x) hm (Addr {| lname := l; ltype := t; lbitfield := Full |} Ptrofs.zero) hm).
Context (Plrvarg : forall hm x t l,
                   vm!(x.(vname)) = None ->
                   t = x.(vtype) ->
                   Genv.find_symbol ge x.(vname) = Some l ->
                   Plred (Var x) hm (Addr {| lname := l; ltype := t; lbitfield := Full |} Ptrofs.zero) hm).
Context (Plderef : forall hm l ofs tv t,
                   Plred (Prim Deref (Val (Vloc l ofs) tv:: nil) t) hm (Addr {| lname := l; ltype := t; lbitfield := Full |} ofs) hm).
Context (Plderef1 : forall hm e e' t hm',
                    Prred e hm e' hm' ->
                    Plred (Prim Deref [:: e] t) hm  (Prim Deref [:: e'] t) hm').
Context (Prvalof : forall hm e t l ofs bf v,
                   deref_addr (typeof_expr e) hm l ofs bf v ->
                   typeof_expr e = t ->
                   BeeTypes.type_is_volatile t = false ->
                   Prred (Valof (Addr {| lname := l; ltype := t; lbitfield := bf |} ofs) t) hm (Val v t) hm).
Context (Prvalof1 : forall hm e t e' hm',
                    Plred e hm e' hm' ->
                    Prred (Valof e t) hm (Valof e' t) hm').
Context (Prref : forall hm v tv t hm' l, 
                 Mem.alloc hm 0 (sizeof_type tv) = (hm', l) ->
                 assign_addr tv hm' l Ptrofs.zero Full v hm' v ->
                 Prred (Prim Ref [:: (Val v tv)] t) hm (Val (Vloc l Ptrofs.zero) tv) hm').
Context (Prref1 : forall hm e t e' hm', 
                  Prred e hm e' hm' ->
                  Prred (Prim Ref [:: e] t) hm (Prim Ref [:: e] t) hm').
Context (Pruop : forall hm v t ct uop v' v'',
                 transBeePL_type t = ret ct ->
                 sem_unary_operation uop (transBeePL_value_cvalue v) ct hm = Some v' -> 
                 transC_val_bplvalue v' = OK v'' ->
                 Prred (Prim (Uop uop) ((Val v t) :: nil) t) hm (Val v'' t) hm).
Context (Pruop1 : forall hm t uop e e' hm',
                  Prred e hm e' hm' ->
                  Prred (Prim (Uop uop) (e :: nil) t) hm (Prim (Uop uop) (e' :: nil) t) hm').
Context (Prbop : forall hm bop v1 t1 v2 t2 ct1 ct2 t v v',
                 transBeePL_type t1 = ret ct1 ->
                 transBeePL_type t2 = ret ct2 ->
                 sem_binary_operation ge bop (transBeePL_value_cvalue v1) ct1 (transBeePL_value_cvalue v2) ct2 hm = Some v ->
                 transC_val_bplvalue v = OK v' ->
                 Prred (Prim (Bop bop) ((Val v1 t1) :: (Val v2 t2) :: nil) t) hm (Val v' t) hm).
Context (Prbop1 : forall hm t bop e1 e1' e2 hm',
                  Prred e1 hm e1' hm' ->
                  Prred (Prim (Bop bop) (e1 :: e2 :: nil) t) hm (Prim (Bop bop) (e1' :: e2 :: nil) t) hm').
Context (Prbop2 : forall hm bop v1 t1 t e2 e2' hm',
                  Prred e2 hm e2' hm' ->
                  Prred (Prim (Bop bop) ((Val v1 t1) :: e2 :: nil) t) hm (Prim (Bop bop) ((Val v1 t1) :: e2' :: nil) t) hm').
Context (Prcond : forall hm v e1 e2 tv t ctv b, 
                  transBeePL_type tv = ret ctv ->
                  bool_val (transBeePL_value_cvalue v) ctv hm = Some b ->
                  Prred (Cond (Val v tv) e1 e2 t) hm (if b then e1 else e2) hm).
Context (Prcond1 : forall hm e1 e2 e3 t e1' hm', 
                   Prred e1 hm e1' hm' ->
                   Prred (Cond e1 e2 e3 t) hm (Cond e1' e2 e3 t) hm).
Context (Prmassgn : forall hm l ofs v tv2 ct1 ct2 t hm' v' bf,
                    transBeePL_type t = ret ct1 ->
                    transBeePL_type tv2 = ret ct2 ->
                    sem_cast (transBeePL_value_cvalue v) ct2 ct1 hm = Some (transBeePL_value_cvalue v') ->
                    assign_addr t hm l ofs bf v' hm' v' ->
                    Prred (Prim Massgn ((Addr {| lname := l; ltype := t; lbitfield := bf |} ofs) :: Val v tv2 :: nil) t) hm (Val v' t) hm').
Context (Prmassgn1 : forall hm e1 e2 t e1' hm',
                     Prred e1 hm e1' hm' ->
                     Prred (Prim Massgn (e1 :: e2 :: nil) t) hm (Prim Massgn (e1' :: e2 :: nil) t) hm').
Context (Prmassgn2 : forall hm l bf ofs e2 t e2' hm',
                     Prred e2 hm e2' hm' ->
                     Prred (Prim Massgn ((Addr {| lname := l; ltype := t; lbitfield := bf |} ofs) :: e2 :: nil) t) hm 
                            (Prim Massgn ((Addr {| lname := l; ltype := t; lbitfield := bf |} ofs) :: e2' :: nil) t)  hm').
Context (Prbind : forall vm hm x v e2 e2' t t' hm',
                  subst vm hm x v e2 hm' e2' ->
                  Prred (Bind x t (Val v t) e2 t') hm e2' hm').
Context (Prbind1 : forall hm x e1 e2 e1' t t' hm',
                   Prred e1 hm e1' hm' ->
                   Prred (Bind x t e1 e2 t') hm (Bind x t e1' e2 t') hm').
Context (Prapp1 : forall hm e e' hm' es t,
                  Prred e hm e' hm' ->
                  Prred (App e es t) hm (App e' es t) hm').
Context (Prapp2 : forall hm v ts ef rt es hm' es' t,
                  Prreds es hm es' hm' ->
                  Prred (App (Val v (Ftype ts ef rt)) es t) hm (App (Val v (Ftype ts ef rt)) es t) hm').
Context (Prunit : forall hm,
                  Prred (Unit (Ptype Tunit)) hm (Val Vunit (Ptype Tunit)) hm).
Context (Prnil : forall hm, Prreds nil hm nil hm).
Context (Prcons : forall e es hm hm' hm'' e' es', 
                  Prred e hm e' hm' ->
                  Prreds es hm' es' hm'' ->
                  Prreds (e :: es) hm (e' :: es') hm'').

Lemma lreduction_rreduction_rreductions_ind : 
(forall e hm e' hm', lreduction ge vm e hm e' hm' -> Plred e hm e' hm) /\
(forall e hm e' hm', rreduction ge vm e hm e' hm' -> Prred e hm e' hm) /\
(forall es hm es' hm', rreductions ge vm es hm es' hm' -> Prreds es hm es' hm).
Proof.
apply lreduction_rreduction_rreductions_mut=> //=.
Admitted.

End Lreduction_Rreduction_Mult.

(* Whole program semantics *) (* Fix me *)
(* Execution of whole program is defined as sequences of transition from initial state 
   to a final state. An initial state is a CallState corresponding to invocation 
   of the main function of the program *)

               
(*Section Small_step_semantics.

Variable ge : genv. 

Inductive sem_expr : vmap -> Memory.mem -> expr -> Memory.mem -> expr -> Prop :=
| sem_val_unit : forall vm hm,
                 sem_expr vm hm (Val Vunit (Ptype Tunit)) hm (Val Vunit (Ptype Tunit))
| sem_val_int : forall vm hm i t,
                 sem_expr vm hm (Val (Vint i) t) hm (Val (Vint i) t)
| sem_val_int64 : forall vm hm i t,
                  sem_expr vm hm (Val (Vint64 i) t) hm (Val (Vint64 i) t)
| sem_val_loc : forall vm hm t l ofs,
                sem_expr vm hm (Val (Vloc l ofs) t) hm (Val (Vloc l ofs) t)
| sem_var : forall vm hm x t l,
            vm!(x.(vname)) = Some (l, t) ->
            t = x.(vtype) ->
            sem_expr vm hm (Var x) hm 
            (Addr {| lname := l; ltype := t; lbitfield := Full |} Ptrofs.zero)
| sem_gvar : forall vm hm x t l,
             vm!(x.(vname)) = None ->
             t = x.(vtype) ->
             Genv.find_symbol ge x.(vname) = Some l ->
             sem_expr vm hm (Var x) hm 
             (Addr {| lname := l; ltype := t; lbitfield := Full |} Ptrofs.zero)
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
| sem_prim_refv : forall vm hm v tv t ct hm' hm'' l,
                  transBeePL_type tv = OK ct ->
                  Mem.alloc hm 0 (sizeof_type t) = (hm', l) ->
                  assign_addr tv hm' l Ptrofs.zero Full v hm'' v ->
                  sem_expr vm hm (Prim Ref ((Val v tv) :: nil) t) hm'' (Val (Vloc l Ptrofs.zero) t)
| sem_prim_deref : forall vm hm e t hm' e',
                   sem_expr vm hm e hm' e' ->
                   sem_expr vm hm (Prim Deref (e :: nil) t) hm' (Prim Deref (e' :: nil) t)
| sem_prim_derefv : forall vm hm tv t ofs l,
                    sem_expr vm hm (Prim Deref (Val (Vloc l ofs) tv:: nil) t) hm 
                    (Addr {| lname := l; ltype := t; lbitfield := Full |} ofs)
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
              bsem_expr_srvs ge vm1 hm1 es hm2 vs ->
              typeof_values vs (extract_types_vinfos fd.(fn_args)) ->
              bind_variables vm1 hm2 fd.(fn_args) vs hm3  ->
              bsem_expr ge vm1 hm3 fd.(fn_body) hm4 rv ->
              bind_variables vm1 hm4 (r::nil) (rv::nil) hm5 ->
              typeof_value rv (fd.(fn_return)) ->
              sem_expr vm hm (App (Some r.(vname)) (Val v (Ftype ts ef rt)) es t) hm5 (Val rv fd.(fn_return))
| sem_addr : forall vm hm t l bf ofs v,
             deref_addr t hm l ofs bf v ->
             sem_expr vm hm (Addr {| lname := l; ltype := t; lbitfield := bf |} ofs) hm (Val v t).

End Small_step_semantics.*)

