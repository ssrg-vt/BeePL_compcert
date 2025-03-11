Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Globalenvs compcert.lib.Coqlib Ctypes.
Require Import BeePL_aux Axioms Memory Int Cop Memtype Errors Csem SimplExpr Events BeeTypes.
From mathcomp Require Import all_ssreflect. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.

Inductive constant : Type :=
| ConsInt : int -> constant
| ConsLong : int64 -> constant
| ConsUnit : constant.

(*Record vinfo : Type := mkvar { vname : ident; vtype : BeeTypes.basic_type }.*)
Record linfo : Type := mkloc { lname : ident; (*ltype : BeeTypes.basic_type;*) lbitfield : bitfield }.

Inductive value : Type :=
| Vunit : value
| Vint : int -> value
| Vint64 : int64 -> value
| Vloc : positive -> ptrofs -> value.

Definition is_vloc (v : value) : bool :=
match v with 
| Vunit => false
| Vint i => false 
| Vint64 l => false
| Vloc l ofs => true 
end.

(* Pointer will be stores in a 64 bit value or 32 bit value *) 
Definition default_attr (t : type) := {| attr_volatile := false;  
                                         attr_alignas := (attr_alignas (attr_of_type t)) |}.

Definition wtypeof_value (v : value) (t :  BeeTypes.wtype) : Prop :=
match v, t with 
| Vunit, Twuint => True 
| Vint i, BeeTypes.Twint => True 
| Vint64 i, BeeTypes.Twlong => True 
| Vloc p ofs, BeeTypes.Twref => True
| _, _ => False
end.

Definition typeof_value (v : value) (t : type) : Prop :=
match v, t with 
| Vunit, (Ptype Tunit) => True 
| Vint i, Ptype (Tint sz s a) => True 
| Vint64 i, Ptype (Tlong s a) => True 
| Vloc p ofs, Reftype h b a => True (* targeting only 64 bit arch *)
| _, _ => False
end.

Definition vals := list value.

Definition of_int (i : int) : value := Vint i.

Fixpoint wtypeof_values (vs : list value) (ts : list BeeTypes.wtype) : Prop :=
match vs, ts with 
| nil, nil => True
| v :: vs, t :: ts => wtypeof_value v t /\ wtypeof_values vs ts
| _, _ => False
end.

Fixpoint typeof_values (vs : list value) (ts : list BeeTypes.type) : Prop :=
match vs, ts with 
| nil, nil => True
| v :: vs, t :: ts => typeof_value v t /\ typeof_values vs ts
| _, _ => False
end.

(*Fixpoint extract_types_vinfos (vs : list vinfo) : list BeeTypes.basic_type :=
match vs with 
| nil => nil
| v :: vs => v.(vtype) :: extract_types_vinfos vs
end.

Fixpoint extract_types_linfos (vs : list linfo) : list BeeTypes.basic_type :=
match vs with 
| nil => nil
| v :: vs => v.(ltype) :: extract_types_linfos vs
end.

Fixpoint extract_vars_vinfos (vs : list vinfo) : list ident :=
match vs with 
| nil => nil
| v :: vs => v.(vname) :: extract_vars_vinfos vs
end.*)

Fixpoint extract_locs_linfos (vs : list linfo) : list ident :=
match vs with 
| nil => nil
| v :: vs => v.(lname) :: extract_locs_linfos vs
end.

(*Fixpoint extract_list_rvtypes (l : list vinfo) : list (ident * BeeTypes.basic_type) :=
match l with 
| nil => nil
| x :: xs => (x.(vname), x.(vtype)) :: extract_list_rvtypes xs
end.

Definition eq_vinfo (v1 : vinfo) (v2 : vinfo) : bool :=
if (v1.(vname) =? v2.(vname))%positive && (eq_basic_type (vtype v1) (vtype v2)) then true else false.*)

(* add equality over bitfield *)
Definition eq_linfo (v1 : linfo) (v2 : linfo) : bool :=
if (v1.(lname) =? v2.(lname))%positive then true else false.

Inductive builtin : Type :=
| Ref : builtin                             (* allocation : ref t e allocates e of type t 
                                               and returns the fresh address *) (* rvalue *)
| Deref : builtin                           (* dereference : deref t e returns the value of type t 
                                               present at location e *) (* rvalue *)
| Massgn : builtin                          (* assign value at a location l (l := e) 
                                               assigns the evaluation of e to the reference cell l *)
| Uop : Cop.unary_operation -> builtin      (* unary operator *) (* rvalue *)
| Bop : Cop.binary_operation -> builtin     (* binary operator *) (* rvalue *)
| Run : Memory.mem -> builtin               (* eliminate heap effect : [r1-> v1, ..., ern->vn] e 
                                               reduces to e captures the essence of state isolation 
                                               and reduces to a value discarding the heap *).

Record bsignature := { bsig_args : list type; bsig_ef : effect; bsig_res : type; bsig_cc : calling_convention }. 

Definition bsig_to_csig (bsig : bsignature) : mon AST.signature :=
do cts <- (transBeePL_types transBeePL_type bsig.(bsig_args));
do ct <- (transBeePL_type bsig.(bsig_res));
ret {| sig_args :=  (map typ_of_type (from_typelist cts)); sig_res := (rettype_of_type ct); sig_cc := bsig.(bsig_cc) |}.

Inductive external_function : Set :=
| EF_external : string -> bsignature -> external_function.

Definition get_ef_eapp (ef : external_function) : effect :=
match ef with 
| EF_external n sig => sig.(bsig_ef)
end.

Definition befuntion_to_cefunction (bef : external_function) : mon AST.external_function :=
match bef with 
| EF_external n bsig => do aef <- bsig_to_csig bsig;
                        ret (AST.EF_external n aef)
end. 

(* The source language never exposes the heap binding construct hpφ.e directly to the user 
   but during evaluation the reductions on heap operations create heaps and use them. *)
Inductive expr : Type :=
| Val : value -> type -> expr                                           (* value *) (* rvalue *)
| Var : ident -> type -> expr                                                   (* variable *) (* lvalue *)
| Const : constant -> type -> expr                                      (* constant *) (* rvalue *)
| App : expr -> list expr -> type -> expr                               (* function application *) (* rvalue *)
| Prim : builtin -> list expr -> type -> expr                           (* primitive operations *)
| Bind : ident -> type -> expr -> expr -> type -> expr                  (* let binding: type of continuation *)
| Cond : expr -> expr -> expr -> type -> expr                           (* if e then e else e *) 
| Unit : type -> expr                                                   (* unit *)
(* not intended to be written by programmers:
   Only should play role in operational semantics *)
| Addr : linfo -> ptrofs -> type -> expr                                (* address *)
| Hexpr : Memory.mem -> expr -> type -> expr                            (* heap effect *)
| Eapp : external_function -> list type -> list expr -> type -> expr    (* external function *).

(*
      e0 --> None (expr)
      e1 --> v1  
------------------------------- None 
match(e0, e1, x2, e2) --> v1

      e0 --> Some v0 (val v0)
      (subst x2 v0 e2) --> v2
-------------------------------- Some 
match(e0, e1, x2, e2) --> v2 *)
(* Use case for checking null derefencing *)

Definition is_value (e : expr) : bool :=
match e with 
| Val v t => true 
| _ => false
end.

Definition is_pointer (e : expr) : bool :=
match e with 
| Val v t => match v with 
             | Vloc l ofs => true 
             | _ => false
            end
| _ => false
end.
 
Definition typeof_expr (e : expr) : BeeTypes.type :=
match e with 
| Val v t => t
(*| Valof e t => t*)
| Var x t => t
| Const x t => t
| App e ts t => t
| Prim b es t => t
| Bind x t e e' t' => t'
| Cond e e' e'' t => t
| Unit t => t
| Addr l p t => t
| Hexpr h e t => t
| Eapp ef ts es t => t
end.

Fixpoint typeof_exprs (e : list expr) : list BeeTypes.type :=
match e with 
| nil => nil
| e :: es => typeof_expr e :: typeof_exprs es
end.

Record function : Type := mkfunction { (*fn_sec: option string; XDP ==> SEC("xdp") *)
                                       fn_return: type;
                                       fn_effect: effect;
                                       fn_callconv: calling_convention;
                                       fn_args: list (ident * type);
                                       fn_vars: list (ident * type);
                                       fn_body: expr }.

Inductive fundef : Type :=
| Internal : function -> fundef
| External: external_function -> list type -> type -> calling_convention -> fundef.

(** Type of a function definition. **)

Definition type_of_function (f: function) : type :=
  Ftype (unzip2 (fn_args f)) (fn_effect f) (fn_return f).

Definition type_of_fundef (f : fundef) : type :=
match f with 
| Internal f => type_of_function f
| External e ts t cc => Ftype ts (get_ef_eapp e) t
end. 

Definition ef_rtype (ef : external_function) : type :=
match ef with 
| EF_external n sig => sig.(bsig_res)
end.

Definition get_rt_fundef (f : fundef) : type :=
match f with 
| Internal fd => fn_return fd
| External ef ts t cc => ef_rtype ef
end.

Definition get_effect_fundef (f : fundef) : effect :=
match f with 
| Internal fd => fn_effect fd
| External ef ts t cc => get_ef_eapp ef
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

Section Semantics.

Variable (ge : BeePL.genv).

(* Executable definition of volatile_load (events.v) *)
(*Definition volatile_load (chunk: memory_chunk) (m: mem) (b: Values.block) (ofs: ptrofs) : val :=
if Senv.block_is_volatile ge b then
match Senv.find_symbol ge b with
| Some id =>
        (* Assume some function eventval_match_eval that computes the eventval *)
        let ev := eventval_match_eval ge (type_of_chunk chunk) in
        (Event_vload chunk id ofs ev :: nil, Val.load_result chunk ev)
    | None => (E0, Vundef)  (* If the symbol lookup fails, return empty trace and undefined value *)
    end
  else
    match Mem.load chunk m b (Ptrofs.unsigned ofs) with
    | Some v => (E0, v)
    | None => (E0, Vundef)
    end.*)

(* [deref_addr ty m addr ofs] computes the value of type [ty] residing in 
    memory [m] at address [addr], offset [ofs] and bitfield designation [bf]:
    if the access mode is by value then the value is returned by performing memory load 
    if the access mode is by reference then the pointer [Vloc addr ofs] is returned *)
(* Add rest like copy, bitfield, volatile, etc once we add arrays and structs *) 
Inductive deref_addr (ty : type) (m : Memory.mem) (addr : Values.block) (ofs : ptrofs) : bitfield -> value -> Prop :=
| deref_addr_value : forall chunk v v',
  access_mode ty = By_value (transl_bchunk_cchunk chunk) ->
  type_is_volatile ty = false ->
  Mem.loadv (transl_bchunk_cchunk chunk) m (transBeePL_value_cvalue (Vloc addr ofs)) = Some v ->
  transC_val_bplvalue v = OK v' ->
  deref_addr ty m addr ofs Full v'
| deref_loc_volatile: forall chunk tr v v',
  access_mode ty = By_value (transl_bchunk_cchunk chunk) -> 
  type_is_volatile ty = true ->
  volatile_load ge (transl_bchunk_cchunk chunk) m addr ofs tr v ->
  transC_val_bplvalue v = OK v' ->
  deref_addr ty m addr ofs Full v'
| deref_addr_reference:
  access_mode ty = By_reference ->
  deref_addr ty m addr ofs Full (Vloc addr ofs). 

(* Executable definition for deref_addr 
Fixpoint deref_addr (t : type) (m : Memory.mem) (addr : Values.block) (ofs : ptrofs) : mon (bitfield * value) :=
match access_mode ty with 
| By_value (transl_bchunk_cchunk chunk) => if (type_is_volatile ty) 
                                           then  
                             
if (type_is_volatile ty) && (access_mode ty == By_value (transl_bchunk_cchunk chunk)) 
then match Mem.loadv (transl_bchunk_cchunk chunk) m (transBeePL_value_cvalue (Vloc addr ofs)) with 
     | Some v => match (transC_val_bplvalue v) with 
                 | Res v' g i => OK (Full, v')
                 | None => Error msg 
     | None => Error msg 
else if deref_addr t m addr ofs
else *)

(* [assign_addr ty m addr ofs v] returns the updated memory after storing the value v at address [addr] and offset 
   [ofs] *)
Inductive assign_addr (ty : type) (m : Memory.mem) (addr : Values.block) (ofs : ptrofs) : bitfield -> value -> Memory.mem -> value -> Prop :=
| assign_addr_value : forall v chunk m' v',
  access_mode ty = By_value (transl_bchunk_cchunk chunk) ->
  type_is_volatile ty = false ->
  Mem.storev (transl_bchunk_cchunk chunk) m (transBeePL_value_cvalue (Vloc addr ofs)) v = Some m' ->
  transC_val_bplvalue v = OK v' ->
  assign_addr ty m addr ofs Full v' m' v'
| assign_loc_volatile: forall v chunk tr m' v',
  access_mode ty = By_value (transl_bchunk_cchunk chunk) -> type_is_volatile ty = true ->
  volatile_store ge (transl_bchunk_cchunk chunk) m addr ofs v tr m' ->
  transC_val_bplvalue v = OK v' ->
  assign_addr ty m addr ofs Full v' m' v'. 

(* Allocation of function local variables *)
(* [alloc_variables vm1 m1 vars vm2 m2] allocates one memory block for each variable
   declared in [vars], and associates the variable name with this block. 
   [vm1] and [m1] are the initial local environment and memory state.
   [e2] and [m2] are the final local environment and memory state *) 
Inductive alloc_variables : vmap -> Memory.mem -> list (ident * type) -> vmap -> Memory.mem -> Prop :=
| alloc_variables_nil : forall vm hm, 
  alloc_variables vm hm nil vm hm
| alloc_variables_con : forall e m id ty vars m1 l1 m2 e2,
  Mem.alloc m 0 (sizeof_type ty) = (m1, l1) ->
  alloc_variables (PTree.set id (l1, ty) e) m1 vars e2 m2 ->
  alloc_variables e m ((id, ty) :: vars) e2 m2.

(** Initialization of local variables that are parameters to a function.
  [bind_parameters e m1 params args m2] stores the values [args]
  in the memory blocks corresponding to the variables [params].
  [m1] is the initial memory state and [m2] the final memory state. **)
Inductive bind_variables  (e: vmap): Memory.mem -> list (ident * type) -> list value -> Memory.mem -> Prop :=
| bind_variables_nil: forall m,
  bind_variables e m nil nil m
| bind_variables_cons: forall m id ty params v1 vl v1' b m1 m2,
  PTree.get id e = Some(b, ty) ->
  assign_addr ty m b Ptrofs.zero Full v1 m1 v1' ->
  bind_variables e m1 params vl m2 ->
  bind_variables e m ((id, ty) :: params) (v1 :: vl) m2.

(** Return the list of blocks in the codomain of [benv], with low and high bounds. **)

Definition block_of_binding (id_b_ty: ident * (positive * BeeTypes.type)) :=
  match id_b_ty with (id, (b, ty)) => (b, 0, sizeof_type ty) end.

Definition blocks_of_env (e: vmap) : list (ident * Z * Z) :=
  List.map block_of_binding (PTree.elements e).

(* Substitution *)
Fixpoint subst (x : ident) (se : expr) (e : expr) {struct e} : expr :=
match e with 
| Val v t => e
| Var y t => if (x =? y)%positive then se else Var y t
| Const c t => e 
| App e es t => App (subst x se e) (map (subst x se) es) t
| Prim b es t => Prim b (map (subst x se) es) t
| Bind y t e1 e2 t' => if (x =? y)%positive 
                       then Bind y t (subst x se e1) e2 t'
                       else Bind y t (subst x se e1) (subst x se e2) t'
| Cond e1 e2 e3 t => Cond (subst x se e1) (subst x se e2) (subst x se e3) t
| Unit t => Unit t 
| Addr l p t => Addr l p t
| Hexpr h e t => Hexpr h (subst x se e) t
| Eapp ef ts es t => Eapp ef ts (map (subst x se) es) t
end.

(*Inductive subst : ident -> expr -> expr -> expr -> Prop :=
| val_subst : forall x se v t,
              subst x se (Val v t) (Val v t)
| var_subst1 : forall x se y t,
               (x =? y)%positive = true ->
               subst x se (Var y t) se
| var_subst2 : forall x se y t,
               (x =? y)%positive = false -> 
               subst x se (Var y t) (Var y t)
| const_subst : forall x se c t,
                subst x se (Const c t) (Const c t)
| app_subst : forall x se e e' es es' t,
              subst x se e e' ->
              substs x se es es' ->
              subst x se (App e es t) (App e' es' t)
| prim_subst : forall b x se es t es',
               substs x se es es' ->
               subst x se (Prim b es t) (Prim b es' t)
| bind_subst1 : forall x se y t e1 e1' e2 t', 
                (* x is shadowed in e2: new variable binding hides older one *)
                (x =? y)%positive = true ->
                subst x se e1 e1' ->
                subst x se (Bind y t e1 e2 t') (Bind y t e1' e2 t')
| bind_subst2 : forall x se y t e1 e2 t' e1' e2',
                (x =? y)%positive = false ->
                subst x se e1 e1' ->
                subst x se (Bind y t e1 e2 t') (Bind y t e1' e2' t')
| cond_subst : forall x se e1 e1' e2 e2' e3 e3' t,
               subst x se e1 e1' ->
               subst x se e2 e2' ->
               subst x se e3 e3' ->
               subst x se (Cond e1 e2 e3 t) (Cond e1' e2' e3' t)
| unit_subst : forall x se,
               subst x se (Unit (Ptype Tunit)) (Unit (Ptype Tunit))
| addr_subst : forall x se l p t,
               subst x se (Addr l p t) (Addr l p t)
| hexpr_subst : forall x se h e t e', 
                subst x se e e' ->
                subst x se (Hexpr h e t) (Hexpr h e' t)
| eapp_subst : forall x se ef ts t es es',
               substs x se es es' ->
               subst x se (Eapp ef ts es t) (Eapp ef ts es' t)
with substs : ident -> expr -> list expr -> list expr -> Prop :=
| substs_nil : forall x e, 
               substs x e nil nil
| substs_cons : forall x se e es e' es',
                subst x se e e' ->
                substs x se es es' -> 
                substs x se (e :: es) (e' :: es').

Scheme subst_ind_mut := Induction for subst Sort Prop
  with substs_ind_mut := Induction for substs Sort Prop.
Combined Scheme substs_subst_ind_mut from substs_ind_mut, subst_ind_mut.*)

Fixpoint is_simple_expr (e : expr) : bool :=
match e with 
| Val v t => true 
| Var v t => true 
| Const c t => true
| App e es t => false 
| Prim o es t => match o with 
                 | Ref => match es with 
                          | [:: e] => is_simple_expr e
                          | _ => false
                          end
                 | Deref => match es with 
                            | [:: e] => is_simple_expr e
                            | _ => false
                            end
                 | Massgn => false
                 | Uop o => match es with 
                            | [:: e] => is_simple_expr e
                            |  _ => false
                            end
                 | Bop o => match es with 
                            | [:: e1; e2] => is_simple_expr e1 && is_simple_expr e2
                            | _ => false
                            end
                 | Run h => false 
                 end
| Bind x t e e' t' => false
| Cond e1 e2 e3 t => false 
| Unit t => true 
| Addr l ofs t => true 
| Hexpr m e t => false
| Eapp ef ts es t => false
end.

Inductive well_formed_value : value -> type -> Prop :=
| wf_vunit : well_formed_value Vunit (Ptype Tunit)
| wf_vint : forall sz s a i, 
            well_formed_value (Vint i) (Ptype (Tint sz s a))
| wf_vlong : forall s a i,
             well_formed_value (Vint64 i) (Ptype (Tlong s a))
| wf_vloc : forall l ofs h t a,
            well_formed_value (Vloc l ofs) (Reftype h t a).

Section Simpl_big_step_semantics.

Variable (vm : vmap).


(* Would be useful in proving equivalence with Cstrategy for simpl expressions *)
(* Simple expressions have interesting properties: their evaluations always
   terminate, and preserve the memory state.
   We seize this opportunity to define a big-step semantics for simple
   expressions. *) 
Inductive bsem_expr_slv : Memory.mem -> expr -> linfo -> ptrofs -> Prop :=
| bsem_var : forall hm x t l h t' a, 
              vm!x = Some (l, Reftype h t' a) ->
              t = Reftype h t' a ->
              bsem_expr_slv hm (Var x t) {| lname := l; lbitfield := Full |} Ptrofs.zero
| bsem_gvar : forall hm x t l h t' a, 
              vm!x = None ->
              Genv.find_symbol ge x = Some l ->
              t = Reftype h (Bprim t') a ->
              bsem_expr_slv hm (Var x t) {| lname := l; lbitfield := Full |} Ptrofs.zero
| bsem_addr : forall hm l ofs t,
              bsem_expr_slv hm (Addr l ofs t) l ofs.
Inductive bsem_expr_srv : Memory.mem -> expr -> value -> Prop :=
| bsem_val : forall hm v t,
             well_formed_value v t ->
             bsem_expr_srv hm (Val v t) v
| bsem_prim_deref : forall hm e t l ofs v,
                    bsem_expr_slv hm e l ofs ->
                    deref_addr (typeof_expr e) hm l.(lname) ofs l.(lbitfield) v ->
                    typeof_expr e = t ->
                    BeeTypes.type_is_volatile t = false ->
                    bsem_expr_srv hm (Prim Deref (e :: nil) t) v
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
                  t = (typeof_expr e1) /\ t = (typeof_expr e2) ->
                  sem_binary_operation ge bop (transBeePL_value_cvalue v1) ct1 (transBeePL_value_cvalue v2) ct2 hm = Some v ->
                  transC_val_bplvalue v = OK v' ->
                  bsem_expr_srv hm (Prim (Bop bop) (e1 :: e2 :: nil) t) v'
| bsem_unit : forall hm, 
              bsem_expr_srv hm (Unit (Ptype Tunit)) Vunit.


Inductive bsem_expr_srvs : Memory.mem -> list expr -> list value -> Prop :=
| bsem_expr_srv_nil : forall hm, 
                      bsem_expr_srvs hm nil nil
| bsem_expr_srv_cons : forall hm e es v vs,
                       bsem_expr_srv hm e v ->
                       bsem_expr_srvs hm es vs ->
                       bsem_expr_srvs hm (e :: es) (v :: vs).

End Simpl_big_step_semantics.

(* Left reduction context *) 
(* These contexts allow reducing to the right of a binary operator only if the 
   left subexpression is simple (terminated and reduced to its value *)
Inductive leftcontext : kind -> kind -> (expr -> expr) -> Prop :=
| lctx_top : forall k,
             leftcontext k k (fun x => x)
| lctx_prim_ref : forall k C t,
                  leftcontext k RV C ->
                  leftcontext k RV (fun x => Prim Ref [:: (C x)] t)
| lctx_prim_deref : forall k C t,
                    leftcontext k RV C ->
                    leftcontext k RV (fun x => Prim Deref [:: (C x)] t)
| lctx_prim_massgn_left : forall k C e2 t, 
                          leftcontext k LV C ->
                          leftcontext k RV (fun x => Prim Massgn ((C x) :: e2) t) 
| lctx_prim_massgn_right : forall k C e1 t, 
                           is_simple_expr e1 = true ->
                           leftcontext k RV (fun x => Prim Massgn (e1 :: (C x)) t)
| lctx_prim_unop: forall k C op ty,
                  leftcontext k RV C -> 
                  leftcontext k RV (fun x => Prim (Uop op) [:: (C x)] ty)
| lctx_binop_left: forall k C op e2 ty,
                   leftcontext k RV C -> 
                   leftcontext k RV (fun x => Prim (Bop op) ((C x) :: e2) ty)
| lctx_binop_right: forall k C op e1 ty,
                    is_simple_expr e1 = true -> 
                    leftcontext k RV C ->
                    leftcontext k RV (fun x => Prim (Bop op) (e1 :: (C x) :: nil) ty)
| lctx_bind_left : forall k C x' e2 tx' ty,
                   leftcontext k RV C ->
                   leftcontext k RV (fun x => Bind x' tx' (C x) e2 ty)
| lctx_bind_right : forall k C x' tx' e1 ty,
                    is_simple_expr e1 = true ->
                    leftcontext k RV C ->
                    leftcontext k RV (fun x => Bind x' tx' e1 (C x) ty)
| lctx_condition: forall k C e2 e3 ty,
                  leftcontext k RV C -> 
                  leftcontext k RV (fun x => Cond (C x) e2 e3 ty)
(* fix me for run *)
| lctx_call_left: forall k C el ty,
                  leftcontext k RV C -> leftcontext k RV (fun x => App (C x) el ty)
| lctx_call_right: forall k C e1 ty,
                   is_simple_expr e1 = true -> leftcontextlist k C ->
                   leftcontext k RV (fun x => App e1 (C x) ty)
| lctx_eapp: forall k C ef ts ty,
             leftcontextlist k C ->
             leftcontext k RV (fun x => Eapp ef ts (C x) ty)
(* fix me for hexpr *)
with leftcontextlist: kind -> (expr -> list expr) -> Prop :=
  | lctx_list_head: forall k C el,
      leftcontext k RV C -> leftcontextlist k (fun x => (C x) :: el)
  | lctx_list_tail: forall k C e1,
      is_simple_expr e1 = true -> leftcontextlist k C ->
      leftcontextlist k (fun x => e1 :: (C x)).

Scheme leftcontext_ind2 := Minimality for leftcontext Sort Prop
  with leftcontextlist_ind2 := Minimality for leftcontextlist Sort Prop.
Combined Scheme leftcontext_leftcontextlist_ind from leftcontext_ind2, leftcontextlist_ind2.


(* Continuation describe the computations that remain to be performed 
   after the expression under consideration has evaluated completely *)
Inductive cont: Type :=
| Kstop : cont 
| Kdo : cont -> cont            (* after [x] in [x;] *)
| Kcond : expr -> expr -> cont -> cont (* after [x] in if {x} {e1} {e2} *)
| Kcall : function ->           (* calling function *)
          vmap ->               (* local env of calling function *)
          (*(expr -> expr) -> *)    (**r context of the call *)
          type ->               (* type of call expression *)
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
| FinalState (res : value)
             (m : Memory.mem) : state (* final state after execution of the function *)
| StuckState                          (* undefined behvaior occured *).

Definition is_ExprState (s : state) : bool :=
match s with 
| ExprState f e k vm m => true
| CallState fd args k m => false
| FinalState v m => false
| StuckState => false
end.

Definition extract_expr_st (s : state) : option expr := 
match s with 
| ExprState f e k vm m => Some e 
| _ => None
end.

(** Strategy for reducing expressions. We reduce the leftmost innermost
    non-simple subexpression, evaluating its arguments (which are necessarily
    simple expressions) with the big-step semantics.
    If there are none, the whole expression is simple and is evaluated in one big step. *)
Inductive bestep : state -> state -> Prop :=
| step_expr : forall vm f e t k m v, 
              bsem_expr_srv vm m e v -> 
              match e with Val _ _ => False | _ => True end ->
              typeof_expr e = t ->
              bestep (ExprState f e k vm m) (ExprState f (Val v t) k vm m)
| step_consti : forall f i t k vm m,
                bestep (ExprState f (Const (ConsInt i) t) k vm m) (FinalState (Vint i) m)
| step_constl : forall f i t k vm m,
                bestep (ExprState f (Const (ConsLong i) t) k vm m) (FinalState (Vint64 i) m)
| step_constu : forall f k vm m,
                bestep (ExprState f (Const ConsUnit (Ptype Tunit)) k vm m) (FinalState Vunit m)
| step_deref_volatile : forall vm f e t k m l ofs v, 
                        (*leftcontext RV RV C ->*)
                        bsem_expr_slv vm m e l ofs ->
                        deref_addr (typeof_expr e) m l.(lname) ofs l.(lbitfield) v ->
                        typeof_expr e = t ->
                        BeeTypes.type_is_volatile t = true ->
                        bestep (ExprState f (Prim Deref (e :: nil) t) k vm m) (ExprState f (Val v t) k vm m)
| step_prim_ref : forall vm f k e v fid t m m' l ofs ct g g' i', 
                  (*leftcontext RV RV C ->*)
                  bsem_expr_srv vm m e v ->
                  transBeePL_type t g = Res ct g' i' ->
                  (gensym ct) = ret fid ->
                  bind_variables vm m ((fid, t) :: nil) (v :: nil) m' ->
                  bsem_expr_slv vm m' (Var fid t) l ofs -> 
                  bestep (ExprState f (Prim Ref [:: e] t) k vm m) 
                         (ExprState f (Val (Vloc l.(lname) ofs) t) k vm m') 
| step_prim_massgn : forall vm f k e1 e2 t ct1 ct2 l ofs m v g1 g2 g3 i i' v' m', 
                     (*leftcontext RV RV C ->*)
                     bsem_expr_slv vm m e1 l ofs ->
                     bsem_expr_srv vm m e2 v ->
                     transBeePL_type (typeof_expr e1) g1 = Res ct1 g2 i ->
                     transBeePL_type (typeof_expr e2) g2 = Res ct2 g3 i' ->
                     sem_cast (transBeePL_value_cvalue v) ct2 ct1 m = Some (transBeePL_value_cvalue v') ->
                     assign_addr (typeof_expr e1) m l.(lname) ofs l.(lbitfield) v' m' v' -> 
                     typeof_expr e1 = t ->
                     bestep (ExprState f (Prim Massgn (e1 :: e2 :: nil) t) k vm m)
                            (ExprState f (Val v' t) k vm m')
| step_bind : forall vm f k x tx e1 v e2 e2' t m m' v',
              (*leftcontext RV RV C ->*)
              bsem_expr_srv vm m e1 v -> 
              subst x (Val v t) e2 = e2' ->
              bestep (ExprState f e2' k vm m) (ExprState f (Val v' t) k vm m') ->
              bestep (ExprState f (Bind x tx e1 e2 t) k vm m)
                     (ExprState f (Val v' t) k vm m')
| step_condition : forall vm f e1 e2 e3 vb t k m b ct1 g g' i,
                   (*leftcontext RV RV C ->*)
                   bsem_expr_srv vm m e1 vb -> 
                   transBeePL_type (typeof_expr e1) g = Res ct1 g' i ->
                   bool_val (transBeePL_value_cvalue vb) ct1 m = Some true ->
                   bestep (ExprState f (Cond e1 e2 e3 t) k vm m)
                          (ExprState f (if b then e2 else e3) k vm m)
| step_call : forall vm m f k e es t l vs fd,
              (*leftcontext RV RV C ->*)
              bsem_expr_srv vm m e (Vloc l Ptrofs.zero) ->
              bsem_expr_srvs vm m es vs ->
              Genv.find_funct ge (transBeePL_value_cvalue (Vloc l Ptrofs.zero)) = Some fd ->
              type_of_fundef fd = Ftype (typeof_exprs es) (get_effect_fundef fd) (get_rt_fundef fd) -> 
              bestep (ExprState f (App e es t) k vm m) 
                     (CallState fd vs (Kcall f vm t k) m)
| step_internal_fun : forall vm f vargs k m m' m'',
                      list_norepet (f.(fn_args) ++ f.(fn_vars)) ->
                      alloc_variables empty_vmap m (f.(fn_args) ++ f.(fn_vars)) vm m' -> 
                      bind_variables vm m' f.(fn_args) vargs m'' ->
                      bestep (CallState (Internal f) vargs k m) (ExprState f f.(fn_body) k vm m'')
| step_final : forall vm f v t m m' k,
               (*leftcontext RV RV C ->*)
               (* free all the memory assigned to variables in a function *)
               Mem.free_list m (blocks_of_env vm) = Some m' ->
               bestep (ExprState f (Val v t) k vm m) (FinalState v m')
| step_external_fun : forall vm f ef ts es ty k e m vs t vres m' cef g g' i' bv,
                      (*leftcontext RV RV C ->*)
                      bsem_expr_srvs vm m es vs ->
                      befuntion_to_cefunction ef g = Res cef g' i' ->
                      external_call cef ge (transBeePL_values_cvalues vs) m t vres m' ->
                      transC_val_bplvalue vres = OK bv ->
                      bestep (ExprState f (Eapp ef ts es ty) k e m)
                             (ExprState f (Val bv ty) k e m').

Definition bstep (S: state) (S': state) : Prop := bestep S S'. 

End Semantics.
            
(** Whole program semantics **)

(** Execution of whole program are described as sequences of transitions 
    from an initial state to a final state. An initial state is a [Callstate] corresponding
    to the invocation of the main function of the program without arguments and with an empty continuation **)

Inductive initial_state (p : program): state -> Prop :=
| initial_state_intro: forall b f m0,  let bge := globalenv p in 
  Genv.alloc_globals (BeePL.globalenv p) Mem.empty (BeePL.prog_defs p) = Some m0 ->
  Genv.find_symbol bge p.(prog_main) = Some b ->
  Genv.find_funct_ptr bge b = Some f ->
  type_of_fundef f = Ftype nil (get_effect_fundef f) (get_rt_fundef f) ->
  initial_state p (CallState f nil Kstop m0).
 
(** A final state is a ExprState with value as expression and empty continuation **) 
Inductive final_state : state -> Prop :=
| final_state_intro : forall v m,
  final_state (FinalState v m).

(** Safe execution **)

(** A state is safe if it cannot get stuck by doing any transition - 
    Either it reaches a final state or it takes step **)
Definition safe (bge : genv) (s : state) : Prop :=
final_state s \/ exists s', bstep bge s s'.

(** Transition semantics **)

(** The general form of a transition semantics. **)

Record semantics : Type := Semantics_gen {
  fstep : genv -> state -> state -> Prop;
  finitial_state: state -> Prop;  ffinal_state: state -> Prop;
  fglobalenv: genv;
  fsymbolenv: Senv.t
}.

Definition beepl_semantics (p : program) :=
{| fstep := bstep ;
   finitial_state := (initial_state p);
   ffinal_state := final_state;
   fglobalenv := BeePL.globalenv p;
   fsymbolenv := BeePL.globalenv p |}.

(*Section Bsem_expr_srv_ind.

Context (Plv : Memory.mem -> expr -> linfo -> ptrofs -> Prop).
Context (Prv : Memory.mem -> expr -> value -> Prop).
Context (Plvar : forall vm hm x t l h a, 
                 vm!(x.(vname)) = Some (l, Reftype h (Bprim t) a) ->
                 x.(vtype) = Reftype h (Bprim t) a ->
                 Plv hm (Var x) {| lname := l; ltype := Reftype h (Bprim t) a; lbitfield := Full |} Ptrofs.zero).
Context (Pgvar : forall vm hm x t l h a,
                 vm!(x.(vname)) = None ->
                 Genv.find_symbol ge x.(vname) = Some l ->
                 x.(vtype) = Reftype h (Bprim t) a ->
                 Plv hm (Var x) {| lname := l; ltype := Reftype h (Bprim t) a; lbitfield := Full |} Ptrofs.zero).
Context (Paddr : forall hm l ofs,
                 Plv hm (Addr l ofs) l ofs).
Context (Pval : forall hm v t,
                 Prv hm (Val v t) v).
Context (Pci : forall hm i t, 
               Prv hm (Const (ConsInt i) t) (Vint i)).
Context (Pcl : forall hm i t, 
               Prv hm (Const (ConsLong i) t) (Vint64 i)).
Context (Pcu : forall hm, 
               Prv hm (Const (ConsUnit) (Ptype Tunit)) Vunit).
Context (Pderef : forall hm e t l ofs v,
                  Plv hm e l ofs ->
                  deref_addr (typeof_expr e) hm l.(lname) ofs l.(lbitfield) v ->
                  typeof_expr e = t ->
                  BeeTypes.type_is_volatile t = false ->
                  Prv hm (Prim Deref (e :: nil) t) v).
Context (Puop : forall hm e v uop  v' t ct v'' g g' i,
                bsem_expr_srv ge vm hm e v ->
                Prv hm e v ->
                transBeePL_type (typeof_expr e) g = Res ct g' i ->
                t = (typeof_expr e) ->
                sem_unary_operation uop (transBeePL_value_cvalue v) ct hm = Some v' ->
                transC_val_bplvalue v' = OK v'' ->
                Prv hm (Prim (Uop uop) (e :: nil) t) v'').
Context (Pbop : forall hm e1 e2 t v1 v2 bop v ct1 ct2 v' g g' g'' i i',
                bsem_expr_srv ge vm hm e1 v1 ->
                Prv hm e1 v1 ->
                bsem_expr_srv ge vm hm e2 v2 ->
                Prv hm e2 v2 ->
                transBeePL_type (typeof_expr e1) g = Res ct1 g' i ->
                transBeePL_type (typeof_expr e2) g' = Res ct2 g'' i'->
                t = (typeof_expr e1) /\ t = (typeof_expr e2) ->
                sem_binary_operation ge bop (transBeePL_value_cvalue v1) ct1 (transBeePL_value_cvalue v2) ct2 hm = Some v ->
                transC_val_bplvalue v = OK v' ->
                Prv hm (Prim (Bop bop) (e1 :: e2 :: nil) t) v').
Context (Punit : forall hm, 
                 Prv hm (Unit (Ptype Tunit)) Vunit).


Lemma bsem_expr_rlv_ind : forall hm e v, 
bsem_expr_srv hm e v -> Prv hm e v.
Proof.
move=> m e v hr. induction hr=> //=. 
+ apply Pderef with l ofs; auto. inversion H; subst.
  + by apply Plvar.
  + by apply Pgvar.
  by apply Paddr.
+ by apply Puop with v v' ct g g' i; auto.
+ by apply Pbop with v1 v2 v ct1 ct2 g g' g'' i i'.
Qed.

End Bsem_expr_srv_ind.*)

Section Small_step_semantics.
Variable (ge : genv).
Variable (vm : vmap).

Inductive lreduction : expr -> Memory.mem -> expr -> Memory.mem -> Prop :=
| lred_var_local : forall hm x t l h t' a,
                   vm!x = Some (l, Reftype h (Bprim t') a) ->
                   t = Reftype h (Bprim t') a ->
                   lreduction (Var x t) hm (Addr {| lname := l; lbitfield := Full |} 
                                            Ptrofs.zero (Reftype h (Bprim t') a)) hm
| lred_var_global : forall hm x t l h t' a,
                    vm!x = None ->
                    t = Reftype h (Bprim t') a ->
                    Genv.find_symbol ge x = Some l ->
                    lreduction (Var x t) hm (Addr {| lname := l; lbitfield := Full |} Ptrofs.zero 
                                             (Reftype h (Bprim t') a)) hm.

Inductive rreduction : expr -> Memory.mem -> expr -> Memory.mem -> Prop :=
| rred_valof : forall hm t l ofs bf v h a,
               deref_addr ge (Ptype t) hm l ofs bf v ->
               BeeTypes.type_is_volatile (Ptype t) = false ->
               rreduction (Prim Deref ((Addr {| lname := l; lbitfield := bf |} ofs (Reftype h (Bprim t) a)) :: nil) (Ptype t)) hm 
               (Val v (Ptype t)) hm
| rred_ref : forall hm t g ct g' i' fid hm' v l ofs h a, 
             transBeePL_type (Ptype t) g = Res ct g' i' ->
             (gensym ct) = ret fid ->
             bind_variables ge vm hm ((fid, (Ptype t)) :: nil) (v :: nil) hm' ->
             lreduction (Var fid (Ptype t)) hm' 
                        (Addr {| lname := l; lbitfield := Full |} Ptrofs.zero (Reftype h (Bprim t) a)) ofs -> 
             rreduction (Prim Ref [:: (Val v (Ptype t))] (Ptype t)) hm 
                        (Addr {| lname := l; lbitfield :=  Full|} Ptrofs.zero (Reftype h (Bprim t) a)) hm'
| rred_uop : forall hm v t ct uop v' v'' g g' i',
             transBeePL_type t g = Res ct g' i' ->
             sem_unary_operation uop (transBeePL_value_cvalue v) ct hm = Some v' -> 
             transC_val_bplvalue v' = OK v'' ->
             rreduction (Prim (Uop uop) ((Val v t) :: nil) t) hm (Val v'' t) hm
| rred_bop : forall hm bop v1 t1 v2 t2 ct1 ct2 t v v' g g' g'' i' i'',
             transBeePL_type t1 g =  Res ct1 g' i' ->
             transBeePL_type t2 g' = Res ct2 g'' i'' ->
             sem_binary_operation ge bop (transBeePL_value_cvalue v1) ct1 (transBeePL_value_cvalue v2) ct2 hm = Some v ->
             transC_val_bplvalue v = OK v' ->
             rreduction (Prim (Bop bop) ((Val v1 t1) :: (Val v2 t2) :: nil) t) hm (Val v' t) hm
| rred_cond : forall hm v e1 e2 tv t ctv b g g' i', 
              transBeePL_type tv g = Res ctv g' i' ->
              bool_val (transBeePL_value_cvalue v) ctv hm = Some b ->
              rreduction (Cond (Val v tv) e1 e2 t) hm (if b then e1 else e2) hm
| rred_massgn : forall hm l ofs v tv2 ct1 ct2 t hm' v' bf g g' g'' i' i'' h a,
                transBeePL_type (Ptype t) g = Res ct1 g' i' ->
                transBeePL_type (Ptype tv2) g' = Res ct2 g'' i''->
                sem_cast (transBeePL_value_cvalue v) ct2 ct1 hm = Some (transBeePL_value_cvalue v') ->
                assign_addr ge (Ptype t) hm l ofs bf v' hm' v' ->
                rreduction (Prim Massgn ((Addr {| lname := l; lbitfield := bf |} ofs (Reftype h (Bprim t) a)) 
                                         :: Val v (Ptype tv2) :: nil) (Ptype t)) hm (Val v' (Ptype t)) hm'
| rred_bind : forall hm x v e2 t t',
              rreduction (Bind x t (Val v t) e2 t') hm (subst x (Val v t) e2) hm
| rred_unit : forall hm,
              rreduction (Unit (Ptype Tunit)) hm (Val Vunit (Ptype Tunit)) hm.

 
Inductive is_list_val : list expr -> list value -> Prop :=
  | is_args_nil:
      is_list_val nil nil
  | is_args_cons: forall v ty vs vs',
      is_list_val vs vs' ->
      is_list_val (Val v ty :: vs) (v :: vs'). 

Inductive callreduction : expr -> Memory.mem -> fundef -> list value -> type -> Prop :=
| red_call : forall hm v fd ts rt vargs vargs' t ef, 
             Genv.find_funct ge (transBeePL_value_cvalue v) = Some (Internal fd) ->
             type_of_fundef (Internal fd) = (Ftype ts ef rt) ->
             is_list_val vargs vargs' ->
             callreduction (App (Val v (Ftype ts ef rt)) vargs t) hm (Internal fd) vargs' t.
  
(* Reduction contexts *)

Inductive context : kind -> kind -> (expr -> expr) -> Prop :=
| ctx_top : forall k,
            context k k (fun x => x)
(* Ref e t, where e is evaluated at RV position *)
| ctx_ref : forall k C t,
            context k RV C ->
            context k RV (fun x => Prim Ref [:: C x] t)
(* Deref e t, where e is evaluated at RV position, but deref is evaluated in LV *)
| ctx_deref : forall k C t,
              context k RV C ->
              context k LV (fun x => Prim Deref [:: C x] t)
(* e1 := e2, evaluates in two rules *)
| ctx_massgn1 : forall k C t e2, 
                context k LV C ->
                context k RV (fun x => Prim Massgn (C x :: e2 :: nil) t)
| ctx_massgn2 : forall k C t e1,
                context k RV C ->
                context k RV (fun x => Prim Massgn (e1 :: C x :: nil) t)
(* uop(e), where e is evaluated at RV position *)
| ctx_uop : forall k C t o,
            context k RV C ->
            context k RV (fun x => Prim (Uop o) [:: (C x)] t)
(* bop(e1,e2), where e1 is evaluated at RV in first rule and e2 is evaluated at RV in second rule *)
| ctx_bop1 : forall k C t o e2,
             context k RV C ->
             context k RV (fun x => Prim (Bop o) ((C x) :: e2 :: nil) t)
| ctx_bop2 : forall k C t o e1,
             context k RV C ->
             context k RV (fun x => Prim (Bop o) (e1 :: (C x) :: nil) t)
| ctx_cond : forall k C t e2 e3,
             context k RV C ->
             context k RV (fun x => Cond (C x) e2 e3 t)
| ctx_bind : forall k C t r t' e,
             context k RV C ->
             context k RV (fun x => Bind r t' (C x) e t)
| ctx_app1 : forall k C t es,
             context k RV C ->
             context k RV (fun x => App (C x) es t)
| ctx_app2 : forall k C t e,
             contexts k C ->
             context k RV (fun x => App e (C x) t)
| ctx_eapp : forall k C ef ts t,
             contexts k C ->
             context k RV (fun x => Eapp ef ts (C x) t)  
(* fix me : add the case for hexpr *)
with contexts : kind -> (expr -> list expr) -> Prop :=
| ctx_hd : forall k C el,
           context k RV C ->
           contexts k (fun x => (C x) :: el)
| ctx_tl : forall k C e1,
           contexts k C ->
           contexts k (fun x => e1 :: (C x)).
              
(* Relation representing safe execution of expressions *)
Inductive expr_safe : kind -> expr -> Memory.mem -> Prop :=
| expr_safe_val : forall v t m,
                  expr_safe RV (Val v t) m
| expr_safe_loc : forall l m ofs t,
                  expr_safe LV (Addr l ofs t) m
| expr_safe_lred : forall e m e' m' to C,
                   lreduction e m e' m' ->
                   context LV to C ->
                   expr_safe to (C e) m
| expr_safe_rred : forall e m e' m' to C,
                   rreduction e m e' m' ->
                   context RV to C -> 
                   expr_safe to (C e) m
| expr_safe_call : forall e m fd args t to C,
                   callreduction e m fd args t ->
                   context RV to C ->
                   expr_safe to (C e) m.

Definition not_stuck (e : expr) (m : Memory.mem) : Prop :=
forall k C e',
context k RV C -> e = C e' -> expr_safe k e' m.

(* Reduction semantics *) (* Fix me *)
Inductive ssem : state -> state -> Prop :=
| s_lreduction : forall C f e k e' m m',
                 lreduction e m e' m' ->
                 context LV RV C ->
                 ssem (ExprState f (C e) k vm m) (ExprState f (C e') k vm m')
| s_rreduction : forall C f e k m e' m',
                 rreduction e m e' m' ->
                 context RV RV C ->
                 ssem (ExprState f (C e) k vm m) (ExprState f (C e') k vm m')
| s_call : forall C f e k m fd args t,
           callreduction e m fd args t ->
           context RV RV C ->
           ssem (ExprState f (C e) k vm m) (CallState fd args (Kcall f vm t k) m)
| s_stuck : forall C f e k m K,
            context K RV C ->
            ~(expr_safe K e m) ->
            ssem (ExprState f (C e) k vm m) StuckState
| s_val : forall m k f v t,
          ssem (ExprState f (Val v t) (Kdo k) vm m) (ExprState f (Unit (Ptype Tunit)) k vm m)
| s_internal_fun : forall f vargs k m m' m'',
                   list_norepet (f.(fn_args) ++ f.(fn_vars)) ->
                   alloc_variables empty_vmap m (f.(fn_args) ++ f.(fn_vars)) vm m' -> 
                   bind_variables ge vm m' f.(fn_args) vargs m'' ->
                   ssem (CallState (Internal f) vargs k m) (ExprState f f.(fn_body) k vm m'')
| s_cond1 : forall f e1 e2 e3 t k m,
            ssem (ExprState f (Cond e1 e2 e3 t) k vm m) (ExprState f e1 (Kcond e2 e3 k) vm m)
| s_cond2 : forall f v e2 e3 t k m ct b g g' i',
            transBeePL_type t g = Res ct g' i' ->
            bool_val (transBeePL_value_cvalue v) ct m = Some b -> 
            ssem (ExprState f (Val v t) (Kcond e2 e3 k) vm m) (ExprState f (if b then e2 else e3) k vm m)
(* add one more rule for bind to evaluate e1 *)
| s_bind1 : forall f x t' v e2 t k m e2',
            subst x (Val v t') e2 = e2' ->
            ssem (ExprState f (Bind x t' (Val v t') e2 t) k vm m) (ExprState f e2' k vm m).

Definition step (s : state) (s' : state) : Prop :=
ssem s s'.


End Small_step_semantics.



