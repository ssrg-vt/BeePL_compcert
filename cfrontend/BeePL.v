Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Numbers.DecimalString.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Globalenvs compcert.lib.Coqlib Ctypes.
Require Import BeePL_aux Axioms Memory Int Cop Memtype Errors Csem SimplExpr Events BeeTypes BeePL_values.
From mathcomp Require Import all_ssreflect. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.

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

(* Patterns *)
(* Used in pattern matching in the match constructor *) 
Inductive pattern : Type :=
| Pnone : pattern
| Psome : ident -> pattern.

Fixpoint idents_eq (xs ys : list ident) : bool :=
match xs, ys with 
| nil, nil => true 
| x :: xs, y :: ys => (x =? y)%positive && idents_eq xs ys
| _, _ => false
end.

Definition eq_pattern (p1 p2 : pattern) : bool :=
match p1, p2 with 
| Pnone, Pnone => true 
| Psome x, Psome x' => ident_eq x x' 
(*| Bstring xs ts, Bstring xs' ts' => idents_eq xs xs' && eq_types eq_type ts ts'*)
| _, _ => false
end. 

Record bsignature := { bsig_args : list type; bsig_ef : effect; bsig_res : type; bsig_cc : calling_convention }. 

Definition bsig_to_csig (bsig : bsignature) : AST.signature :=
{| sig_args :=  (map typ_of_type (from_typelist (transBeePL_types transBeePL_type bsig.(bsig_args)))); 
   sig_res := (rettype_of_type (transBeePL_type bsig.(bsig_res))); 
   sig_cc := bsig.(bsig_cc) |}.

Inductive external_function : Set :=
| EF_external : string -> bsignature -> external_function.

Definition get_ef_eapp (ef : external_function) : effect :=
match ef with 
| EF_external n sig => sig.(bsig_ef)
end.

Definition get_rt_eapp (ef : external_function) : type :=
match ef with 
| EF_external n sig => sig.(bsig_res)
end.

Definition get_at_eapp (ef : external_function) : list type :=
match ef with 
| EF_external n sig => sig.(bsig_args)
end.

Definition get_name_eapp (ef : external_function) : string :=
match ef with 
| EF_external n sig => n
end.
 
Definition befunction_to_cefunction (bef : external_function) : AST.external_function :=
match bef with 
| EF_external n bsig => (AST.EF_external n (bsig_to_csig bsig))
end. 

(* The source language never exposes the heap binding construct hpφ.e directly to the user 
   but during evaluation the reductions on heap operations create heaps and use them. *)
Inductive expr : Type :=
| Val : value -> type -> expr                                           (* value *) (* rvalue *)
| Var : ident -> type -> expr                                           (* variable *) (* lvalue *)
| Const : BeePL_values.constant -> type -> expr                         (* constant *) (* rvalue *)
| App : expr -> list expr -> type -> expr                               (* function application *) (* rvalue *)
| Prim : builtin -> list expr -> type -> expr                           (* primitive operations *)
| Bind : ident -> type -> expr -> expr -> type -> expr                  (* let binding: type of continuation *)
| Cond : expr -> expr -> expr -> type -> expr                           (* if e then e else e *) 
| Unit : type -> expr                                                   (* unit *)
| Addr : linfo -> ptrofs -> type -> expr                                (* address: Addr: not intended to be written by programmers: *)
| Hexpr : Memory.mem -> expr -> type -> expr                            (* heap effect *)
| Eapp : external_function -> list type -> list expr -> type -> expr    (* external function *)
| Screate : ident -> list ident -> list expr -> type -> expr                (* struct creation *)
| Sfield : expr -> ident -> type -> expr                                (* access to a member of struct *)
| For : expr -> expr -> dir -> expr -> type -> expr                     (* for loop - constant bound *)
| Enone : type -> expr                                                  (* none: option *)
| Esome : expr -> type -> expr                                          (* some: option *)
| Match : expr -> list pattern -> list expr -> type -> expr             (* pattern matching *).

(* for i = 1 to 5 Upto e *)
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

Lemma expr_list_expr_ind_mut:
  forall (Pe : BeePL.expr -> Prop) (Pl : list BeePL.expr -> Prop),
    (* Expression constructors *)
    (forall (v : value) (t : type), Pe (Val v t)) ->
    (forall (x : ident) (t : type), Pe (Var x t)) ->
    (forall (c : BeePL_values.constant) (t : type), Pe (Const c t)) ->
    (forall (e : BeePL.expr) (es : list BeePL.expr) (t : type),
      Pe e -> Pl es -> Pe (App e es t)) ->
    (forall (b : builtin) (es : list BeePL.expr) (t : type),
      Pl es -> Pe (Prim b es t)) ->
    (forall (x : ident) (t : type) (e e' : BeePL.expr) (t' : type),
      Pe e -> Pe e' -> Pe (Bind x t e e' t')) ->
    (forall (e1 e2 e3 : BeePL.expr) (t : type),
      Pe e1 -> Pe e2 -> Pe e3 -> Pe (Cond e1 e2 e3 t)) ->
    (forall (t : type), Pe (Unit t)) ->
    (forall (l : linfo) (ofs : ptrofs) (t : type), Pe (Addr l ofs t)) ->
    (forall (m : Memory.mem) (e : BeePL.expr) (t : type),
      Pe e -> Pe (Hexpr m e t)) ->
    (forall (ef : external_function) (ts : list type) (es : list BeePL.expr) (t : type),
      Pl es -> Pe (Eapp ef ts es t)) ->
    (forall (i : ident) (idents : list ident) (es : list expr) (t : type),
      Pl es -> Pe (Screate i idents es t)) ->
    (forall (e : expr) (x : ident) (t : type), Pe e -> Pe (Sfield e x t)) ->
    (forall (e1 e2 : expr) (d : dir) (e3 : expr) (t : type), 
      Pe e1 -> Pe e2 -> Pe e3 -> Pe (For e1 e2 d e3 t)) ->
    (forall (t : type), Pe (Enone t)) ->
    (forall (e : expr) (t : type), Pe e -> Pe (Esome e t)) ->
    (forall (e : expr) (ps : list pattern) (es : list expr) (t : type),
      Pe e -> Pl es -> Pe (Match e ps es t)) ->
    (Pl nil) ->
    (forall (e : BeePL.expr) (es : list BeePL.expr),
      Pe e -> Pl es -> Pl (e :: es)) ->
    (forall e, Pe e) /\ (forall es, Pl es).
Proof.
  intros Pe Pl HVal HVar HConst HApp HPrim HBind HCond HUnit HAddr HHexpr HEapp Hcreate HSfield HFor HNone HSome HMatch Hnil Hcons.
  
  (* Main proof strategy: induction on the structure of expressions and lists *)
  assert (forall e, Pe e) as He.
  { 
    fix IHe 1.
    intros e.
    destruct e.
    - apply HVal.
    - apply HVar.
    - apply HConst.
    - apply HApp.
      + apply IHe.
      + apply (fix IHl (l : list BeePL.expr) : Pl l :=
          match l with
          | nil => Hnil
          | e :: es => Hcons e es (IHe e) (IHl es)
          end).
    - apply HPrim.
      apply (fix IHl (l : list BeePL.expr) : Pl l :=
        match l with
        | nil => Hnil
        | e :: es => Hcons e es (IHe e) (IHl es)
        end).
    - apply HBind; apply IHe.
    - apply HCond; apply IHe.
    - apply HUnit.
    - apply HAddr.
    - apply HHexpr. apply IHe.
    - apply HEapp.
      apply (fix IHl (l : list BeePL.expr) : Pl l :=
        match l with
        | nil => Hnil
        | e :: es => Hcons e es (IHe e) (IHl es)
        end).
    - apply Hcreate.
      apply (fix IHl (l : list BeePL.expr) : Pl l :=
        match l with
        | nil => Hnil
        | e :: es => Hcons e es (IHe e) (IHl es)
        end).
    - apply HSfield; apply IHe.
    - apply HFor; apply IHe.
    - apply HNone.
    - apply HSome; apply IHe.
    - apply HMatch.
      + apply IHe.
      + induction l0; auto.
  }
  
  assert (forall l, Pl l) as Hl.
  {
    fix IHl 1.
    intros l.
    destruct l.
    - apply Hnil.
    - apply Hcons.
      + apply He.
      + apply IHl.
  }
  
  split; assumption.
Qed.

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
| Screate _ _ _ t => t
| Sfield e x t => t
| For e1 e2 d e t => t
| Enone t => t
| Esome e t => t
| Match e ps es t => t
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

(*Inductive init_data : Set :=
| Init_int8 : int -> init_data
| Init_int16 : int -> init_data
| Init_int32 : int -> init_data
| Init_int64 : int64 -> init_data.*)

Definition globvar (V : Type) := AST.globvar V.

Definition globdef (F V : Type) := AST.globdef F V.

(* Try to write C program that has array of bytes uint_8 and see how it gets translated to Csyntax *)

Definition is_external_fundef (gd : globdef fundef type) : bool :=
match gd with 
| Gfun fd => match fd with 
             | Internal _ => false
             | External _ _ _ _ => true
             end
| Gvar v => false
end.

Record program  : Type := mkprogam { prog_defs : list (ident * globdef fundef type);
                                     prog_public : list ident;
                                     prog_main : ident;
                                     prog_types : list bcomposite_definition;
                                     prog_comp_env : bcomposite_env;
                                     prog_comp_env_eq : build_bcomposite_env prog_types = OK prog_comp_env; 
                                     prog_ident_to_string : list (ident * string)}.

Program Definition make_bprogram (types : list bcomposite_definition)
                                 (defs : list (ident * globdef fundef type))
                                 (public : list ident)
                                 (main : ident)
                                 (ident_to_string :  list (ident * string)) : res program :=
  match build_bcomposite_env types with
  | Error e => Error e
  | OK ce =>
      OK {| prog_defs := defs;
            prog_public := public;
            prog_main := main;
            prog_types := types;
            prog_comp_env := ce;
            prog_comp_env_eq := _;
            prog_ident_to_string := ident_to_string|}
  end.

Definition mkbprogram (types: list bcomposite_definition)
                      (defs: list (ident * globdef fundef type))
                      (public: list ident)
                      (main: ident)
                      (WF: wf_bcomposites types) 
                      (ident_to_string :  list (ident * string)): BeePL.program :=
  let (ce, EQ) := build_bcomposite_env' types WF in
  {| prog_defs := defs;
     prog_public := public;
     prog_main := main;
     prog_types := types;
     prog_comp_env := ce;
     prog_comp_env_eq := EQ; 
     prog_ident_to_string := ident_to_string |}.

(************************** Operation Semantics **************************************)
(* Global environments are a component of the dynamic semantics of
   BeePL language.  A global environment maps symbol names 
   (names of functions and of global variables)
   to the corresponding function declarations. *) 
Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> bcomposite_env }. 

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
Fixpoint trans_bvalue_cvalue (v : value) : Values.val :=
match v with 
| Vunit => Values.Vint (Int.repr 0) (* Fix me *)
| Vbool b => if eqb b true then Values.Vint (Int.repr 1) else Values.Vint (Int.repr 0)
| Vint i => Values.Vint i
| Vint64 i => Values.Vlong i 
| Vloc p ofs => Values.Vptr p ofs
| Voption v => match v with 
               | None => Values.Vptr (Z.to_pos 0) Ptrofs.zero
               | Some v' => trans_bvalue_cvalue v'
               end
end.

(* Converts list of BeePL value to list of C value *)
Fixpoint trans_bvalues_cvalues (vs : list value) : list Values.val :=
match vs with 
| nil => nil
| v :: vs => trans_bvalue_cvalue v :: trans_bvalues_cvalues vs
end.

(* Converts C value to BeePL value *) 
(* we don't want to allow int i and then read i to get garbage value *) 
(* Reading uninitialized memory is not allowed in eBPF as it might leak sensitive information *)
(* A function stores secret data in stack and later it is not cleared and then other function 
   is called, the secret data from older function can be leaked *)
Definition trans_cvalue_bvalue (v : Values.val) : res value :=
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

Section Memory_semantics.

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
  access_mode_type ty = By_value (transl_bchunk_cchunk chunk) ->
  type_is_volatile (transBeePL_type ty) = false ->
  Mem.loadv (transl_bchunk_cchunk chunk) m (trans_bvalue_cvalue (Vloc addr ofs)) = Some v ->
  trans_cvalue_bvalue v = OK v' ->
  deref_addr ty m addr ofs Full v'
| deref_loc_volatile: forall chunk tr v v',
  access_mode_type ty = By_value (transl_bchunk_cchunk chunk) -> 
  type_is_volatile (transBeePL_type ty) = true ->
  volatile_load ge (transl_bchunk_cchunk chunk) m addr ofs tr v ->
  trans_cvalue_bvalue v = OK v' ->
  deref_addr ty m addr ofs Full v'
| deref_addr_reference:
  access_mode_type ty = By_reference ->
  deref_addr ty m addr ofs Full (Vloc addr ofs) 
| deref_addr_copy:
  access_mode_type ty = By_copy ->
  deref_addr ty m addr ofs Full (Vloc addr ofs)
| deref_addr_bitfield: forall sz sg pos width v v' cty,
  transBeePL_type ty = cty ->
  load_bitfield cty sz sg pos width m (Values.Vptr addr ofs) v ->
  trans_cvalue_bvalue v = OK v' ->
  deref_addr ty m addr ofs (Bits sz sg pos width) v'.


(* [assign_addr ty m addr ofs v] returns the updated memory after storing the value v at address [addr] and offset 
   [ofs] *) 
Inductive assign_addr (ty : type) (m : Memory.mem) (addr : Values.block) (ofs : ptrofs) : bitfield -> value -> Memory.mem -> value -> Prop :=
| assign_addr_value : forall v chunk m' v',
  access_mode_type ty = By_value (transl_bchunk_cchunk chunk) ->
  type_is_volatile (transBeePL_type ty) = false ->
  Mem.storev (transl_bchunk_cchunk chunk) m (trans_bvalue_cvalue (Vloc addr ofs)) v = Some m' ->
  trans_cvalue_bvalue v = OK v' ->
  assign_addr ty m addr ofs Full v' m' v'
| assign_loc_volatile: forall v chunk tr m' v',
  access_mode_type ty = By_value (transl_bchunk_cchunk chunk) -> 
  type_is_volatile (transBeePL_type ty) = true ->
  volatile_store ge (transl_bchunk_cchunk chunk) m addr ofs v tr m' ->
  trans_cvalue_bvalue v = OK v' ->
  assign_addr ty m addr ofs Full v' m' v'
| assign_addr_copy: forall b' ofs' bytes m',
  access_mode_type ty = By_copy ->
  (alignof_blockcopy (bcomposite_composite_env (genv_cenv ge)) (transBeePL_type ty) | Ptrofs.unsigned ofs') ->
  (alignof_blockcopy (bcomposite_composite_env (genv_cenv ge)) (transBeePL_type ty) | Ptrofs.unsigned ofs) ->
      b' <> addr \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs' + sizeof (bcomposite_composite_env (genv_cenv ge)) (transBeePL_type ty) <= Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs + sizeof (bcomposite_composite_env (genv_cenv ge)) (transBeePL_type ty) <= Ptrofs.unsigned ofs' ->
   Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof (bcomposite_composite_env (genv_cenv ge)) (transBeePL_type ty)) = Some bytes ->
   Mem.storebytes m addr (Ptrofs.unsigned ofs) bytes = Some m' ->
   assign_addr ty m addr ofs Full (Vloc b' ofs') m' (Vloc b' ofs')
| assign_addr_bitfield: forall sz sg pos width v m' v' bv bv',
  store_bitfield (transBeePL_type ty) sz sg pos width m (Values.Vptr addr ofs) v m' v' ->
  trans_cvalue_bvalue v = OK bv ->
  trans_cvalue_bvalue v' = OK bv' -> 
  assign_addr ty m addr ofs (Bits sz sg pos width) bv m' bv'. 

(* Allocation of function local variables *)
(* [alloc_variables vm1 m1 vars vm2 m2] allocates one memory block for each variable
   declared in [vars], and associates the variable name with this block. 
   [vm1] and [m1] are the initial local environment and memory state.
   [e2] and [m2] are the final local environment and memory state *) 
Inductive alloc_variables : vmap -> Memory.mem -> list (ident * type) -> vmap -> Memory.mem -> Prop :=
| alloc_variables_nil : forall vm hm, 
  alloc_variables vm hm nil vm hm
| alloc_variables_con : forall e m id ty vars m1 l1 m2 e2,
  Mem.alloc m 0 (sizeof_type (genv_cenv ge) ty) = (m1, l1) ->
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
  match id_b_ty with (id, (b, ty)) => (b, 0, sizeof_type (genv_cenv ge) ty) end.

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
  | Bind y t e1 e2 t' =>
      if (x =? y)%positive 
      then Bind y t (subst x se e1) e2 t'
      else Bind y t (subst x se e1) (subst x se e2) t'
  | Cond e1 e2 e3 t => Cond (subst x se e1) (subst x se e2) (subst x se e3) t
  | Unit t => Unit t 
  | Addr l p t => Addr l p t
  | Hexpr h e t => Hexpr h (subst x se e) t
  | Eapp ef ts es t => Eapp ef ts (map (subst x se) es) t
  | Screate x ids es t => Screate x ids (map (subst x se) es) t (* fix we need to make comparison with ids? *)
  | Sfield e fld t => Sfield (subst x se e) fld t
  | For e1 e2 d e' t => For (subst x se e1) (subst x se e2) d (subst x se e') t
  | Enone t => Enone t 
  | Esome e t => Esome (subst x se e) t
  | Match e ps es t => Match (subst x se e) ps (map (subst x se) es) t
  end.


Inductive well_formed_value : value -> type -> Prop :=
| wf_vunit : well_formed_value Vunit (Utype)
| wf_vint : forall sz s a i, 
            well_formed_value (Vint i) (Vtype (Tint sz s a))
| wf_vlong : forall s a i,
             well_formed_value (Vint64 i) (Vtype (Tlong s a))
| wf_vloc : forall l ofs h t a,
            well_formed_value (Vloc l ofs) (Ptrtype (Reftype h t a)).

End Memory_semantics.

(*Section Simpl_big_step_semantics.

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
                  if (is_bop_undef t bop (e1 :: e2 :: nil)) 
                  then return_bzero t = Ok v ->
                       bsem_expr_srv hm (Prim (Bop bop) (e1 :: e2 :: nil) t) v 
                  else bsem_expr_srv hm e1 v1 ->
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

End Simpl_big_step_semantics. *)



