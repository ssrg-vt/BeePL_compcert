Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Numbers.DecimalString.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Globalenvs compcert.lib.Coqlib Ctypes.
Require Import BeePL_aux Axioms Memory Int Cop Memtype Errors Csem SimplExpr Events BeeTypes BeePL_values Coq.Lists.ListDec.
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
| Cast : type -> builtin                     (* casting operator *).
(*| Run : Memory.mem -> builtin               (* eliminate heap effect : [r1-> v1, ..., ern->vn] e 
                                               reduces to e captures the essence of state isolation 
                                               and reduces to a value discarding the heap *).*)

(* Patterns *)
(* Used in pattern matching in the match constructor *) 
Inductive pattern : Type :=
| Pnone : pattern
| Psome : ident -> pattern
| Pbytes : ident -> type -> list (ident * type) -> pattern.

Definition get_pattern_var (p : pattern) : list ident :=
match p with 
| Pnone => nil
| Psome x => (x :: nil)
| Pbytes x t ys => (x :: unzip1 ys)
end.

Fixpoint get_patterns_var (ps : list pattern) : list ident :=
match ps with 
| nil => nil
| p :: ps => get_pattern_var p ++ get_patterns_var ps
end.

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
| Pbytes x t xs, Pbytes x' t' xs' => ident_eq x x' && eq_type t t' &&
                                     idents_eq (unzip1 xs) (unzip1 xs') && eq_types eq_type (unzip2 xs) (unzip2 xs')
| _, _ => false
end. 

Record bsignature := { bsig_args : list type; bsig_ef : effect; bsig_res : type; bsig_cc : calling_convention }. 

Definition bsig_to_csig (bsig : bsignature) : AST.signature :=
{| sig_args :=  (map xtyp_of_type (transBeePL_types transBeePL_type bsig.(bsig_args))); 
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
(*| Eapp : external_function -> list type -> list expr -> type -> expr    (* external function *)*)
| Sinit : ident -> list ident -> list expr -> type -> expr              (* struct creation *)
| Sfield : expr -> ident -> type -> expr                                (* access to a member of struct *)
| For : expr -> expr -> dir -> expr -> type -> expr                     (* for loop - constant bound *)
| Enone : type -> expr                                                  (* none: option *)
| Esome : expr -> type -> expr                                          (* some: option *)
| Match : expr -> list pattern -> list expr -> type -> expr             (* pattern matching *)
| Ebytes : list expr -> type -> expr                                    (* bitstrings *)
| Ainit : ident -> type -> list expr -> type -> expr                    (* array initialization *)
| Aaccess : ident -> type -> nat -> type -> expr.                       (* array access *)

(*int x = 2; {
int x = 3;
int y = 4; }
int z = x + y;
return z; z : 6

let x = 2 in 
 let x = 3 in 
  let y = 4 in 
   let z = x + y in z ==> 7

let x = 2 in 
 let x1 = 3 in 
  let y = 4 in 
   let z = x1 + y in z ==> 

[x : l] ==> [cx : l']*)

Section Expr_Ind.
Context 
  (P : expr -> Prop)
  (Hval : forall t v, P (Val v t))
  (Hvar : forall t x, P (Var x t))
  (Hconst : forall t c, P (Const c t))
  (Happ : forall t e, P e -> forall es, (forall e, List.In e es -> P e) -> P (App e es t))
  (Hprim : forall b t es, (forall e, List.In e es -> P e) -> P (Prim b es t))
  (Hbind : forall x t t' e1, P e1 -> forall e2, P e2 -> P (Bind x t e1 e2 t')) 
  (Hcond : forall t e1, P e1 -> forall e2, P e2 -> forall e3, P e3 -> P (Cond e1 e2 e3 t))
  (Hunit : forall t, P (Unit t))
  (Haddr : forall l o t, P (Addr l o t))
  (*(Heapp : forall t ef ts es, (forall e, List.In e es -> P e) -> P (Eapp ef ts es t))*)
  (Hsinit : forall t h ids es, (forall e, List.In e es -> P e) -> P (Sinit h ids es t))
  (Hsfield : forall t h e, P e -> P (Sfield e h t))
  (Hfor : forall t d e1, P e1 -> forall e2, P e2 -> forall e3, P e3 -> P (For e1 e2 d e3 t))
  (Hnone : forall t, P (Enone t))
  (Hsome : forall t e, P e -> P (Esome e t))
  (Hmatch : forall t ps e, P e -> forall es, (forall e, List.In e es -> P e) -> P (Match e ps es t))
  (Hbytes : forall t es, (forall e, List.In e es -> P e) -> P (Ebytes es t))
  (Hainit : forall a t t' es, (forall e, List.In e es -> P e) -> P (Ainit a t es t'))
  (Haccess : forall a t n t', P (Aaccess a t n t')). 


Definition exprs_ind_rec (f : forall e, P e)
  : forall es : list expr, forall e, List.In e es -> P e :=
  fix loop es :=
    match es with
    | e' :: es' =>
        fun e k =>
          match List.in_inv k with
          | or_introl a  => ecast x (P x) a (f e')
          | or_intror b  => loop es' e b
          end
    | [::] =>
        fun e k =>
          False_ind _ (List.in_nil k)
    end.

Fixpoint expr_ind_rec (e : expr) : P e :=
match e with 
| Val v t => Hval t v
| Var x t => Hvar t x
| Const c t => Hconst t c
| App e es t => Happ t (@expr_ind_rec e) (@exprs_ind_rec expr_ind_rec es)
| Prim b es t => Hprim b t (@exprs_ind_rec expr_ind_rec es)
| Cond e1 e2 e3 t => Hcond t (expr_ind_rec e1) (expr_ind_rec e2) (expr_ind_rec e3)
| Bind x t e1 e2 t' => Hbind x t t' (expr_ind_rec e1) (expr_ind_rec e2) 
| Unit t => Hunit t
| Addr l o t => Haddr l o t
(*| Eapp ef ts es t => Heapp t ef ts (@exprs_ind_rec expr_ind_rec es)*)
| Sinit s ids es t => Hsinit t s ids (@exprs_ind_rec expr_ind_rec es)
| Sfield e id t => Hsfield t id (expr_ind_rec e)
| For e1 e2 d e3 t => Hfor t d (expr_ind_rec e1) (expr_ind_rec e2) (expr_ind_rec e3)
| Enone t => Hnone t
| Esome e t => Hsome t (expr_ind_rec e)
| Match e ps es t => Hmatch t ps (expr_ind_rec e) (@exprs_ind_rec expr_ind_rec es)
| Ebytes es t => Hbytes t (@exprs_ind_rec expr_ind_rec es)
| Ainit a t es t' => Hainit a t t' (@exprs_ind_rec expr_ind_rec es)
| Aaccess a t n t' => Haccess a t n t'
end.

End Expr_Ind.

(* Mutual induction Scheme for expr and list expr *)
Section Exprs_Ind.
Context (P : expr -> Prop)
        (Ps : list expr -> Prop).

Record expr_ind_hypotheses : Prop := {
    exprs_nil : Ps nil;
    exprs_cons : forall e, P e -> forall es, Ps es -> Ps (e :: es);
    expr_val : forall t v, P (Val v t);
    expr_var : forall t x, P (Var x t);
    expr_const : forall t c, P (Const c t);
    expr_app : forall t e es, P e -> Ps es -> P (App e es t);
    expr_prim : forall b t es, Ps es -> P (Prim b es t);
    expr_cond : forall t e1, P e1 -> forall e2, P e2 -> forall e3, P e3 -> P (Cond e1 e2 e3 t);
    expr_bind : forall x t t' e1, P e1 -> forall e2, P e2 -> P (Bind x t e1 e2 t');
    expr_unit : forall t, P (Unit t);
    expr_addr : forall t l o, P (Addr l o t);
    (*expr_eapp : forall t ef ts es, Ps es -> P (Eapp ef ts es t);*)
    expr_sinit : forall t s ids es, Ps es -> P (Sinit s ids es t);
    expr_sfield : forall t id e, P e -> P (Sfield e id t);
    expr_for : forall t d e1, P e1 -> forall e2, P e2 -> forall e3, P e3 -> P (For e1 e2 d e3 t);
    expr_enone : forall t, P (Enone t);
    expr_esome : forall t e, P e -> P (Esome e t);
    expr_match : forall t ps e es, P e -> Ps es -> P (Match e ps es t);
    expr_ebytes : forall t es, Ps es -> P (Ebytes es t);
    expr_ainit : forall a t t' es, Ps es -> P (Ainit a t es t');
    expr_access : forall a t n t', P (Aaccess a t n t')}.

Context (h: expr_ind_hypotheses).

Definition exprs_ind expr_mut_ind : forall pes, Ps pes :=
fix exprs_ind pes :=
    if pes is pe :: pes'
    then exprs_cons h (expr_mut_ind pe) (exprs_ind pes')
    else exprs_nil h.

Fixpoint expr_mut_ind e : P e :=
match e with 
| Val v t => expr_val h t v
| Var x t => expr_var h t x
| Const c t => expr_const h t c
| App e es t => expr_app h t (expr_mut_ind e) (exprs_ind expr_mut_ind es)
| Prim b es t => expr_prim h b t (exprs_ind expr_mut_ind es)
| Cond e1 e2 e3 t => expr_cond h t (expr_mut_ind e1) (expr_mut_ind e2) (expr_mut_ind e3)
| Bind x t e1 e2 t' => expr_bind h x t t' (expr_mut_ind e1) (expr_mut_ind e2)
| Unit t => expr_unit h t 
| Addr l o t => expr_addr h t l o
(*| Eapp ef ts es t => expr_eapp h t ef ts (exprs_ind expr_mut_ind es)*)
| Sinit s ids es t => expr_sinit h t s ids (exprs_ind expr_mut_ind es)
| Sfield e id t => expr_sfield h t id (expr_mut_ind e) 
| For e1 e2 d e3 t => expr_for h t d (expr_mut_ind e1) (expr_mut_ind e2) (expr_mut_ind e3) 
| Enone t => expr_enone h t
| Esome e t => expr_esome h t (expr_mut_ind e) 
| Match e ps es t => expr_match h t ps (expr_mut_ind e) (exprs_ind expr_mut_ind es)
| Ebytes es t => expr_ebytes h t (exprs_ind expr_mut_ind es)
| Ainit a t es t' => expr_ainit h a t t' (exprs_ind expr_mut_ind es)
| Aaccess a t n t' => expr_access h a t n t'
end.

Definition exprs_ind_pair :=
 conj expr_mut_ind (exprs_ind expr_mut_ind).

End Exprs_Ind.


(* Size of the expression to help termination checker of Rocq *)
Fixpoint size_e (e : expr) : nat :=
match e with 
| Val v t => 1
| Var x t => 1
| Const c t => 1
| App e es t => size_e e + foldr (fun e acc => (size_e e + acc)%nat) O es + 1
| Prim b es t => foldr (fun e acc => (size_e e + acc)%nat) O es + 1
| Bind x t e1 e2 t' => size_e e1 + size_e e2 + 1 
| Cond e1 e2 e3 t => size_e e1 + size_e e2 + size_e e3 + 1
| Unit t => 1
| Addr l ofs t => 1
(*| Eapp ef ts es t => foldr (fun e acc => (size_e e + acc)%nat) O es + 1*)
| Sinit s ids es t => foldr (fun e acc => (size_e e + acc)%nat) O es + 1
| Sfield e id t => size_e e + 1
| For e1 e2 d e3 t => size_e e1 + size_e e2 + size_e e3 + 1
| Enone t => 1
| Esome e t => size_e e + 1
| Match e ps es t => size_e e + foldr (fun e acc => (size_e e + acc)%nat) O es + 1
| Ebytes es t => foldr (fun e acc => (size_e e + acc)%nat) O es + 1
| Ainit a t es t' => foldr (fun e acc => (size_e e + acc)%nat) O es + 1
| Aaccess a t n t' => 1
end.

Definition size_es (es : list BeePL.expr) := foldr (fun e acc => (BeePL.size_e e + acc)%nat) O es.


(* Free variables *) 
Fixpoint free_variables (e : expr) : list ident  :=
match e with 
| Val v t => nil
| Var x t => (x :: nil)
| Const c t => nil
| App e es t => let fvs := map free_variables es in 
                let fve := free_variables e in 
                fve ++ flatten fvs
| Prim b es t => flatten (map free_variables es)
| Bind x r e1 e2 t => free_variables e1 ++ (remove ident_eq x (free_variables e2))
| Cond e1 e2 e3 t => free_variables e1 ++ free_variables e2 ++ free_variables e3
| Unit t => nil
| Addr l o t => nil
(*| Eapp ef ts es t => flatten (map free_variables es)*)
| Sinit x ids es t => flatten (map free_variables es)
| Sfield e x t => free_variables e 
| For e1 e2 d e t => free_variables e1 ++ free_variables e2 ++ free_variables e
| Enone t => nil
| Esome e t => free_variables e 
| Match e ps es t => free_variables e ++ flatten (map free_variables es) 
| Ebytes es t => flatten (map free_variables es)
| Ainit a t es t' => flatten (map free_variables es)
| Aaccess a t n t' => nil
end.
 
Fixpoint in_vars (x : ident) (xs : list ident) : bool :=
match xs with 
| nil => true
| y :: ys => if ident_eq x y then true else in_vars x ys
end.

Fixpoint disjoint_vars (l1 l2 : list ident) : bool :=
match l1 with
| nil => true
| x :: xs =>
      if in_vars x l2 then false
      else disjoint_vars xs l2
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
| Prim b es t => match b with 
                 | Cast t' => t'
                 | _ => t
                 end
| Bind x t e e' t' => t'
| Cond e e' e'' t => t
| Unit t => t
| Addr l p t => t
(*| Eapp ef ts es t => t*)
| Sinit _ _ _ t => t
| Sfield e x t => t
| For e1 e2 d e t => t
| Enone t => t
| Esome e t => t
| Match e ps es t => t
| Ebytes es t => t
| Ainit _ _ _ t => t
| Aaccess _ _ _ t => t
end.

Fixpoint typeof_exprs (e : list expr) : list BeeTypes.type :=
match e with 
| nil => nil
| e :: es => typeof_expr e :: typeof_exprs es
end.


Record function : Type := mkfunction { fn_return: type;
                                       fn_effect: effect;
                                       fn_callconv: calling_convention;
                                       fn_args: list (ident * type);
                                       fn_vars: list (ident * type);
                                       fn_body: expr;
                                       is_ebpf : bool }.

Inductive fundef : Type :=
| Internal : function -> fundef
| External: external_function -> list type -> type -> calling_convention -> fundef.

(** Type of a function definition. **)
Definition type_of_function (f: function) : type :=
  Ftype (unzip2 (fn_args f)) (fn_effect f) (fn_return f) (cc_vararg (fn_callconv f)).

Definition type_of_fundef (f : fundef) : type :=
match f with 
| Internal f => type_of_function f
| External e ts t cc => Ftype ts (get_ef_eapp e) t (cc_vararg cc)
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

Definition get_v_fundef (f : fundef) : bool :=
match f with 
| Internal fd => (cc_vararg (fn_callconv fd))
| External ef ts t cc => cc_vararg cc
end.

Definition get_v_function (f : function) : bool :=
(cc_vararg (fn_callconv f)).

Definition get_effect_fundef (f : fundef) : effect :=
match f with 
| Internal fd => fn_effect fd
| External ef ts t cc => get_ef_eapp ef
end.

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

Record program  : Type := mkprogam { prog_defs : list (ident * AST.globdef BeePL.fundef type * option string);
                                     prog_public : list ident;
                                     prog_main : ident;
                                     prog_types : list bcomposite_definition;
                                     prog_comp_env : bcomposite_env;
                                     prog_comp_env_eq : build_bcomposite_env prog_types = OK prog_comp_env; 
                                     prog_ident_to_string : list (ident * string)}.

Program Definition make_bprogram (types : list bcomposite_definition)
                                 (defs : list (ident * globdef fundef type * option string))
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
                      (defs: list (ident * globdef fundef type * option string))
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

Definition get_args_ebpf_gbdef (gd : globdef fundef type) : list (ident * type) :=
match gd with 
| Gfun fd => match fd with 
             | Internal f => if f.(is_ebpf) then f.(fn_args) else nil
             | External _ _ _ _ => nil
             end
| Gvar v => nil
end.

Fixpoint get_args_ebpf_gbdefs (gd : list (globdef fundef type)) : list (ident * type) :=
match gd with 
| nil => nil
| gd :: gds => get_args_ebpf_gbdef gd  ++ get_args_ebpf_gbdefs gds
end.

Definition get_args (p : program) : list (ident * type) :=
match map (fun '(x, y, z) => y) p.(prog_defs) with
| nil => nil
| gd :: gds => get_args_ebpf_gbdef gd ++ get_args_ebpf_gbdefs gds
end.

(************************** Operation Semantics **************************************)
(* Global environments are a component of the dynamic semantics of
   BeePL language.  A global environment maps symbol names 
   (names of functions and of global variables)
   to the corresponding function declarations. *) 
Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> bcomposite_env }. 

Definition trans_program_astprog (p : program) : AST.program fundef type :=
@mkprogram fundef type
   (map (fun '(id, gd, _) => (id, gd)) p.(prog_defs))
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


(* In BeePL, all pointers come only from trusted helpers or explicit reference creation, 
   so every dereference is a real memory load and implies a valid memory block. 
   Allowing deref-by-reference or deref-by-copy would let BeePL fabricate pointers to non-existent memory, 
   breaking safety. Helpers are trusted but checked via options. 
   Unlike CompCert, which can produce unchecked Vptr b ofs without a memory read, BeePL disallows such unchecked pointer creation. *)
(* [deref_addr ty m addr ofs] computes the value of type [ty] residing in 
    memory [m] at address [addr], offset [ofs] and bitfield designation bf *)
Inductive deref_addr (ty : type) (m : Memory.mem) (addr : Values.block) (ofs : ptrofs) : bitfield -> value -> Prop :=
| deref_addr_value : forall chunk v v',
  access_mode_type ty = By_value (transl_bchunk_cchunk chunk) ->
  type_is_volatile (transBeePL_type ty) = false ->
  Mem.loadv (transl_bchunk_cchunk chunk) m (trans_bvalue_cvalue (Vloc addr ofs)) = Some v ->
  trans_cvalue_bvalue v = OK v' ->
  deref_addr ty m addr ofs Full v'
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
(*| assign_loc_volatile: forall v chunk tr m' v',
  access_mode_type ty = By_value (transl_bchunk_cchunk chunk) -> 
  type_is_volatile (transBeePL_type ty) = true ->
  volatile_store ge (transl_bchunk_cchunk chunk) m addr ofs v tr m' ->
  trans_cvalue_bvalue v = OK v' ->
  assign_addr ty m addr ofs Full v' m' v'*)
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
(* Sigma is a mapping from location to the type of element it holds *) 
Definition balloc (Sigma : store_context) (m : Memory.mem) (ty : type) (lo hi: Z) : 
Mem.mem' * Values.block * store_context :=
let (m1, l1) := Mem.alloc m 0 (sizeof_type (genv_cenv ge) ty) in 
let Sigma' := PTree.set l1 ty Sigma in
(m1, l1, Sigma').

Inductive alloc_variables : store_context -> vmap -> Memory.mem -> list (ident * type) -> vmap -> Memory.mem -> store_context -> Prop :=
| alloc_variables_nil : forall Sigma vm hm, 
  alloc_variables Sigma vm hm nil vm hm Sigma
| alloc_variables_con : forall Sigma e m id ty vars m1 l1 m2 e2 Sigma',
  balloc Sigma m ty 0 (sizeof_type (genv_cenv ge) ty) = (m1, l1, Sigma') ->
  alloc_variables Sigma (PTree.set id (l1, ty) e) m1 vars e2 m2 Sigma' ->
  alloc_variables Sigma e m ((id, ty) :: vars) e2 m2 Sigma'.

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

Fixpoint vars_bound_by (p : pattern) : list ident :=
  match p with
  | Pnone => nil
  | Psome x => x :: nil
  | Pbytes x _ fields => x :: map fst fields
  end.

End Memory_semantics.


Section SubstHelper.

Variable subst : ident -> expr -> expr -> expr.

Fixpoint x_in_xs (x : ident) (p : list ident) : bool :=
  match p with 
  | nil => false
  | y :: ys => if (x =? y)%positive then true else x_in_xs x ys
end.

Definition x_in_pattern (x : ident) (p : pattern) : bool :=
let bound_vars := vars_bound_by p in
x_in_xs x bound_vars.

Fixpoint subst_match_branches (x : ident) (se : expr) (ps : list pattern) (es : list expr) : list expr :=
  match ps, es with
  | nil, nil => nil
  | p :: ps', e :: es' =>
      let e' := if x_in_pattern x p
                then e
                else subst x se e in
      e' :: subst_match_branches x se ps' es'
  | _, _ => es
  end.

End SubstHelper.

Section Substitution.

Variable S : ident -> expr -> expr -> expr.

Fixpoint substs (x : ident) (se : expr) (es : list expr) : list expr :=
match es with 
| nil => nil
| e :: es => S x se e :: substs x se es
end.

End Substitution.

(* Substitution *)
Fixpoint subst (x : ident) (se : expr) (e : expr) {struct e} : expr :=
  match e with 
  | Val v t => e
  | Var y t => if (x =? y)%positive then se else Var y t
  | Const c t => e 
  | App e es t => App (subst x se e) (substs subst x se es) t
  | Prim b es t => Prim b (substs subst x se es) t
  | Bind y t e1 e2 t' =>
      if (x =? y)%positive 
      then Bind y t (subst x se e1) e2 t'
      else Bind y t (subst x se e1) (subst x se e2) t'
  | Cond e1 e2 e3 t => Cond (subst x se e1) (subst x se e2) (subst x se e3) t
  | Unit t => Unit t 
  | Addr l p t => Addr l p t
  (*| Eapp ef ts es t => Eapp ef ts (substs subst x se es) t*)
  | Sinit y ids es t => if (x =? y)%positive then Sinit y ids es t
                        else Sinit y ids (substs subst x se es) t
  | Sfield e fld t => Sfield (subst x se e) fld t
  | For e1 e2 d e' t => For (subst x se e1) (subst x se e2) d (subst x se e') t
  | Enone t => Enone t 
  | Esome e t => Esome (subst x se e) t
  | Match e ps es t => (*Match (subst x se e) ps (subst_match_branches subst x se ps es) t : correct *)
    Match (subst x se e) ps (substs subst x se es) t (* replace this with above *)
  | Ebytes es t => Ebytes (substs subst x se es) t
  | Ainit a t es t' => Ainit a t (substs subst x se es) t'
  | Aaccess a t n t' => Aaccess a t n t'
  end.

(* Inductive principles for subst *)
Inductive SubstE (x:ident) (se:expr) : expr -> expr -> Prop :=
| S_Val v t :
    SubstE x se (Val v t) (Val v t)
| S_Var_hit t :
    SubstE x se (Var x t) se
| S_Var_miss y t (H: x <> y) :
    SubstE x se (Var y t) (Var y t)
| S_Const c t :
    SubstE x se (Const c t) (Const c t)
| S_App e0 e0' es es' t
    (H0  : SubstE  x se e0 e0')
    (Hes : SubstEs x se es es') :
    SubstE x se (App e0 es t) (App e0' es' t)
| S_Prim b es es' t
    (Hes : SubstEs x se es es') :
    SubstE x se (Prim b es t) (Prim b es' t)
| S_Bind_hit y t e1 e1' e2 t'
    (Hy : x = y)
    (H1 : SubstE x se e1 e1') :
    SubstE x se (Bind y t e1 e2 t') (Bind y t e1' e2 t')
| S_Bind_miss y t e1 e1' e2 e2' t'
    (Hy : x <> y)
    (H1 : SubstE  x se e1 e1')
    (H2 : SubstE  x se e2 e2') :
    SubstE x se (Bind y t e1 e2 t') (Bind y t e1' e2' t')
| S_Cond e1 e1' e2 e2' e3 e3' t
    (H1: SubstE x se e1 e1') (H2: SubstE x se e2 e2') (H3: SubstE x se e3 e3') :
    SubstE x se (Cond e1 e2 e3 t) (Cond e1' e2' e3' t)
| S_Unit t :
    SubstE x se (Unit t) (Unit t)
| S_Addr l p t :
    SubstE x se (Addr l p t) (Addr l p t)
(*| S_Eapp ef ts es es' t
    (Hes : SubstEs x se es es') :
    SubstE x se (Eapp ef ts es t) (Eapp ef ts es' t)*)
| S_Sinit_hit y ids es t (Hy : x = y) :
    SubstE x se (Sinit y ids es t) (Sinit y ids es t)
| S_Sinit_miss y ids es es' t (Hy : x <> y)
    (Hes : SubstEs x se es es') :
    SubstE x se (Sinit y ids es t) (Sinit y ids es' t)
| S_Sfield e e' fld t
    (He : SubstE x se e e') :
    SubstE x se (Sfield e fld t) (Sfield e' fld t)
| S_For e1 e1' e2 e2' d e e' t
    (H1: SubstE x se e1 e1') (H2: SubstE x se e2 e2') (H3: SubstE x se e e') :
    SubstE x se (For e1 e2 d e t) (For e1' e2' d e' t)
| S_Enone t :
    SubstE x se (Enone t) (Enone t)
| S_Esome e e' t
    (He: SubstE x se e e') :
    SubstE x se (Esome e t) (Esome e' t)
| S_Match e e' ps es es' t
    (He : SubstE  x se e  e')
    (Hs : SubstEs x se es es') :
    SubstE x se (Match e ps es t) (Match e' ps es' t)
| S_Ebytes es es' t
    (Hs : SubstEs x se es es') :
    SubstE x se (Ebytes es t) (Ebytes es' t)
| S_Ainit a t0 es es' t'
    (Hs : SubstEs x se es es') :
    SubstE x se (Ainit a t0 es t') (Ainit a t0 es' t')
| S_Aaccess a t0 n t' :
    SubstE x se (Aaccess a t0 n t') (Aaccess a t0 n t')

with SubstEs (x:ident) (se:expr) : list expr -> list expr -> Prop :=
| S_Nil :
    SubstEs x se nil nil
| S_Cons e e' es es'
    (He  : SubstE  x se e  e')
    (Hes : SubstEs x se es es') :
    SubstEs x se (e :: es) (e' :: es').

Scheme SubstE_mut_ind  := Induction for SubstE  Sort Prop
with   SubstEs_mut_ind := Induction for SubstEs Sort Prop.
Combined Scheme Subst_mutind from SubstE_mut_ind, SubstEs_mut_ind.


Inductive well_formed_value : value -> type -> Prop :=
| wf_vunit : well_formed_value Vunit (Utype)
| wf_vbool : forall b, well_formed_value (Vbool b) (Vtype Tbool)
| wf_vint : forall sz s a i, 
            well_formed_value (Vint i) (Vtype (Tint sz s a))
| wf_vlong : forall s a i,
             well_formed_value (Vint64 i) (Vtype (Tlong s a))
| wf_vloc : forall l ofs t a,
            well_formed_value (Vloc l ofs) (Ptrtype (Reftype t a)).


Fixpoint bind_vars (Gamma : ty_context) (l: list (ident * type)) : ty_context :=
match l with
| nil => Gamma
| (id, ty) :: l => bind_vars (PTree.set id ty Gamma) l
end.

Fixpoint bind_globdef (Gamma: ty_context) (l: list (ident * globdef fundef type)) : ty_context :=
match l with
| nil => Gamma
| (id, Gfun fd) :: l => bind_globdef (PTree.set id (type_of_fundef fd) Gamma) l
| (id, Gvar v) :: l => bind_globdef (PTree.set id v.(gvar_info) Gamma) l
end.




