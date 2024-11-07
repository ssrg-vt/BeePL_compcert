Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps.
Require Import BeePL_aux BeeTypes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive constant : Type :=
| ConsInt : int -> constant
| ConsBool : bool -> constant
| ConsUnit : constant.

Inductive gconstant : Type := 
| Gvalue : constant -> gconstant
| Gloc : positive -> gconstant
| Gspace : Z -> gconstant (* uninitialized global variables *). 

(* Overloaded C operators and their semantics depends on the type of arguments *)
Inductive uop : Type :=
| Notbool : uop   (* boolean negation ! *)
| Notint : uop    (* int compliment ~ (one's compiment *) 
| Neg : uop.      (* opposite : two's compliment *)

Inductive bop : Type :=
(* arithmetic *)
| Plus : bop 
| Minus : bop
| Mult : bop
| Div : bop
(* logical *)
| And : bop
| Or : bop
| Xor : bop 
| Shl : bop
| Shr : bop
(* comparison *)
| Eq : bop 
| Neq : bop 
| Lt : bop
| Lte : bop
| Gt : bop
| Gte : bop. 

Inductive value : Type :=
| Vunit : value
| Vint : int -> value
| Vbool : bool -> value
| Vloc : positive -> value.

Definition vals := list value.

Definition loc := positive. 

Definition heap := list (loc * value).

Definition vmap := list (ident * value).

Fixpoint update_heap (h : heap) (k : loc) (v : value) : heap := 
match h with 
| nil => (k, v) :: nil
| h :: t => if (k =? fst(h))%positive then (k, v) :: t else h :: update_heap t k v
end.

Fixpoint update_vmap (h : vmap) (k : ident) (v : value) : vmap := 
match h with 
| nil => (k, v) :: nil
| h :: t => if (k =? fst(h))%positive then (k, v) :: t else h :: update_vmap t k v
end.

Fixpoint get_val_loc (h : heap) (k : loc) : option value :=
match h with 
| nil => None 
| v :: vm => if (k =? fst(v))%positive then Some (snd(v)) else get_val_loc vm k
end.

Fixpoint get_val_var (h : vmap) (k : ident) : option value :=
match h with 
| nil => None 
| v :: vm => if (k =? fst(v))%positive then Some (snd(v)) else get_val_var vm k
end.

Inductive builtin : Type :=
| Ref : builtin              (* allocation : ref t e allocates e of type t 
                                and returns the fresh address *)
| Deref : builtin            (* dereference : deref t e returns the value of type t 
                                present at location e *)
| Massgn : builtin           (* assign value at a location l (l := e) 
                                assigns the evaluation of e to the reference cell l *)
| Uop : uop -> builtin       (* unary operator *)
| Bop : bop -> builtin       (* binary operator *)
| Run : heap -> builtin      (* eliminate heap effect : [r1-> v1, ..., ern->vn] e 
                                reduces to e captures the essence of state isolation 
                                and reduces to a value discarding the heap *).


(* The source language never exposes the heap binding construct hpφ.e directly to the user 
   but during evaluation the reductions on heap operations create heaps and use them. *)
Inductive expr : Type :=
| Var : ident -> type -> expr                                      (* variable *)
| Const : constant -> type -> expr                                 (* constant *)
| App : expr -> list expr -> type -> expr                          (* function application *)
| Prim : builtin -> list expr -> type -> expr                      (* primitive functions: arrow : 
                                                                      for now I want to treat them not like functions
                                                                      during the semantics of App, we always make sure that
                                                                      the fist "e" is evaluated to a location  *)
| Bind : ident -> type -> expr -> expr -> type -> expr             (* let binding: type of continuation *)
| Cond : expr -> expr -> expr -> type -> expr                      (* if e then e else e *)
(* not intended to be written by programmers:*)
| Addr : loc -> basic_type -> expr                                 (* address *)
| Hexpr : heap -> expr -> type -> expr                             (* heap effect *).

Notation "x ':' t" := (Var x t) (at level 70, no associativity).
Notation "c '~' t" := (Const c t) (at level 80, no associativity).
Notation "'val' x ':' t '=' e ';' e'" := (Bind x t e e') (at level 60, right associativity).
Notation "'prim' b ( n , es , ts )" := (Prim b n es ts)(at level 50, right associativity).
Notation "'fun' \ f ( n , es , ts )" := (App f n es ts)(at level 50, right associativity).
Notation "'If' e ':' t 'then' e' 'else' e'' ':' t'" := (Cond e t e' e'' t')(at level 40, left associativity).

Definition typeof (e : expr) : type :=
match e with 
| Var x t => t
| Const x t => t
| App e ts t => t
| Prim b es t => t
| Bind x t e e' t' => t'
| Cond e e' e'' t => t
| Addr l t => match t with 
              | Bprim tb => (Ptype tb)
              end
| Hexpr h e t => t
end.

(* f(x1 : t1, x2 : t2) : t3 = int x = 0; int y =0; return 0 (* Dummy example *) *)
Record fun_decl : Type := 
       mkfunction {fname : ident; args : list (ident * type); lvars : list (ident * type); rtype : type; body : expr}.

Record globv : Type := mkglobv {gname : ident; gtype : type; gval : list gconstant}.

Record talias : Type := mktalias {tname : ident; atype : type}.

Inductive decl : Type :=
| Fdecl : fun_decl -> decl
| Gvdecl : globv -> decl.
(*| Tadecl : talias -> decl.*) (* Fix me: Not sure to what global declaration this can be translated to *) 

Definition genv := list (loc * decl).

Fixpoint get_decl (ge : genv) (l : loc) : option decl :=
match ge with 
| nil => None
| g :: gs => if (l =? fst(g))%positive then Some (snd(g)) else get_decl gs l
end.

Definition get_declv (ge : genv) (v : value) : option decl :=
match v with 
| Vloc p => get_decl ge p 
| _ => None
end.

(* first loc represents where the decl is stored and second loc represents where the 
   definition of main is stored *)
Definition module := prod (list (loc * decl)) loc.

Section FTVS.

Variable free_variables_type : type -> list ident.

Fixpoint free_variables_types (ts : list type) : list ident :=
match ts with 
| nil => nil
| t :: ts => free_variables_type t ++ (free_variables_types ts)
end.

End FTVS.

(* Free variable with respect to types *)
Fixpoint free_variables_type (t : type) : list ident :=
match t with 
| Ptype t => nil
| Ftype ts ef t => free_variables_types free_variables_type ts ++ free_variables_type t
| Reftype h t => h :: nil
end.

Definition free_variables_effect_label (ef : effect_label) : list ident :=
match ef with 
| Panic => nil 
| Divergence => nil
| Read h => h :: nil
| Write h => h :: nil
| Alloc h => h :: nil
end.

Fixpoint free_variables_effect (ef : effect) : list ident := 
match ef with 
| nil => nil
| e :: es => free_variables_effect_label e ++ free_variables_effect es
end.

(* For now, we take it as empty but once we introduce polymorphism the free variables needs to be tracked to ensure 
   correct substiution of type variables *)
Definition free_variables_ty_context (Gamma : ty_context) : list ident := nil.

Definition free_variables_store_context (Sigma : store_context) : list ident := nil.

Definition ftv (Gamma : ty_context) (Sigma : store_context) (t : type) (ef : effect) : list ident :=
free_variables_ty_context Gamma ++ free_variables_store_context Sigma ++ free_variables_type t ++ free_variables_effect ef.

(* State is made from heap and virtual map (registers to values) *)
Inductive state : Type :=
| State : heap -> vmap -> state.

Definition get_vmap (st : state) : vmap :=
match st with 
| State h vm => vm
end.

Definition get_heap (st : state) : heap :=
match st with 
| State h vm => h
end.

Fixpoint mem (x : ident) (l : list ident) {struct l} : bool :=
match l with 
| nil => false
| y :: ys => if (x =? y)%positive then true else mem x ys
end. 

Section Subs.

Variable subst : ident -> expr -> expr -> expr.

Fixpoint substs (x : ident) (e' : expr) (es : list expr) : list expr :=
match es with 
| nil => nil 
| e1 :: es1 => subst x e' e1 :: substs x e' es1
end. 

End Subs.

(* Substitution *)
Fixpoint subst (x:ident) (e':expr) (e:expr) : expr :=
match e with
| Var y t => if (x =? y)%positive then e' else e
| Const c t => Const c t
| App e es t => App (subst x e' e) (substs subst x e' es) t
| Prim b es t => Prim b (substs subst x e' es) t 
| Bind y t e1 e2 t' => if (x =? y)%positive then Bind y t e1 e2 t' else Bind y t e1 (subst x e' e2) t'
| Cond e1 e2 e3 t => Cond (subst x e' e1) (subst x e' e2) (subst x e' e3) t
| Addr l t => Addr l t 
| Hexpr h e t => Hexpr h (subst x e' e) t
end.

(* Substitution of multiple variables *)
Fixpoint substs_multi (xs : list ident) (es' : list expr) (e : expr) : expr :=
match xs with 
| nil => e 
| x' :: xs' => match es' with 
             | nil => e 
             | e' :: es' => substs_multi xs' es' (subst x' e' e)
             end
end.

(*Definition write_var (x : ident) (s : state) : option state := 
let vm := get_vmap st in*) 

(* Operational Semantics *)
Inductive sem_expr : genv -> state -> expr -> state -> value -> Prop :=
| sem_var : forall ge st x t vm v, 
            get_vmap st = vm ->
            get_val_var vm x = Some v -> 
            sem_expr ge st (Var x t) st v
| sem_const_int : forall ge st i, 
                  sem_expr ge st (Const (ConsInt i) (Ptype Tint)) st (Vint i)
| sem_const_bool : forall ge st b, 
                  sem_expr ge st (Const (ConsBool b) (Ptype Tbool)) st (Vbool b)
| sem_const_unit : forall ge st,
                   sem_expr ge st (Const (ConsUnit) (Ptype Tunit)) st (Vunit)
| sem_appv : forall ge e es t st l st' st'' vs fd,
             sem_expr ge st e st' (Vloc l) ->
             sem_exprs ge st' es st'' vs ->
             get_decl ge l = Some fd ->
             
             sem_expr ge st (App e es t) st (Vloc l) 
with sem_exprs : genv -> state -> list expr -> state -> list value -> Prop :=
| sem_nil : forall ge st,
            sem_exprs ge st nil st nil
| sem_cons : forall ge st e es st' v st'' vs,
             sem_expr ge st e st' v ->
             sem_exprs ge st' es st'' vs ->
             sem_exprs ge st (e :: es) st'' (v :: vs).



