Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps.
Require Import BeeTypes.

Inductive constant : Type :=
| ConsInt : int -> constant
| ConsBool : bool -> constant
| ConsUnit : constant.

Inductive uop : Type :=
| Not : uop
| Incr : uop 
| Decr : uop
| Sizeof : uop
| Neg : uop.

Inductive bop : Type :=
| Plus : bop 
| Minus : bop
| Mult : bop
| Div : bop
| Eq : bop 
| Neq : bop 
| Lt : bop
| Lte : bop
| Gt : bop
| Gte : bop. 

Inductive val : Type :=
| Vunit : val
| Vint : int -> val
| Vbool : bool -> val
| Vloc : positive -> val.

Definition vals := list val.

Definition loc := positive. 

Definition heap := list (loc * val).

Definition vmap := list (ident * val).

Fixpoint update_heap (h : heap) (k : loc) (v : val) : heap := 
match h with 
| nil => (k, v) :: nil
| h :: t => if (k =? fst(h))%positive then (k, v) :: t else h :: update_heap t k v
end.

Fixpoint update_vmap (h : vmap) (k : ident) (v : val) : vmap := 
match h with 
| nil => (k, v) :: nil
| h :: t => if (k =? fst(h))%positive then (k, v) :: t else h :: update_vmap t k v
end.

Fixpoint get_val_loc (h : heap) (k : loc) : option val :=
match h with 
| nil => None 
| v :: vm => if (k =? fst(v))%positive then Some (snd(v)) else get_val_loc vm k
end.

Fixpoint get_val_var (h : vmap) (k : ident) : option val :=
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
| Run : heap -> builtin      (* eliminate heap effect : [r1-> v1, ..., ern->vn] e 
                                reduces to e captures the essence of state isolation 
                                and reduces to a value discarding the heap *)
| Uop : uop -> builtin       (* unary operator *)
| Bop : bop -> builtin.       (* binary operator *)

(* The source language never exposes the heap binding construct hpφ.e directly to the user 
   but during evaluation the reductions on heap operations create heaps and use them. *)
Inductive expr : Type :=
| Var : ident -> type -> expr                                   (* variable *)
| Const : constant -> type -> expr                              (* constant *)
| App : expr -> nat -> list expr -> list type -> expr           (* function application *)
| Bfun : builtin -> nat -> list expr -> list type -> expr       (* builtin functions *)
| Lexpr : ident -> type -> expr -> expr -> expr                 (* let binding *)
| Cond : expr -> type -> expr -> expr -> type -> expr           (* if e then e else e *)
(* not intended to be written by programmers:*)
| Addr : loc -> basic_type -> expr                              (* address *)
| Hexpr : heap -> expr -> type -> expr                          (* heap effect *).

 
Inductive decl : Type :=
| TAlias : ident -> type -> decl
| Gval : ident -> constant -> decl
| Fdecl : ident -> list (ident * type) -> expr -> decl.

Definition genv := list (loc * decl).

Fixpoint get_decl (ge : genv) (l : loc) : option decl :=
match ge with 
| nil => None
| g :: gs => if (l =? fst(g))%positive then Some (snd(g)) else get_decl gs l
end.

Fixpoint get_declv (ge : genv) (v : val) : option decl :=
match v with 
| Vloc p => get_decl ge p 
| _ => None
end.

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
| Ftype ts n ef t => free_variables_types free_variables_type ts ++ free_variables_type t
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

(* Typing Rules 
Inductive ty_expr : ty_context -> store_context -> expr -> type -> effect -> Type :=
(* Since the variable and constant evaluation produces no effect, 
   we are free to assume any arbitrary effect *)
| Ty_var : forall Gamma Sigma t x ef,
           get_ty Gamma x = Some t ->
           ty_expr Gamma Sigma (Var t x) t ef
| Ty_const_int : forall Gamma Sigma i ef,
                 ty_expr Gamma Sigma (Const (ConsInt i)) (Btype (Bprim Tint)) ef
| Ty_const_bool : forall Gamma Sigma b ef,
                  ty_expr Gamma Sigma (Const (ConsBool b)) (Btype (Bprim Tbool)) ef
| Ty_const_unit : forall Gamma Sigma ef,
                  ty_expr Gamma Sigma (Const (ConsUnit)) (Btype (Bprim Tunit)) ef
| Ty_abs : forall Gamma Gamma' Sigma n xs e t2 ef2 ef,
           extend_contexts Gamma xs = Gamma' ->
           ty_expr Gamma' Sigma e t2 ef2 ->
           ty_expr Gamma Sigma (Abs n xs e) (Ftype (unzip2 xs) n ef2 t2) ef
| Ty_app : forall Gamma Sigma e es ts n ef t1,
           ty_expr Gamma Sigma e (Ftype ts n ef t1) ef ->
           ty_exprs Gamma Sigma es ts ef ->
           ty_expr Gamma Sigma (App e n es) t1 ef
| Ty_addr : forall Gamma Sigma l t h ef,
            get_sty Sigma l = Some t -> 
            ty_expr Gamma Sigma (Addr t l) (Reftype h t) ef
| Ty_ref : forall Gamma Sigma e t h ef,
           ty_expr Gamma Sigma e (Btype t) ef->
           ty_expr Gamma Sigma (Ref t e) (Reftype h t) (Erow (Esingle (Hst h)) ef)
| Ty_deref : forall Gamma Sigma e t h ef,
             ty_expr Gamma Sigma e (Reftype h t) ef ->
             ty_expr Gamma Sigma (Deref t e) (Btype t) (Erow (Esingle (Hst h)) ef)
| Ty_mexpr : forall Gamma Sigma e1 t e2 h ef,
             ty_expr Gamma Sigma e1 (Reftype h t) ef ->
             ty_expr Gamma Sigma e2 (Btype t) ef ->
             ty_expr Gamma Sigma (Massgn e1 e2) (Btype (Bprim Tunit)) (Erow (Esingle (Hst h)) ef)
| Ty_run : forall Gamma Sigma e t h ef fv,
           ty_expr Gamma Sigma e t (Erow (Esingle (Hst h)) ef) ->
           ftv Gamma Sigma t ef = fv ->
           ~(List.In h fv) ->
           ty_expr Gamma Sigma (Run e) t ef
| Ty_hexpr : forall Gamma Sigma H e t h ef, 
             ty_expr Gamma Sigma e t ef ->
             ty_expr Gamma Sigma (Hexpr H e) t (Erow (Esingle (Hst h)) ef)
| Ty_let : forall Gamma Sigma x t e1 e2 ef Gamma' t',
           ty_expr Gamma Sigma e1 t Empty -> 
           extend_context Gamma x t = Gamma' ->
           ty_expr Gamma' Sigma e2 t' ef ->  
           ty_expr Gamma Sigma (Lexpr x t e1 e2) t' ef
| Ty_cond : forall Gamma Sigma e1 e2 e3 t ef1 ef2,
            ty_expr Gamma Sigma e1 (Btype (Bprim Tbool)) ef1 ->
            ty_expr Gamma Sigma e2 t ef2 ->
            ty_expr Gamma Sigma e3 t ef2 ->
            ty_expr Gamma Sigma (Cond e1 e2 e3) t (Erow ef1 ef2)
with ty_exprs : ty_context -> store_context -> list expr -> list type -> effect -> Prop :=
| Ty_nil : forall Gamma Sigma,
           ty_exprs Gamma Sigma nil [::(Btype(Bprim Tunit))] Empty
| Ty_cons : forall Gamma Sigma e es t ef ts efs,
            ty_expr Gamma Sigma e t ef ->
            ty_exprs Gamma Sigma es ts efs ->
            ty_exprs Gamma Sigma (e :: es) (t :: ts) (Erow ef efs).


Scheme ty_expr_exprs_rec := Induction for ty_expr Sort Prop
 with ty_exprs_expr_rec := Induction for ty_exprs Sort Prop.*)


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

Fixpoint unzip1 {A} {B} (es : list (A * B)) : list A :=
match es with 
| nil => nil
| e :: es => fst(e) :: unzip1 es
end.

Fixpoint unzip2 {A} {B} (es : list (A * B)) : list B :=
match es with 
| nil => nil
| e :: es => snd(e) :: unzip2 es
end.

(* Substitution *)
Fixpoint subst (x:ident) (e':expr) (e:expr) : expr :=
match e with
| Var y t => if (x =? y)%positive then e' else e
| Const c t => Const c t
| App e n es ts => App (subst x e' e) n (substs subst x e' es) ts
| Bfun b n es ts => Bfun b n (substs subst x e' es) ts
| Lexpr y t e1 e2 => if (x =? y)%positive then Lexpr y t e1 e2 else Lexpr y t e1 (subst x e' e2)
| Cond e1 t1 e2 e3 t2 => Cond (subst x e' e1) t1 (subst x e' e2) (subst x e' e3) t2
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

(* Operational Semantics *)
Inductive sem_expr : genv -> state -> expr -> state -> val -> Prop :=
| sem_var : forall ge st x t vm v,
            get_vmap st = vm ->
            get_val_var vm x = Some v ->
            sem_expr ge st (Var x t) st v
| sem_const_int : forall ge st i,
                  sem_expr ge st (Const (ConsInt i) (Ptype Tint)) st (Vint i)
| sem_const_bool : forall ge st b,
                   sem_expr ge st (Const (ConsBool b) (Ptype Tbool)) st (Vbool b)
| sem_const_uint : forall ge st,
                   sem_expr ge st (Const (ConsUnit) (Ptype Tunit)) st (Vunit)
| sem_appv : forall ge st e n es ts ve st' fd fn xs fb vs st'',
             sem_expr ge st e st' ve ->
             get_declv ge ve = Some fd ->
             fd = Fdecl fn xs fb ->
             sem_exprs ge st' es st'' vs ->
             (*(substs_multi (unzip1 xs) vs e) = e' ->*)
             sem_expr ge st (App e n es ts) st'' (Vunit)
with sem_exprs : genv -> state -> list expr -> state -> list val -> Prop :=
| sem_nil : forall ge st,
            sem_exprs ge st nil st nil
| sem_cons : forall ge st e es st' v st'' vs,
             sem_expr ge st e st' v ->
             sem_exprs ge st' es st'' vs ->
             sem_exprs ge st (e :: es) st'' (v :: vs).         



(*| sem_app_abs : forall st n1 xs e n2 vs,
                values vs ->
                n1 = n2 ->
                sem_expr st (App (Abs n1 xs e) n2 vs) st (substs_multi (unzip1 xs) vs e)
| sem_app1 : forall e1 n e2 st e1' st',
             sem_expr st e1 st' e1' ->
             sem_expr st (App e1 n e2) st' (App e1' n e2)
| sem_app2 : forall v1 n e2 st e2' st',
             value v1 ->
             sem_exprs st e2 st' e2' ->
             sem_expr st (App v1 n e2) st' (App v1 n e2')
| sem_addr : forall st t l,
             value (Addr t l) -> 
             sem_expr st (Addr t l) st (Addr t l)
| sem_ref : forall t e st e' st',
            sem_expr st e st' e' ->
            sem_expr st (Ref t e) st' (Ref t e')
| sem_refv : forall h t e st l h',
             value e ->
             get_heap st = h ->
             ~(In l (domain_heap h)) -> 
             update_heap h l e = h' ->
             sem_expr st (Ref t e) (State h' (get_vmap st)) (Addr t l)
| sem_deref : forall st t e st' e',
              sem_expr st e st' e' ->
              sem_expr st (Deref t e) st' (Deref t e')
| sem_derefv : forall st t l h v,
               value (Addr t l) ->
               value v ->
               get_heap st = (H h) ->
               get h l = Some v ->
               sem_expr st (Deref t (Addr t l)) st v
| sem_massgn1 : forall st e1 e2 st' e1',
                sem_expr st e1 st' e1' ->
                sem_expr st (Massgn e1 e2) st' (Massgn e1' e2)
| sem_massgn2 : forall st v1 e2 st' e2',
                value v1 ->
                sem_expr st e2 st' e2' ->
                sem_expr st (Massgn v1 e2) st' (Massgn v1 e2')
| sem_massgnl : forall st t l v2 h h',
                value v2 ->
                get_heap st = h ->
                update_heap h l v2 = h' ->
                sem_expr st (Massgn (Addr t l) v2) (State h' (get_vmap st)) (Const (ConsUnit))
| sem_run : forall st h e, (* FIX ME *)
            sem_expr st (Run (Hexpr h e)) st e
| sem_hexpr1 : forall st h hm t l v,
               value (Addr t l) ->
               value v ->
               h = (H hm) ->
               get hm l = Some v ->
               sem_expr st (Hexpr h (Deref t (Addr t l))) st v 
| sem_hexpr2 : forall st h t e e' st',
               sem_expr st e st' e' ->
               sem_expr st (Hexpr h (Deref t e)) st' (Hexpr h (Deref t e')) 
| sem_hexpr3 : forall st t l v h h',
               value (Addr t l) ->
               value v ->
               get_heap st = h ->
               (In l (domain_heap h)) -> 
               update_heap h l v = h' ->
               sem_expr st (Hexpr h (Massgn (Addr t l) v)) (State h' (get_vmap st)) v 
| sem_hexpr4 : forall st t l e e' st' h,
               value (Addr t l) ->
               sem_expr st e st' e' ->
               sem_expr st (Hexpr h (Massgn (Addr t l) e)) st' (Hexpr h (Massgn (Addr t l) e'))
| sem_hexpr5 : forall st e1 e1' e2 st' h,
               sem_expr st e1 st' e1' ->
               sem_expr st (Hexpr h (Massgn e1 e2)) st' (Hexpr h (Massgn e1' e2)) 
| sem_hexpr6 : forall st t l h v hm,
               get_heap st = h ->
               h = (H hm) ->
               get hm l = Some v ->
               sem_expr st (Hexpr h (Addr t l)) st v
| sem_letv : forall x t v1 e2 st,
             value v1 ->
             sem_expr st (Lexpr x t v1 e2) st (subst x v1 e2)
| sem_let1 : forall x t e1 e2 st st' e1',
             sem_expr st e1 st' e1' ->
             sem_expr st (Lexpr x t e1 e2) st' (Lexpr x t e1' e2)
| sem_condt : forall e2 e3 st,
              sem_expr st (Cond (Const (ConsBool true)) e2 e3) st e2 
| sem_condf : forall e2 e3 st,
              sem_expr st (Cond (Const (ConsBool false)) e2 e3) st e3
| sem_cond : forall e1 e2 e3 st e1' st',
             sem_expr st e1 st' e1' -> 
             sem_expr st (Cond e1 e2 e3) st' (Cond e1' e2 e3)
with sem_exprs : state -> list expr -> state -> list expr -> Prop :=
| sem_nil : forall st,
            sem_exprs st nil st nil
| sem_cons : forall st e es st' e' st'' es',
             sem_expr st e st' e' ->
             sem_exprs st' es st'' es' ->
             sem_exprs st (e :: es') st'' (e' :: es'). *)
