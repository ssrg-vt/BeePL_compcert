Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps.
Require Import BeePL_aux BeePL_mem BeeTypes.

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
| App : option ident -> expr -> list expr -> type -> expr          (* function application: option ident represents return variable *)
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
| App x e ts t => t
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

Definition is_fun_decl (d : decl) : bool :=
match d with 
| Fdecl fd => true 
| Gvdecl gd => false
end.

Definition is_global_decl (d : decl) : bool :=
match d with 
| Fdecl fd => false 
| Gvdecl gd => true
end.

Fixpoint get_fun_decl (ge : genv) (l : loc) : option decl :=
match ge with 
| nil => None
| g :: gs => if (l =? fst(g))%positive && is_fun_decl (snd(g)) then Some (snd(g)) else get_fun_decl gs l
end.

(* first loc represents where the decl is stored and second loc represents where the 
   definition of main is stored *)
Definition module := prod (list (loc * decl)) loc.

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
| App r e es t => App r (subst x e' e) (substs subst x e' es) t
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
| sem_var : forall ge st x t v, 
            get_val_var st.(vmem) x = Some v -> 
            sem_expr ge st (Var x t) st v
| sem_const_int : forall ge st i, 
                  sem_expr ge st (Const (ConsInt i) (Ptype Tint)) st (Vint i)
| sem_const_bool : forall ge st b, 
                  sem_expr ge st (Const (ConsBool b) (Ptype Tbool)) st (Vbool b)
| sem_const_unit : forall ge st,
                   sem_expr ge st (Const (ConsUnit) (Ptype Tunit)) st (Vunit)
| sem_appr : forall ge e es t st l st' st'' vs fd vm' st''' rv r vm'',
             sem_expr ge st e st' (Vloc l) ->
             get_fun_decl ge l = Some (Fdecl fd) ->
             sem_exprs ge st' es st'' vs ->
             type_of_values vs = unzip2 (fd.(args)) ->
             write_vars (st.(vmem)) (unzip1 fd.(args)) vs = Ok error vm' ->
             sem_expr ge {| hmem := st''.(hmem); vmem := vm' |} fd.(body) st''' rv -> 
             write_var (st'''.(vmem)) r rv = vm'' ->
             type_of_value rv = fd.(rtype) ->
             sem_expr ge st (App (Some r) e es t) {| hmem := st'''.(hmem); vmem := vm'' |}  rv 
| sem_app : forall ge e es t st l st' st'' vs fd vm' st''' rv vm'',
             sem_expr ge st e st' (Vloc l) ->
             get_fun_decl ge l = Some (Fdecl fd) ->
             sem_exprs ge st' es st'' vs ->
             type_of_values vs = unzip2 (fd.(args)) ->
             write_vars (st.(vmem)) (unzip1 fd.(args)) vs = Ok error vm' ->
             sem_expr ge {| hmem := st''.(hmem); vmem := vm' |} fd.(body) st''' rv -> 
             type_of_value rv = fd.(rtype) ->
             sem_expr ge st (App None e es t) {| hmem := st'''.(hmem); vmem := vm'' |}  rv 
with sem_exprs : genv -> state -> list expr -> state -> list value -> Prop :=
| sem_nil : forall ge st,
            sem_exprs ge st nil st nil
| sem_cons : forall ge st e es st' v st'' vs,
             sem_expr ge st e st' v ->
             sem_exprs ge st' es st'' vs ->
             sem_exprs ge st (e :: es) st'' (v :: vs).



