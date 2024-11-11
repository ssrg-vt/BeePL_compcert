Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps.
Require Import BeePL_aux BeePL_mem BeeTypes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive constant : Type :=
| ConsInt : int -> constant
| ConsUint : int -> constant
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

Definition typeof_expr (e : expr) : type :=
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

(***** Semantics of unary operators *****)
Definition sem_notbool (v : value) : option value :=
match v with 
| Vunit => None 
| Vint i => None
| Vuint i => None 
| Vbool b => Some (of_bool (negb b)) 
| Vloc l => None
end.


Definition sem_notint (v : value) : option value :=
match v with 
| Vunit => None 
| Vint i => Some (of_int (Int.not i)) 
| Vuint i => Some (of_int (Int.not i))
| Vbool b => None 
| Vloc l => None 
end.

Definition sem_neg (v : value) : option value :=
match v with 
| Vunit => None 
| Vint i => Some (of_int (Int.neg i)) 
| Vuint i => Some (of_int (Int.neg i))
| Vbool b => None 
| Vloc l => None 
end.

Definition sem_unary_operation (op : uop) (v : value) : option value :=
match op with 
| Notbool => sem_notbool v 
| Notint => sem_notint v
| Neg => sem_neg v
end.


(***** Semantics of binary operators *****)
(* Addition: Integer overflow is taken care in the definition of int 
   Example : 4 bit (15 is the max) : 15 + 1 wraps around and produces 0 *)
Definition sem_plus (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => None 
| Vint i1, Vint i2 => Some (of_int (Int.add i1 i2)) 
| Vuint i1, Vuint i2 => Some (of_int (Int.add i1 i2))
| Vloc l1, Vloc l2 => None 
| _, _ => None
end.

Definition sem_minus (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => None 
| Vint i1, Vint i2 => Some (of_int (Int.sub i1 i2)) 
| Vuint i1, Vuint i2 => Some (of_int (Int.sub i1 i2))
| Vloc l1, Vloc l2 => None 
| _, _ => None
end.

Definition sem_mult (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => None 
| Vint i1, Vint i2 => Some (of_int (Int.mul i1 i2)) 
| Vuint i1, Vuint i2 => Some (of_int (Int.mul i1 i2))
| Vloc l1, Vloc l2 => None 
| _, _ => None
end.

Definition sem_div (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => None 
| Vint i1, Vint i2 => if (Int.eq i2 Int.zero) || (Int.eq i1 (Int.repr Int.min_signed) && Int.eq i2 Int.mone) (* -128/-1 *)
                      then None 
                      else Some (of_int (Int.divs i1 i2))
| Vuint i1, Vuint i2 => if (Int.eq i2 Int.zero) then None else Some (of_int (Int.divu i1 i2)) 
| Vloc l1, Vloc l2 => None 
| _, _ => None
end.

Definition sem_and (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => Some (of_bool (b1 && b2)) 
| Vint i1, Vint i2 => None 
| Vuint i1, Vuint i2 => None
| Vloc l1, Vloc l2 => None 
| _, _ => None
end.

Definition sem_or (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => Some (of_bool (b1 || b2)) 
| Vint i1, Vint i2 => None 
| Vuint i1, Vuint i2 => None
| Vloc l1, Vloc l2 => None 
| _, _ => None
end.

Definition sem_xor (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => Some (of_bool (xorb b1 b2)) 
| Vint i1, Vint i2 => None 
| Vuint i1, Vuint i2 => None
| Vloc l1, Vloc l2 => None 
| _, _ => None
end.

Definition sem_shl (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => None
| Vint i1, Vint i2 => Some (of_int (Int.shl i1 i2))
| Vuint i1, Vuint i2 => Some (of_int (Int.shl i1 i2))
| Vloc l1, Vloc l2 => None 
| _, _ => None
end.

Definition sem_shr (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => None
| Vint i1, Vint i2 => Some (of_int (Int.shr i1 i2))
| Vuint i1, Vuint i2 => Some (of_int (Int.shru i1 i2))
| Vloc l1, Vloc l2 => None 
| _, _ => None
end.

Definition sem_eq (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => Some (Vbool true)
| Vbool b1, Vbool b2 => Some (of_bool (Bool.eqb b1 b2))
| Vint i1, Vint i2 => Some (of_bool (Int.cmp Ceq i1 i2))
| Vuint i1, Vuint i2 => Some (of_bool (Int.cmpu Ceq i1 i2))
| Vloc l1, Vloc l2 => Some (of_bool (l1 =? l2)%positive) 
| _, _ => None
end.

Definition sem_neq (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => Some (Vbool true)
| Vbool b1, Vbool b2 => Some (of_bool (Bool.eqb b1 b2))
| Vint i1, Vint i2 => Some (of_bool (Int.cmp Cne i1 i2))
| Vuint i1, Vuint i2 => Some (of_bool (Int.cmpu Cne i1 i2))
| Vloc l1, Vloc l2 => Some (of_bool (negb (l1 =? l2)%positive)) 
| _, _ => None
end.

Definition sem_lt (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => None
| Vint i1, Vint i2 => Some (of_bool (Int.cmp Clt i1 i2))
| Vuint i1, Vuint i2 => Some (of_bool (Int.cmpu Clt i1 i2))
| Vloc l1, Vloc l2 => None
| _, _ => None
end.

Definition sem_lte (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => None
| Vint i1, Vint i2 => Some (of_bool (Int.cmp Cle i1 i2))
| Vuint i1, Vuint i2 => Some (of_bool (Int.cmpu Cle i1 i2))
| Vloc l1, Vloc l2 => None
| _, _ => None
end.

Definition sem_gt (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => None
| Vint i1, Vint i2 => Some (of_bool (Int.cmp Cgt i1 i2))
| Vuint i1, Vuint i2 => Some (of_bool (Int.cmpu Cgt i1 i2))
| Vloc l1, Vloc l2 => None
| _, _ => None
end.

Definition sem_gte (v1 : value) (v2 : value) : option value :=
match v1, v2 with 
| Vunit, Vunit => None
| Vbool b1, Vbool b2 => None
| Vint i1, Vint i2 => Some (of_bool (Int.cmp Cge i1 i2))
| Vuint i1, Vuint i2 => Some (of_bool (Int.cmpu Cge i1 i2))
| Vloc l1, Vloc l2 => None
| _, _ => None
end.

Definition sem_binary_operation (op : bop) (v1 v2 : value) : option value :=
match op with 
| Plus => sem_plus v1 v2
| Minus => sem_minus v1 v2
| Mult => sem_mult v1 v2
| Div => sem_div v1 v2
| And => sem_and v1 v2
| Or => sem_or v1 v2
| Xor => sem_xor v1 v2
| Shl => sem_shl v1 v2
| Shr => sem_shr v1 v2
| Eq => sem_eq v1 v2
| Neq => sem_neq v1 v2
| Lt => sem_lt v1 v2
| Lte => sem_lte v1 v2
| Gt => sem_gt v1 v2
| Gte => sem_gte v1 v2
end.

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
             typeof_values vs = unzip2 (fd.(args)) ->
             write_vars (st.(vmem)) (unzip1 fd.(args)) vs = Ok error vm' ->
             sem_expr ge {| hmem := st''.(hmem); vmem := vm' |} fd.(body) st''' rv -> 
             write_var (st'''.(vmem)) r rv = vm'' ->
             typeof_value rv = fd.(rtype) ->
             sem_expr ge st (App (Some r) e es t) {| hmem := st'''.(hmem); vmem := vm'' |}  rv 
| sem_app : forall ge e es t st l st' st'' vs fd vm' st''' rv vm'',
             sem_expr ge st e st' (Vloc l) ->
             get_fun_decl ge l = Some (Fdecl fd) ->
             sem_exprs ge st' es st'' vs ->
             typeof_values vs = unzip2 (fd.(args)) ->
             write_vars (st.(vmem)) (unzip1 fd.(args)) vs = Ok error vm' ->
             sem_expr ge {| hmem := st''.(hmem); vmem := vm' |} fd.(body) st''' rv -> 
             typeof_value rv = fd.(rtype) ->
             sem_expr ge st (App None e es t) {| hmem := st'''.(hmem); vmem := vm'' |}  rv 
| sem_prim_uop : forall ge st e t v uop st' v',
                 sem_expr ge st e st' v ->
                 sem_unary_operation uop v = Some v' ->
                 typeof_expr e = typeof_value v ->
                 sem_expr ge st (Prim (Uop uop) (e :: nil) t) st' v'
| sem_prim_bop : forall ge st e1 e2 t v1 v2 bop st' st'' v,
                 sem_expr ge st e1 st' v1 ->
                 sem_expr ge st' e2 st'' v2 ->
                 sem_binary_operation bop v1 v2 = Some v ->
                 typeof_expr e1 = typeof_value v1 ->
                 typeof_expr e2 = typeof_value v2 ->
                 sem_expr ge st (Prim (Bop bop) (e1 :: e2 :: nil) t) st' v
| sem_prim_ref : forall ge st e t l st' h v, 
                 sem_expr ge st e st' v ->
                 fresh_loc st'.(hmem) l = true ->
                 update_heap st'.(hmem) l v = h ->
                 typeof_value v = typeof_expr e ->
                 sem_expr ge st (Prim Deref (e :: nil) t) st' v
| sem_prim_deref : forall ge st e t l st' v, 
                   sem_expr ge st e st' (Vloc l) ->
                   get_val_loc st.(hmem) l = Some v -> 
                   typeof_value v = typeof_expr e ->
                   sem_expr ge st (Prim Deref (e :: nil) t) st' v
| sem_prim_massgn : forall ge st e1 e2 t l v h st' st'',
                    sem_expr ge st e1 st' (Vloc l) -> 
                    sem_expr ge st' e2 st'' v ->
                    update_heap st''.(hmem) l v = h ->
                    sem_expr ge st (Prim Massgn (e1 :: e2 :: nil) t) {| hmem := h; vmem := st''.(vmem) |} Vunit
| sem_bind : forall ge st x t e e' t' st' st'' v e'',
             subst x e e' = e'' ->
             sem_expr ge st' e'' st'' v ->
             sem_expr ge st (Bind x t e e' t') st'' v
| sem_cond_true : forall ge st e1 e2 e3 t st' st'' v, 
                  sem_expr ge st e1 st' (Vbool true) -> 
                  sem_expr ge st' e2 st'' v ->
                  sem_expr ge st (Cond e1 e2 e3 t) st'' v
| sem_cond_false : forall ge st e1 e2 e3 t st' st'' v, 
                   sem_expr ge st e1 st' (Vbool false) -> 
                   sem_expr ge st' e3 st'' v ->
                   sem_expr ge st (Cond e1 e2 e3 t) st'' v
| sem_addr : forall ge st l bt,
             sem_expr ge st (Addr l bt) st (Vloc l) 
with sem_exprs : genv -> state -> list expr -> state -> list value -> Prop :=
| sem_nil : forall ge st,
            sem_exprs ge st nil st nil
| sem_cons : forall ge st e es st' v st'' vs,
             sem_expr ge st e st' v ->
             sem_exprs ge st' es st'' vs ->
             sem_exprs ge st (e :: es) st'' (v :: vs).



