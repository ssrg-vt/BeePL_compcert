Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes.
Require Import BeePL Clight.

(****** Translation from BeePL to Clight ******)

Section translate_types.

Variable transBeePL_type : BeeTypes.type -> Ctypes.type.

Fixpoint transBeePL_types (ts : list BeeTypes.type) : Ctypes.typelist :=
match ts with 
| nil => Tnil
| t :: ts => Tcons (transBeePL_type t) (transBeePL_types ts)
end.

End translate_types.

(* Translation of BeePL types to Clight Types *) 
Fixpoint transBeePL_type (t : BeeTypes.type) : Ctypes.type :=
match t with 
| BeeTypes.Ptype (BeeTypes.Tunit) => Tvoid
| BeeTypes.Ptype (BeeTypes.Tint) => (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |})
| BeeTypes.Ptype (BeeTypes.Tbool) => (Tint I8 Unsigned {| attr_volatile := false; attr_alignas := Some 1%N |}) 
| BeeTypes.Reftype h b => match b with 
                          | BeeTypes.Bprim (BeeTypes.Tunit) => Tpointer Tvoid {| attr_volatile := false; attr_alignas := None |}
                          | BeeTypes.Bprim (BeeTypes.Tint) => Tpointer (Tint I32 Signed {| attr_volatile := false; 
                                                                                           attr_alignas := Some 4%N |})
                                                              {| attr_volatile := false; attr_alignas := Some 4%N |}
                          | BeeTypes.Bprim (BeeTypes.Tbool) => Tpointer (Tint I8 Unsigned {| attr_volatile := false; 
                                                                                             attr_alignas := Some 1%N |}) 
                                                               {| attr_volatile := false; attr_alignas := Some 4%N |}
                          end
| BeeTypes.Ftype ts n ef t => Tfunction (transBeePL_types transBeePL_type ts) 
                                        (transBeePL_type t)  
                                        {| cc_vararg := Some (Z.of_nat(n)); cc_unproto := false; cc_structret := false |}  
end. 

(* Represents a default variable: can be used to create a variable  *)
Definition dident := 1%positive. 

(* Represents a default value: as 0 (int), when we need to assign it to a variable, we need to 
   type cast it to the respective type *)
Definition dvalue := (Econst_int (Int.repr 0) (Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 4%N |})).

Definition bool_to_int (b : bool) : int :=
match b with 
| true => (Int.repr 1)
| false => (Int.repr 0)
end.

Fixpoint transBeePL_expr_i (e: BeePL.expr) : Clight.statement :=
match e with 
(* Var x t ==> x := dv_t *)
| Var x t => Sset x (Ecast dvalue 
                    (transBeePL_type t))
(* Const c t ==> tvar x := c_t *)
| Const c t => match c with 
               | ConsInt i => Clight.Ssequence 
                              (Sset dident (Etempvar dident (transBeePL_type t))) 
                              (Sset dident (Econst_int i (transBeePL_type t)))
               | ConsBool b => Clight.Ssequence 
                               (Sset dident (Etempvar dident (transBeePL_type t))) 
                               (Sset dident (Econst_int (bool_to_int b) (transBeePL_type t)))
               | ConsUnit => Sskip (* FIX ME: there is no unit constant in Clight *)
               end
| App e n es ts => Sskip
| _ => Sskip
end.


(* Examples *)
Compute (transBeePL_expr_i (Var 2%positive (BeeTypes.Ptype (BeeTypes.Tint)))).
Compute (transBeePL_expr_i (Const (ConsInt (Int.repr 2)) (BeeTypes.Ptype (BeeTypes.Tint)))).


(*Inductive expr : Set :=
    Var : ident -> BeeTypes.type -> BeePL.expr
  | Const : constant -> BeeTypes.type -> BeePL.expr
  | App : BeePL.expr ->
          nat -> list BeePL.expr -> list BeeTypes.type -> BeePL.expr
  | Bfun : builtin ->
           nat -> list BeePL.expr -> list BeeTypes.type -> BeePL.expr
  | Lexpr : ident ->
            BeeTypes.type -> BeePL.expr -> BeePL.expr -> BeePL.expr
  | Cond : BeePL.expr ->
           BeeTypes.type ->
           BeePL.expr -> BeePL.expr -> BeeTypes.type -> BeePL.expr
  | Addr : loc -> BeeTypes.basic_type -> BeePL.expr
  | Hexpr : heap -> BeePL.expr -> BeeTypes.type -> BeePL.expr


Inductive expr : Set :=
    Econst_int : int -> type -> expr
  | Econst_float : Floats.float -> type -> expr
  | Econst_single : Floats.float32 -> type -> expr
  | Econst_long : int64 -> type -> expr
  | Evar : ident -> type -> expr
  | Etempvar : ident -> type -> expr
  | Ederef : expr -> type -> expr
  | Eaddrof : expr -> type -> expr
  | Eunop : Cop.unary_operation -> expr -> type -> expr
  | Ebinop : Cop.binary_operation -> expr -> expr -> type -> expr
  | Ecast : expr -> type -> expr
  | Efield : expr -> ident -> type -> expr
  | Esizeof : type -> type -> expr
  | Ealignof : type -> type -> expr

Inductive statement : Set :=
    Sskip : statement
  | Sassign : expr -> expr -> statement
  | Sset : ident -> expr -> statement
  | Scall : option ident -> expr -> list expr -> statement
  | Sbuiltin : option ident ->
               external_function -> typelist -> list expr -> statement
  | Ssequence : statement -> statement -> statement
  | Sifthenelse : expr -> statement -> statement -> statement
  | Sloop : statement -> statement -> statement
  | Sbreak : statement
  | Scontinue : statement
  | Sreturn : option expr -> statement
  | Sswitch : expr -> labeled_statements -> statement
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement
  with labeled_statements : Set :=
    LSnil : labeled_statements
  | LScons : option Z ->
             statement -> labeled_statements -> labeled_statements*)
