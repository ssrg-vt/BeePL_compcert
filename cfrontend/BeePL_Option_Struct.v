Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib SimplExpr Csyntaxdefs.
Require Import BeePL_aux BeePL BeeTypes Csyntax Errors SimplExpr BeePL_values DecimalString.

Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.
Local Open Scope list_scope.

Fixpoint filter_otype (l : list type) : list type :=
match l with
| nil => nil
| Otype t :: xs => Otype t :: filter_otype xs
| _ :: xs => filter_otype xs
end.

Fixpoint mem_type (t : type) (l : list type) : bool :=
match l with
| nil => false
| x :: xs => if eq_type t x then true else mem_type t xs
end.

Fixpoint remove_duplicate_type (l : list type) : list type :=
match l with
| nil => nil
| x :: xs => let rest := remove_duplicate_type xs in
             if mem_type x rest then rest else x :: rest
end.

Definition unique_option_types (l : list type) : list type :=
remove_duplicate_type (filter_otype l).

Fixpoint get_bcs_from_types (ots : list type) (bc : list bcomposite_definition) : list bcomposite_definition :=
match ots with
| nil => bc
| Otype t' :: ots_tail => let nbc := Bcomposite (create_ident_type t') Struct
                                       (Member_plain option_tag (Ptype (Tint I8 Unsigned noattr)) ::
                                        Member_plain option_val t' :: nil) noattr in
                          let bc' := bc ++ (nbc :: nil) in
                          get_bcs_from_types ots_tail bc'
| _ :: ots_tail => get_bcs_from_types ots_tail bc
end.

Definition get_bcs_from_vars (vars : list (ident * type)) (bc : list bcomposite_definition) : list bcomposite_definition :=
let ts := map snd vars in
let ots := unique_option_types ts in
get_bcs_from_types ots bc.

(* Test *)
(*
Definition x : ident := 1%positive.
Definition y : ident := 2%positive.
Definition s : ident := 3%positive.
Definition sf1 : ident := 4%positive.
Definition bc : bcomposite_definition :=  Bcomposite s Struct
                                            (Member_plain sf1 (Ptype Tbool) :: nil) noattr.
Compute (get_bc_from_vars ((x, Otype (Ptype Tunit)) :: (y, Otype (Ptype Tunit)) :: nil) nil).
Compute (get_bc_from_vars ((x, Otype (Ptype (Tint I8 Unsigned noattr))) :: 
                           (y, Otype (Ptype (Tint I8 Signed noattr))) :: nil) (bc :: nil)).*)

Definition get_bcs_from_function (fn : BeePL.function) (bc : list bcomposite_definition) : list bcomposite_definition := 
let vars := fn.(BeePL.fn_vars) in 
get_bcs_from_vars vars bc.


Definition get_bcs_from_fundef (fd : BeePL.fundef) (bc : list bcomposite_definition) : list bcomposite_definition := 
match fd with 
| Internal f => get_bcs_from_function f bc
| External ef ts t cc => bc 
end.

Definition get_bcs_from_globdef (gd : BeePL.globdef BeePL.fundef BeeTypes.type) (bc : list bcomposite_definition) : 
                                 list bcomposite_definition :=
match gd with 
| AST.Gfun f => get_bcs_from_fundef f bc
| AST.Gvar g => bc
end.

Fixpoint get_bcs_from_globdefs (gd : list (BeePL.globdef BeePL.fundef BeeTypes.type)) (bc : list bcomposite_definition) : 
                                 list bcomposite_definition :=
match gd with 
| nil => bc
| gd :: gds => let nbc := get_bcs_from_globdef gd bc in
               get_bcs_from_globdefs gds nbc
end.

Definition get_bcs_from_program (p : BeePL.program) : list bcomposite_definition :=
let fv := unzip2 p.(prog_defs) in 
let bc := p.(prog_types) in 
get_bcs_from_globdefs fv bc.


