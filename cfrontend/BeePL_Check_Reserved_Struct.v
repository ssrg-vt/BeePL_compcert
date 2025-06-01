Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib SimplExpr Csyntaxdefs.
Require Import BeePL_aux BeePL BeeTypes Csyntax Errors SimplExpr BeePL_values DecimalString BeePL_notations.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope list_scope.

Definition check_user_struct (t : type) : bool :=
match t with 
| Stype x a => ((substring 0 5 (string_of_ident x)) =? "bytes")%string
| _ => false
end.
      
Fixpoint check_user_structs (ts : list type) : bool :=
match ts with 
| nil => false
| st :: sts' => if check_user_struct st then true else check_user_structs sts' 
end. 

(*Compute (check_user_structs (Stype (ident_of_string "bytes_t") noattr ::
                             Stype (ident_of_string "x") noattr :: 
                             tint32s :: nil)).*)

Definition check_struct_from_types (ots : list type) : res (list type) :=
if check_user_structs ots 
then Error (msg "Reserved bytes struct names are not allowed")
else OK ots.

Definition check_struct_from_vars (vars : list (ident * type)) : res (list (ident * type)) :=
let ts := map snd vars in
do rts <- check_struct_from_types ts;
OK (zip (map fst vars) rts).

Definition check_struct_from_function (fn : BeePL.function) : res BeePL.function := 
let vars := fn.(BeePL.fn_vars) in 
do rs <- check_struct_from_vars vars;
OK fn.


Definition check_struct_from_fundef (fd : BeePL.fundef)  : res BeePL.fundef := 
match fd with 
| Internal f => do rs <- check_struct_from_function f; OK fd
| External ef ts t cc => OK fd 
end.

Definition check_struct_from_globdef (gd : BeePL.globdef BeePL.fundef BeeTypes.type) : 
                                res (BeePL.globdef BeePL.fundef BeeTypes.type) :=
match gd with 
| AST.Gfun f => do rs <- check_struct_from_fundef f; OK gd
| AST.Gvar g => OK gd
end.

Fixpoint check_struct_from_globdefs (gd : list (BeePL.globdef BeePL.fundef BeeTypes.type)) : 
                                 res (list (BeePL.globdef BeePL.fundef BeeTypes.type)) :=
match gd with 
| nil => OK gd
| gd1 :: gds1 => do nbc <- check_struct_from_globdef gd1;
               do nbcs <- check_struct_from_globdefs gds1; OK gd 
end.

Definition check_struct_from_program (p : BeePL.program) : res BeePL.program :=
  let defs := map (fun '(_, gd, _) => gd) p.(prog_defs) in
  do rs <- check_struct_from_globdefs defs; OK p.
