Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux BeePL_notations.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* fun main () : int32, [] {
   let u : int32* = ref 2 in  
   let o : int32* = some u in
   match o with 
        | none => 0
        | some v => !u + 4
    end
  }
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _u : ident := $"u".
Definition _o : ident := $"o".
Definition _v : ident := $"v".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_u, "u") :: 
                                                       (_o, "o") :: 
                                                       (_v, "v") ::
                                                       (_main, "main") :: nil).

Definition f_some_match : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := (Alloc mem_ident :: Read mem_ident :: Write mem_ident :: Read mem_ident :: nil);
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_u, trint32s) :: (_o, toint32s) :: (_v, trint32s):: nil);
                                   fn_body := Bind _u trint32s 
                                                (Prim Ref (cint (Int.repr 2) tint32s :: nil) trint32s)
                                                  (Bind _o toint32s 
                                                    (Esome (Var _u trint32s) toint32s)
                                                      (Match (Var _o toint32s) 
                                                         (Pnone :: Psome _v :: nil) 
                                                         (cint (Int.repr 0) tint32s ::
                                                           (Prim (Bop Cop.Oadd) (Prim Deref (Var _u trint32s :: nil) tint32s :: 
                                                                                 cint (Int.repr 4) tint32s :: nil) tint32s) :: nil) tint32s) tint32s) tint32s;
                                   is_ebpf := false|}.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   := (_main, AST.Gfun(BeePL.Internal (f_some_match)), None) :: nil.

Definition public_idents : list ident := (_main :: nil).
Definition bcomposites : list bcomposite_definition := nil.

Lemma bcomposite_correct :

  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed.
