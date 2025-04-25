Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* int main() {
     match ref(2) 
     | None option<ref<int>> => -1 (* I want to produce error msg with string *)
     | Some x => let r = !(ref(2)) in r
  }
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _h : ident := $"h".
Definition _p : ident := $"p".
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_p, "p") :: 
                                                       (_r, "r") ::
                                                       (_main, "main") :: nil).

Definition f_null_ptr : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Unsigned dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_p, Otype (Reftype _h (Bprim (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) noattr)) :: 
                                               (_r, Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned noattr)) :: 
                                                nil);
                                   fn_body := Match (Prim (Ref) 
                                                       (Const (ConsInt (Int.repr 2)) (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                                      (Reftype _h (Bprim (Tint Ctypes.I32 Ctypes.Signed dattr)) dattr))
                                              ((Pnone, (Const (ConsInt (Int.repr (-1)%Z)) (Ptype (BeeTypes.Tint I32 Signed dattr)))) ::
                                               (Psome _p, Bind _r (Ptype (Tint Ctypes.I32 Ctypes.Signed dattr))
                                                            (Prim (Deref) 
                                                               (Prim (Ref) (Const (ConsInt (Int.repr 2)) (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                                                     (Reftype _h (Bprim (Tint Ctypes.I32 Ctypes.Signed dattr)) dattr) :: nil) 
                                                               (Ptype (Tint Ctypes.I32 Ctypes.Signed dattr)))
                                                            (Var _r (Ptype (Tint Ctypes.I32 Ctypes.Signed dattr)))
                                                          (Ptype (Tint Ctypes.I32 Ctypes.Signed dattr))) :: nil)
                                               (Ptype (Tint Ctypes.I32 Ctypes.Signed dattr)) |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_null_ptr))) :: nil.

Definition public_idents : list ident := (_main :: nil).

Definition bcomposites : list bcomposite_definition := nil.

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed.
