Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* int main() {

     return r;
  }
*)

(* attr_alignas is optional *)
(*Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _r : ident := $"r".
Definition _tmp_1000 : ident := $"_tmp_1000".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_x, "x") :: 
                                                       (_y, "y") :: 
                                                       (_r, "r") ::
                                                       (_main, "main") :: nil).

Definition f_ref : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := nil;
                                   fn_body := Prim (Ref) 
                                                   (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                                   (Reftype _y (Bprim (Tint Ctypes.I32 Ctypes.Signed dattr)) dattr)
                                                |}.

(* Swarn said this should be rejected by the typechecker *)
Definition f_ref2 : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: nil);
                                   fn_body := Bind 
                                                (_x) 
                                                (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                                (Const (ConsInt (Int.repr 2)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                ((Bind 
                                                      (_r) 
                                                      (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                                      (Prim (Ref) 
                                                            (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                                            (Reftype _y (Bprim (Tint Ctypes.I32 Ctypes.Signed dattr)) dattr))
                                                      (Var _x (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                      (Ptype (BeeTypes.Tint I32 Unsigned dattr))))
                                                (Ptype (BeeTypes.Tint I32 Unsigned dattr)) |}.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_ref))) :: nil.

Definition public_idents : list ident := (_main :: nil).*)
