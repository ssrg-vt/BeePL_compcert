Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux BeePL_Option_Struct.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* This program should not be allowed by the compiler as we only allow option containing pointers *)
(* int main() {
   option<int> r;
   r = Some 4;
   y = match r with
        | None => 0
        | Some x => x
   return y; }
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _r : ident := $"r".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _t : ident := $"t".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_r, "r") :: 
                                                       (_x, "x") ::
                                                       (_y, "y") ::
                                                       (_t, "t") ::
                                                       (_main, "main") :: nil).

Definition f_option1 : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Unsigned dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_r, BeeTypes.Otype (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))) :: 
                                               (_x, (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))) ::
                                               (_y, (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))) :: 
                                               (_t, (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))) :: nil);
                                   fn_body := Bind _t (Ptype Tunit)
                                                 (Prim Massgn ((Var _r (BeeTypes.Otype (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))) :: 
                                                               (Esome (Const (ConsInt (Int.repr 4)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                                   (BeeTypes.Otype (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))) :: nil) 
                                                 (Ptype Tunit))
                                               (Bind _y (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) 
                                                     (Match (Var _r (BeeTypes.Otype (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))))
                                                              (Pnone :: Psome _x :: nil) 
                                                              (Const (ConsInt (Int.repr 0)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)) ::
                                                               Var _x (Ptype (BeeTypes.Tint I32 Unsigned dattr)) :: nil) 
                                                             (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                     (Var _y (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))
                                                (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))
                                               (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))|}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_option1))) :: nil.

Definition public_idents : list ident := (_main :: nil).


Definition bcomposites : list bcomposite_definition := nil.

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed.

(*Compute (get_bcs_from_globdefs (unzip2 global_definitions)).*)
