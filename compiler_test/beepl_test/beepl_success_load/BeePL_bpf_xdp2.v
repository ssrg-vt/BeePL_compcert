Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations BeePL_bpf. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>

SEC("xdp")
int xdp_prog(struct xdp_md *ctx) {
    bpf_printk("Hello");
    return XDP_PASS;
}

char _license[] SEC("license") = "Dual BSD/GPL"; *)


Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _ctx : ident := $"ctx".
Definition _r : ident := $"r".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___license : ident := $"__license".
Definition _xdp_packet_count : ident := $"xdp_packet_count".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ident_to_string_hf ++ ident_to_string_xdp_md ++
                                                      ((_ctx, "ctx") :: (___stringlit_1, "__stringlit_1") :: (___license, "___license") ::
                                                       (_r, "r") ::
                                                       (_xdp_packet_count, "xdp_packet_count") :: 
                                                       (_main, "main") :: nil).

Definition v___license := {|
  gvar_info := tbarray tint8s 4 noattr;
  gvar_init := (Init_int8 (Int.repr 71) ::  (* 'G' *)
                Init_int8 (Int.repr 80) ::  (* 'P' *)
                Init_int8 (Int.repr 76) ::  (* 'L' *)
                Init_int8 (Int.repr 0) :: nil);  (* '\0' *)
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tbarray tint8s 6 noattr);
  gvar_init := (Init_int8 (Int.repr 72) :: (* 'H' *)
                Init_int8 (Int.repr 101) :: (* 'e' *)
                Init_int8 (Int.repr 108) :: (* 'l' *)
                Init_int8 (Int.repr 108) :: (* 'l' *)
                Init_int8 (Int.repr 111) :: (* 'o' *)
                Init_int8 (Int.repr 0) :: nil); (* '\0' *)
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_xdp_packet_count : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := (Io :: nil);
                                   fn_callconv := cc_default;
                                   fn_args := (_ctx, tpstruct _xdp_md) :: nil ;
                                   fn_vars := (_r, tint32s) :: nil;
                                   fn_body := Bind _r tint32s 
                                                (App (Var bpf_printk (tfun (trint8s :: nil) (Io :: nil) tint32s))
                                                                  (Var ___stringlit_1 (tbarray tint8s 6 noattr) :: nil) tint32s)
                                                (cint (Int.repr 2) tint32s) tint32s;
                                   is_ebpf := true |}.

Definition bcomposites : list bcomposite_definition := bcomposites_xdp_md.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef BeeTypes.type * option string) 
   :=  (___license, Gvar v___license, Some "license") ::
       (___stringlit_1, Gvar v___stringlit_1, None) ::
       (bpf_printk, AST.Gfun(BeePL.External bpf_printk_ef
                                     (trint8s :: nil) tint32s
                                     {|cc_vararg:=(Some (Z.of_nat 1)); cc_unproto:=false; cc_structret:=false|}), None) ::
       (_xdp_packet_count, AST.Gfun(BeePL.Internal (f_xdp_packet_count)), Some "xdp") :: nil.

Definition public_idents : list ident := (_xdp_packet_count :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _xdp_packet_count 
                                                   bcomposite_correct
                                                   ident_to_string.

Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_xdp_packet_count.(fn_args)) f_xdp_packet_count.(fn_vars)) empty_context f_xdp_packet_count.(fn_body)).


Compute (type_check_program example1). *) (* Type checks! *)
