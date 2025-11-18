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
    // Helper returns: (u64)(pid | (tgid << 32))
    u64 pid_tgid = bpf_get_current_pid_tgid();

    // Extract individual fields
    u32 pid = pid_tgid & 0xFFFFFFFF;
    u32 tgid = pid_tgid >> 32;

    bpf_printk("PID: %d, TGID: %d\n", pid, tgid);

    return XDP_PASS;
}

char LICENSE[] SEC("license") = "GPL"; *) 


(*Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _ctx : ident := $"ctx".
Definition _pid_tgid : ident := $"pid_tgid".
Definition _pid : ident := $"pid".
Definition _tgid : ident := $"tgid".
Definition _r : ident := $"r".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___license : ident := $"__license".
Definition _xdp_pid_tgid : ident := $"xdp_pid_tgid".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ident_to_string_hf ++ ident_to_string_xdp_md ++
                                                      ((_ctx, "ctx") :: (___stringlit_1, "__stringlit_1") :: (___license, "___license") ::
                                                       (_pid_tgid, "pid_tgid") :: (_pid, "pid") :: (_tgid, "tgid") :: (_r, "r") ::
                                                       (_xdp_pid_tgid, "xdp_pid_tgid") :: 
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
  gvar_info := (tbarray tint8s 19 noattr);
  gvar_init := (Init_int8 (Int.repr 80) :: (* 'P' *)
                Init_int8 (Int.repr 73) :: (* 'I' *)
                Init_int8 (Int.repr 68) :: (* 'D' *)
                Init_int8 (Int.repr 58) :: (* ':' *)
                Init_int8 (Int.repr 32) :: (* '' *)
                Init_int8 (Int.repr 37) :: (* '%' *)
                Init_int8 (Int.repr 100) :: (* 'd' *)
                Init_int8 (Int.repr 44) :: (* ',' *)
                Init_int8 (Int.repr 32) :: (* '' *)
                Init_int8 (Int.repr 84) :: (* 'T' *)
                Init_int8 (Int.repr 71) :: (* 'G' *)
                Init_int8 (Int.repr 73) :: (* 'I' *)
                Init_int8 (Int.repr 68) :: (* 'D' *)
                Init_int8 (Int.repr 58) :: (* ':' *)
                Init_int8 (Int.repr 32) :: (* '' *)
                Init_int8 (Int.repr 37) :: (* '%' *)
                Init_int8 (Int.repr 100) :: (* 'd' *)
                Init_int8 (Int.repr 10) :: (* '\n' *)
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.


Definition f_xdp_pid_tgid : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := (Io :: Io :: nil);
                                   fn_callconv := cc_default;
                                   fn_args := (_ctx, tpstruct _xdp_md) :: nil;
                                   fn_vars := (_pid_tgid, tlongu) :: (_pid, tint32s) :: (_tgid, tint32s) :: (_r, tint32s) :: nil;
                                   fn_body := Bind _pid_tgid tlongu 
                                                (App (Var bpf_get_current_pid_tgid (tfun nil nil tlongu)) nil tlongu)
                                                (Bind _pid tint32s
                                                      (Prim (Cast tint32s) 
                                                         (Prim (Bop Cop.Oand) (Var _pid_tgid tlongu :: clong (Int64.repr 4294967295) tlongu :: nil) tlongu :: nil) tint32s)
                                                      (Bind _tgid tint32s
                                                            (Prim (Cast tint32s)
                                                               (Prim (Bop Cop.Oshr) (Var _pid_tgid tlongu :: clong (Int64.repr 32) tlongu :: nil) tlongu :: nil) tint32s)
                                                            (Bind _r tint32s
                                                                  (App (Var bpf_printk (tfun (trint8s :: tint32s :: tint32s :: tint32s :: nil) (Io :: nil) tint32s))
                                                                  (Var ___stringlit_1 (tbarray tint8s 19 noattr) :: cint (Int.repr 19) tint32s :: 
                                                                   Var _pid tint32s :: 
                                                                   Var _tgid tint32s :: nil) tint32s)
                                                             (cint (Int.repr 2) tint32s) tint32s) tint32s) tint32s) tint32s;
                                                                  
                                                      
                                   is_ebpf := true |}.

Definition bcomposites : list bcomposite_definition := bcomposites_xdp_md.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef BeeTypes.type * option string) 
   :=  (___license, Gvar v___license, Some "license") ::
       (___stringlit_1, Gvar v___stringlit_1, None) ::
       (bpf_get_current_pid_tgid, AST.Gfun(BeePL.External bpf_get_current_pid_tgid_ef
                                     nil tlongu
                                     (cc_default)), None) :: 
       (bpf_printk, AST.Gfun(BeePL.External bpf_printk_ef
                                     (trint8s :: tint32s :: tint32s :: tint32s :: nil) tint32s
                                     {|cc_vararg:=(Some (Z.of_nat 1)); cc_unproto:=false; cc_structret:=false|}), None) ::
       (_xdp_pid_tgid, AST.Gfun(BeePL.Internal (f_xdp_pid_tgid)), Some "xdp") :: nil.

Definition public_idents : list ident := (_xdp_pid_tgid :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.*)

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _xdp_pid_tgid 
                                                   bcomposite_correct
                                                   ident_to_string.

Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_xdp_pid_tgid.(fn_args)) f_xdp_pid_tgid.(fn_vars)) empty_context f_xdp_pid_tgid.(fn_body)).

Compute (type_check_program example1). *) (* Type checks! *)

