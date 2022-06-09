Require Import String.
Require Import AST.
Require Import Builtins0.

Inductive platform_builtin: Type.

Definition platform_builtin_sig (b: platform_builtin) : signature :=
  mksignature (Tfloat :: Tfloat :: nil) Tfloat cc_default.

Definition platform_builtin_table : list (string * platform_builtin) := nil.

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  mkbuiltin_n2t Tfloat Tfloat Tfloat (fun f1 f2 => f1).
