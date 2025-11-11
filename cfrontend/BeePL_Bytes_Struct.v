Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib SimplExpr.
Require Import BeePL_aux BeePL BeeTypes Csyntax Errors SimplExpr BeePL_values DecimalString BeePL_notations.
From compcert Require Import Csyntaxdefs. 
Import Csyntaxdefs.CsyntaxNotations.

Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.
Local Open Scope list_scope.
Local Open Scope csyntax_scope.

(* ---------------------------------------------------------------------- *)
(*    Collecting all uses of the BeePL [bytes] type                        *)
(* ---------------------------------------------------------------------- *)

Fixpoint filter_bytes (l : list type) : list type :=
  match l with
  | nil => nil
  | Bytes :: xs => Bytes :: filter_bytes xs
  | _ :: xs      => filter_bytes xs
  end.

Fixpoint mem_type (t : type) (l : list type) : bool :=
  match l with
  | nil => false
  | x :: xs =>
      if eq_type t x
      then true
      else mem_type t xs
  end.

Fixpoint remove_duplicate_type (l : list type) : list type :=
  match l with
  | nil => nil
  | x :: xs =>
      let rest := remove_duplicate_type xs in
      if mem_type x rest then rest else x :: rest
  end.

Definition unique_bytes_types (l : list type) : list type :=
  remove_duplicate_type (filter_bytes l).

(* ---------------------------------------------------------------------- *)
(*    Composite definition for BeePL [bytes]                               *)
(* ---------------------------------------------------------------------- *)

(* Identifiers reserved for bytes *)
Definition bytes_t     : ident := $"bytes_t".
Definition bytes_start : ident := $"bytes_start".
Definition bytes_end   : ident := $"bytes_end".

Definition ident_to_string_bytes : list (ident * string) :=
  ( (bytes_t,     "bytes_t")
  :: (bytes_start,"bytes_start")
  :: (bytes_end,  "bytes_end") :: nil).

Fixpoint get_bcs_from_types (ots : list type) : list composite_definition :=
  match ots with
  | nil => nil
  | Bytes :: bts_tail =>
      let nbc :=
        Composite bytes_t Struct
          ( Ctypes.Member_plain bytes_start (tptr tuchar)
          :: Ctypes.Member_plain bytes_end   (tptr tuchar)
          :: nil) noattr in
      let nbc' := get_bcs_from_types bts_tail in
      nbc :: nbc'
  | _ :: bts_tail =>
      get_bcs_from_types bts_tail
  end.

Definition get_bcs_from_vars (vars : list (ident * type)) : list composite_definition :=
  let ts  := map snd vars in
  let ots := unique_bytes_types ts in
  get_bcs_from_types ots.

(* Test *)
(*
Definition x : ident := 1%positive.
Definition y : ident := 2%positive.
Definition s : ident := 3%positive.
Definition sf1 : ident := 4%positive.
Compute (get_bcs_from_vars ((x, Bytes) :: (y, Bytes) :: nil)).
*)

Definition get_bcs_from_function (fn : BeePL.function) : list composite_definition :=
  let vars := fn.(BeePL.fn_vars) in
  get_bcs_from_vars vars.

Definition get_bcs_from_fundef (fd : BeePL.fundef) : list composite_definition :=
  match fd with
  | Internal f           => get_bcs_from_function f
  | External _ _ _ _     => nil
  end.

Definition get_bcs_from_globdef
           (gd : BeePL.globdef BeePL.fundef BeeTypes.type)
  : list composite_definition :=
  match gd with
  | AST.Gfun f => get_bcs_from_fundef f
  | AST.Gvar _ => nil
  end.

(* ---------------------------------------------------------------------- *)
(*    De-duplicate composites (avoid multiple [Composite bytes_t ...])     *)
(* ---------------------------------------------------------------------- *)

Fixpoint mem_composite_id (id : ident) (l : list composite_definition) : bool :=
  match l with
  | nil => false
  | Composite id' _ _ _ :: xs =>
      if ident_eq id id'
      then true
      else mem_composite_id id xs
  end.

Fixpoint remove_duplicate_composites (l : list composite_definition)
  : list composite_definition :=
  match l with
  | nil => nil
  | (Composite id k m a as c) :: xs =>
      let rest := remove_duplicate_composites xs in
      if mem_composite_id id rest
      then rest
      else c :: rest
  end.

(* Internal recursive helper: just concatenates composites from each globdef *)
Fixpoint get_bcs_from_globdefs_aux
         (gd : list (BeePL.globdef BeePL.fundef BeeTypes.type))
  : list composite_definition :=
  match gd with
  | nil => nil
  | d :: ds =>
      let nbc  := get_bcs_from_globdef d in
      let nbc' := get_bcs_from_globdefs_aux ds in
      nbc ++ nbc'
  end.

(* Public function used by BeePL_Csyntax.v *)
Definition get_bcs_from_globdefs
           (gd : list (BeePL.globdef BeePL.fundef BeeTypes.type))
  : list composite_definition :=
  remove_duplicate_composites (get_bcs_from_globdefs_aux gd).



