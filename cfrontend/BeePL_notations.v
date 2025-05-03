Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Ctyping Cop.
Require Import BeePL_aux BeePL BeePL_values BeeTypes BeePL_mem Errors Csyntaxdefs Csyntax Ctypesdefs.
From mathcomp Require Import all_ssreflect. 
Import Csyntaxdefs.CsyntaxNotations.
                                      
Definition ctrue := (Const (ConsBool true)).
Definition cfalse := (Const (ConsBool false)).
Definition cint i := (Const (ConsInt i)).
Definition clong l := (Const (ConsLong l)). 
Definition cunit := (Const ConsUnit).
Definition pbool := Tbool.
Definition pint8u := Tint I8 Unsigned noattr.
Definition pint8s := Tint I8 Signed noattr.
Definition pint16u := Tint I16 Unsigned noattr.
Definition pint16s := Tint I16 Signed noattr.
Definition pint32u := Tint I32 Unsigned noattr.
Definition pint32s := Tint I32 Signed noattr.
Definition plongu := Tlong Unsigned noattr.
Definition plongs := Tlong Signed noattr.
Definition punit := Utype.

Definition bbool := Bprim pbool.
Definition bint8u := Bprim pint8u.
Definition bint8s := Bprim pint8s.
Definition bint16u := Bprim pint16u.
Definition bint16s := Bprim pint16s.
Definition bint32u := Bprim pint32u.
Definition bint32s := Bprim pint32s.
Definition blongu := Bprim plongu.
Definition blongs := Bprim plongs.
Definition bstruct x := Bstruct x noattr.

Definition tbool := Vtype pbool.
Definition tint8u := Vtype pint8u.
Definition tint8s := Vtype pint8s.
Definition tint16u := Vtype pint16u.
Definition tint16s := Vtype pint16s.
Definition tint32u := Vtype pint32u.
Definition tint32s := Vtype pint32s.
Definition tlongu := Vtype plongu.
Definition tlongs := Vtype plongs.

Definition trbool {h} := Reftype h bbool noattr.
Definition trint8u {h} := Reftype h bint8u noattr.
Definition trint8s {h} := Reftype h bint8s noattr.
Definition trint16u {h} := Reftype h bint16u noattr.
Definition trint16s {h} := Reftype h bint16s noattr.
Definition trint32u {h} := Reftype h bint32u noattr.
Definition trint32s {h} := Reftype h bint32s noattr.
Definition trlongu {h} := Reftype h blongu noattr.
Definition trlongs {h} := Reftype h blongs noattr.
Definition trstruct x {h} := Reftype h (bstruct x) noattr.
Definition tfun ts ef t := Ftype ts ef t.
Definition tstruct x := Stype x noattr.
Definition toption t := Otype t.


