Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes.
Require Import BeePL_aux BeePL BeeTypes BeePL_mem.

(***** Type checker for BeePL *****)

Definition type_constant (c : constant) : type :=
match c with 
| ConsInt i => (Ptype Tint)
| ConsUint i => (Ptype Tuint)
| ConsBool b => (Ptype Tbool)
| ConsUnit => (Ptype Tunit)
end.
