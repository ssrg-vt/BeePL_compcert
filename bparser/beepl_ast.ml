type effect = 
  | Read of string 
  | Write of string 
  | Alloc of string 
  | Io

type ptype = 
  | Tbool
  | Tint32
  | Tlong

type typ = 
  | Utype
  | Vtype of ptype 

type const = 
  | Cunit 
  | Cbool of bool
  | Cint32 of int32
  | Clong of int64

(** The type of the abstract syntax tree (AST). *)
type expr =
  | Var of string 
  | Const of const
  | Let of string * typ * expr * expr
  | If of expr * expr * expr

type fundecl = 
  | Tfundecl of string * typ * effect * (string * typ) list * (string * typ) list * expr * bool

type toplevel = 
  | Internal of fundecl 

type program = toplevel list

  

  