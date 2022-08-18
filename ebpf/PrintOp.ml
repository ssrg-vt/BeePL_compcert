(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printing of operators, conditions, addressing modes *)

open Printf
open Camlcoq
open Integers
open Op

let comparison_name = function
  | Ceq -> "=="
  | Cne -> "!="
  | Clt -> "<"
  | Cle -> "<="
  | Cgt -> ">"
  | Cge -> ">="

let print_condition reg pp = function
  | (Ccomp c, [r1;r2]) ->
      fprintf pp "%a %ss %a" reg r1 (comparison_name c) reg r2
  | (Ccompu c, [r1;r2]) ->
      fprintf pp "%a %su %a" reg r1 (comparison_name c) reg r2
  | (Ccompimm(c, n), [r1]) ->
      fprintf pp "%a %ss %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompuimm(c, n), [r1]) ->
      fprintf pp "%a %su %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccomp _ , _ ) | Ccompu _ ,_ | Ccompimm _ , _ | Ccompuimm _ ,_  -> assert false
  | (Ccompfs c | Ccompf c) , [r1;r2] -> fprintf pp "%a %sf %a" reg r1 (comparison_name c) reg r2
  | (Cnotcompfs c | Cnotcompf c) , [r1;r2] -> fprintf pp "%a not(%sf) %a" reg r1 (comparison_name c) reg r2
  | _ -> assert false

let print_operation reg pp = function
  | Omove, [r1] -> reg pp r1
  | Ointconst n, [] -> fprintf pp "%ld" (camlint_of_coqint n)
  | Oaddrsymbol(id, ofs), [] ->
      fprintf pp "\"%s\" + %Ld" (extern_atom id) (camlint64_of_ptrofs ofs)
  | Oaddrstack ofs, [] ->
      fprintf pp "stack(%Ld)" (camlint64_of_ptrofs ofs)
  | Oadd, [r1;r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Oaddimm n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Oneg, [r1] -> fprintf pp "-(%a)" reg r1
  | Osub, [r1;r2] -> fprintf pp "%a - %a" reg r1 reg r2
  | Osubimm n, [r1] -> fprintf pp "%a - %ld" reg r1 (camlint_of_coqint n)
  | Omul, [r1;r2] -> fprintf pp "%a * %a" reg r1 reg r2
  | Omulimm n, [r1] -> fprintf pp "%a * %ld" reg r1 (camlint_of_coqint n)
  | Odivu, [r1;r2] -> fprintf pp "%a /u %a" reg r1 reg r2
  | Odivuimm n, [r1] -> fprintf pp "%a /u %ld" reg r1 (camlint_of_coqint n)
  | Omodu, [r1;r2] -> fprintf pp "%a %%u %a" reg r1 reg r2
  | Omoduimm n, [r1] -> fprintf pp "%a %%u %ld" reg r1 (camlint_of_coqint n)
  | Oand, [r1;r2] -> fprintf pp "%a & %a" reg r1 reg r2
  | Oandimm n, [r1] -> fprintf pp "%a & %ld" reg r1 (camlint_of_coqint n)
  | Oor, [r1;r2] -> fprintf pp "%a | %a" reg r1 reg r2
  | Oorimm n, [r1] ->  fprintf pp "%a | %ld" reg r1 (camlint_of_coqint n)
  | Oxor, [r1;r2] -> fprintf pp "%a ^ %a" reg r1 reg r2
  | Oxorimm n, [r1] -> fprintf pp "%a ^ %ld" reg r1 (camlint_of_coqint n)
  | Oshl, [r1;r2] -> fprintf pp "%a << %a" reg r1 reg r2
  | Oshlimm n, [r1] -> fprintf pp "%a << %ld" reg r1 (camlint_of_coqint n)
  | Oshr, [r1;r2] -> fprintf pp "%a >>s %a" reg r1 reg r2
  | Oshrimm n, [r1] -> fprintf pp "%a >>s %ld" reg r1 (camlint_of_coqint n)
  | Oshru, [r1;r2] -> fprintf pp "%a >>u %a" reg r1 reg r2
  | Oshruimm n, [r1] -> fprintf pp "%a >>u %ld" reg r1 (camlint_of_coqint n)
  | Ocmp c, args -> print_condition reg pp (c, args)
  | Ocast8signed, [r1] -> fprintf pp "(8s) %a" reg r1
  | Ocast16signed, [r1] -> fprintf pp "(16s) %a" reg r1
  | Omulhs , [r1;r2]    -> fprintf pp "mulhs(%a,%a)" reg r1 reg r2
  | Omulhu , [r1;r2]    -> fprintf pp "mulhu(%a,%a)" reg r1 reg r2
  | Omod , [r1;r2]    -> fprintf pp "%a mod %a)" reg r1 reg r2
  | Omakelong, [r1;r2]   -> fprintf pp "makelong(%a,%a)" reg r1 reg r2
  | Olowlong, [r1]       -> fprintf pp "lowlong(%a)" reg r1
  | Ohighlong , [r1]       -> fprintf pp "highlong(%a)" reg r1
  | Onegf     , [r1]       -> fprintf pp "negf(%a)" reg r1
  | Oabsf     , [r1]       -> fprintf pp "absf(%a)" reg r1
  | Oaddf     , [r1;r2]    -> fprintf pp "%a +f %a" reg r1 reg r2
  | Osubf     , [r1;r2]    -> fprintf pp "%a -f %a" reg r1 reg r2
  | Omulf     , [r1;r2]    -> fprintf pp "%a *f %a" reg r1 reg r2
  | Odivf    , [r1;r2]    -> fprintf pp "%a /f %a" reg r1 reg r2
  | Onegfs     , [r1]       -> fprintf pp "negfs(%a)" reg r1
  | Oabsfs     , [r1]       -> fprintf pp "absfs(%a)" reg r1
  | Oaddfs     , [r1;r2]    -> fprintf pp "%a +s %a" reg r1 reg r2
  | Osubfs     , [r1;r2]    -> fprintf pp "%a -s %a" reg r1 reg r2
  | Omulfs     , [r1;r2]    -> fprintf pp "%a *s %a" reg r1 reg r2
  | Odivfs    , [r1;r2]    -> fprintf pp "%a /s %a" reg r1 reg r2
  | Osingleoffloat , [r]   -> fprintf pp "singleoffloat(%a)" reg r
  | Ofloatofsingle , [r]   -> fprintf pp "floatofsingle(%a)" reg r
  | Ointoffloat, [r]   -> fprintf pp "intoffloat(%a)" reg r
  | Ointuoffloat , [r]   -> fprintf pp "intuoffloat(%a)" reg r
  | Ofloatofint, [r]   -> fprintf pp "floatofint(%a)" reg r
  | Ofloatofintu , [r]   -> fprintf pp "floatofintu(%a)" reg r
  | Ointofsingle , [r]   -> fprintf pp "intofsingle(%a)" reg r
  | Ointuofsingle, [r]   -> fprintf pp "intuofsingle(%a)" reg r
  | Osingleofint,  [r]   -> fprintf pp "singleofint(%a)" reg r
  | Osingleofintu, [r]   -> fprintf pp "singleofintu(%a)" reg r
  | Olongoffloat, [r] -> fprintf pp "longoffloat(%a)" reg r
  | Olonguoffloat,[r] -> fprintf pp "longuoffloat(%a)" reg r
  | Ofloatoflong, [r] -> fprintf pp "floatoflong(%a)" reg r
  | Ofloatoflongu,[r] -> fprintf pp "floatoflongu(%a)" reg r
  | Olongofsingle,[r] -> fprintf pp "longofsingle(%a)" reg r
  | Olonguofsingle,[r] -> fprintf pp "longuofsingle(%a)" reg r
  | Osingleoflong,[r] -> fprintf pp "singleofsingle(%a)" reg r
  | Osingleoflongu,[r]-> fprintf pp "singleoflongu(%a)" reg r
  | Ofloatconst n , [] -> fprintf pp "%F" (camlfloat_of_coqfloat n)
  | Osingleconst n, [] -> fprintf pp "%Ff" (camlfloat_of_coqfloat32 n)
  | _ -> fprintf pp "<bad operator>"

let print_addressing reg pp = function
  | Aindexed n, [r1] -> fprintf pp "%a + %Ld" reg r1 (camlint64_of_ptrofs n)
  | Ainstack ofs, [] -> fprintf pp "stack(%Ld)" (camlint64_of_ptrofs ofs)
  | _ -> fprintf pp "<bad addressing>"
