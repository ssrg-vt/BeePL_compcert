
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | XOR
    | WRITE
    | WITH
    | UP
    | UNIT
    | ULONGTYPE
    | UINT8TYPE
    | UINT32TYPE
    | UINT16TYPE
    | TSTRUCT
    | TILDE
    | THEN
    | STRUCT
    | STRING of (
# 37 "bparser/beepl_parser.mly"
       (string)
# 28 "bparser/beepl_parser.ml"
  )
    | STAR
    | SINIT
    | SHR
    | SHL
    | SECTION of (
# 38 "bparser/beepl_parser.mly"
       (string)
# 37 "bparser/beepl_parser.ml"
  )
    | RULONGTYPE
    | RUINT8TYPE
    | RUINT32TYPE
    | RUINT16TYPE
    | RSTRUCT
    | RPAREN
    | RLONGTYPE
    | RINT8TYPE
    | RINT32TYPE
    | RINT16TYPE
    | REF
    | READ
    | RBRACK
    | RBRACE
    | RBOOLTYPE
    | RAULONG
    | RAUINT8
    | RAUINT32
    | RAUINT16
    | RARRAY
    | RALONG
    | RAINT8
    | RAINT32
    | RAINT16
    | RABOOL
    | PLUS
    | PBYTES
    | OSOME
    | ORULONGTYPE
    | ORUINT8TYPE
    | ORUINT32TYPE
    | ORUINT16TYPE
    | ORSTRUCT
    | ORLONGTYPE
    | ORINT8TYPE
    | ORINT32TYPE
    | ORINT16TYPE
    | ORBOOLTYPE
    | ORAULONG
    | ORAUINT8
    | ORAUINT32
    | ORAUINT16
    | ORARRAY
    | ORALONG
    | ORAINT8
    | ORAINT32
    | ORAINT16
    | ORABOOL
    | OR
    | ONONE
    | OEQ
    | NEQ
    | NEG
    | MUL
    | MOD
    | MINUS
    | MATCH
    | MASSGN
    | LT
    | LPAREN
    | LONGTYPE
    | LET
    | LE
    | LBRACK
    | LBRACE
    | IO
    | INT8TYPE
    | INT64 of (
# 7 "bparser/beepl_parser.mly"
       (int64)
# 109 "bparser/beepl_parser.ml"
  )
    | INT32TYPE
    | INT32 of (
# 6 "bparser/beepl_parser.mly"
       (int32)
# 115 "bparser/beepl_parser.ml"
  )
    | INT16TYPE
    | IN
    | IF
    | IDENT of (
# 5 "bparser/beepl_parser.mly"
       (string)
# 123 "bparser/beepl_parser.ml"
  )
    | HASHEBPF
    | GT
    | GE
    | FUNTYPE
    | FUNC
    | FOR
    | EQ
    | EOF
    | EMPTYBRACKETS
    | ELSE
    | DOWN
    | DOT
    | DIVERGENCE
    | DIV
    | DEREF
    | COMMA
    | COLON
    | CAST
    | BYTES
    | BOOLTYPE
    | BOOL of (
# 8 "bparser/beepl_parser.mly"
       (bool)
# 148 "bparser/beepl_parser.ml"
  )
    | BAR
    | ARROW
    | ARRAY
    | AND
    | ALLOC
    | AINIT
    | AACEESS
  
end

include MenhirBasics

# 1 "bparser/beepl_parser.mly"
  
open Beepl_ast

# 166 "bparser/beepl_parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState000 : ('s, _menhir_box_prog) _menhir_state
    (** State 000.
        Stack shape : .
        Start symbol: prog. *)

  | MenhirState003 : (('s, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 003.
        Stack shape : STRUCT IDENT.
        Start symbol: prog. *)

  | MenhirState005 : (('s, _menhir_box_prog) _menhir_cell1_IDENT, _menhir_box_prog) _menhir_state
    (** State 005.
        Stack shape : IDENT.
        Start symbol: prog. *)

  | MenhirState107 : (('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 107.
        Stack shape : LPAREN.
        Start symbol: prog. *)

  | MenhirState114 : (('s, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_state
    (** State 114.
        Stack shape : FUNTYPE.
        Start symbol: prog. *)

  | MenhirState118 : (('s, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 118.
        Stack shape : typ.
        Start symbol: prog. *)

  | MenhirState121 : (('s, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 121.
        Stack shape : typ.
        Start symbol: prog. *)

  | MenhirState126 : ((('s, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__, _menhir_box_prog) _menhir_state
    (** State 126.
        Stack shape : FUNTYPE loption(separated_nonempty_list(COMMA,typ)).
        Start symbol: prog. *)

  | MenhirState137 : (((('s, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_effect__, _menhir_box_prog) _menhir_state
    (** State 137.
        Stack shape : FUNTYPE loption(separated_nonempty_list(COMMA,typ)) loption(separated_nonempty_list(COMMA,effect)).
        Start symbol: prog. *)

  | MenhirState140 : (('s, _menhir_box_prog) _menhir_cell1_effect, _menhir_box_prog) _menhir_state
    (** State 140.
        Stack shape : effect.
        Start symbol: prog. *)

  | MenhirState147 : (('s, _menhir_box_prog) _menhir_cell1_field_decl, _menhir_box_prog) _menhir_state
    (** State 147.
        Stack shape : field_decl.
        Start symbol: prog. *)

  | MenhirState149 : (('s, _menhir_box_prog) _menhir_cell1_SECTION, _menhir_box_prog) _menhir_state
    (** State 149.
        Stack shape : SECTION.
        Start symbol: prog. *)

  | MenhirState150 : (('s, _menhir_box_prog) _menhir_cell1_HASHEBPF, _menhir_box_prog) _menhir_state
    (** State 150.
        Stack shape : HASHEBPF.
        Start symbol: prog. *)

  | MenhirState155 : (('s, _menhir_box_prog) _menhir_cell1_toplevel, _menhir_box_prog) _menhir_state
    (** State 155.
        Stack shape : toplevel.
        Start symbol: prog. *)

  | MenhirState160 : (('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 160.
        Stack shape : annotations IDENT.
        Start symbol: prog. *)

  | MenhirState162 : ((('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 162.
        Stack shape : annotations IDENT typ.
        Start symbol: prog. *)

  | MenhirState164 : (('s, _menhir_box_prog) _menhir_cell1_TILDE, _menhir_box_prog) _menhir_state
    (** State 164.
        Stack shape : TILDE.
        Start symbol: prog. *)

  | MenhirState167 : (('s, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 167.
        Stack shape : STRUCT IDENT.
        Start symbol: prog. *)

  | MenhirState169 : (('s, _menhir_box_prog) _menhir_cell1_IDENT, _menhir_box_prog) _menhir_state
    (** State 169.
        Stack shape : IDENT.
        Start symbol: prog. *)

  | MenhirState173 : ((('s, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_separated_nonempty_list_COMMA_IDENT_, _menhir_box_prog) _menhir_state
    (** State 173.
        Stack shape : STRUCT IDENT separated_nonempty_list(COMMA,IDENT).
        Start symbol: prog. *)

  | MenhirState175 : (('s, _menhir_box_prog) _menhir_cell1_REF, _menhir_box_prog) _menhir_state
    (** State 175.
        Stack shape : REF.
        Start symbol: prog. *)

  | MenhirState176 : (('s, _menhir_box_prog) _menhir_cell1_OSOME, _menhir_box_prog) _menhir_state
    (** State 176.
        Stack shape : OSOME.
        Start symbol: prog. *)

  | MenhirState177 : (('s, _menhir_box_prog) _menhir_cell1_ONONE, _menhir_box_prog) _menhir_state
    (** State 177.
        Stack shape : ONONE.
        Start symbol: prog. *)

  | MenhirState179 : (('s, _menhir_box_prog) _menhir_cell1_MINUS, _menhir_box_prog) _menhir_state
    (** State 179.
        Stack shape : MINUS.
        Start symbol: prog. *)

  | MenhirState180 : (('s, _menhir_box_prog) _menhir_cell1_MATCH, _menhir_box_prog) _menhir_state
    (** State 180.
        Stack shape : MATCH.
        Start symbol: prog. *)

  | MenhirState181 : (('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 181.
        Stack shape : LPAREN.
        Start symbol: prog. *)

  | MenhirState185 : ((('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 185.
        Stack shape : LPAREN LPAREN.
        Start symbol: prog. *)

  | MenhirState188 : (('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 188.
        Stack shape : LET IDENT.
        Start symbol: prog. *)

  | MenhirState190 : ((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 190.
        Stack shape : LET IDENT typ.
        Start symbol: prog. *)

  | MenhirState191 : (((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_LBRACE, _menhir_box_prog) _menhir_state
    (** State 191.
        Stack shape : LET IDENT typ LBRACE.
        Start symbol: prog. *)

  | MenhirState194 : (('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_state
    (** State 194.
        Stack shape : IF.
        Start symbol: prog. *)

  | MenhirState200 : (('s, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_state
    (** State 200.
        Stack shape : FOR.
        Start symbol: prog. *)

  | MenhirState201 : (('s, _menhir_box_prog) _menhir_cell1_DEREF, _menhir_box_prog) _menhir_state
    (** State 201.
        Stack shape : DEREF.
        Start symbol: prog. *)

  | MenhirState204 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 204.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState209 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 209.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState211 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 211.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState213 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 213.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState215 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 215.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState220 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 220.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState222 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 222.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState224 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 224.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState226 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 226.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState228 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 228.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState230 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 230.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState232 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 232.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState234 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 234.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState236 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 236.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState238 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 238.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState240 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 240.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState242 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 242.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState244 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 244.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState246 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 246.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState249 : ((('s, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 249.
        Stack shape : FOR expr.
        Start symbol: prog. *)

  | MenhirState255 : (((('s, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_dir, _menhir_box_prog) _menhir_state
    (** State 255.
        Stack shape : FOR expr expr dir.
        Start symbol: prog. *)

  | MenhirState259 : ((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 259.
        Stack shape : IF expr.
        Start symbol: prog. *)

  | MenhirState261 : (((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 261.
        Stack shape : IF expr expr.
        Start symbol: prog. *)

  | MenhirState267 : (((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 267.
        Stack shape : LET IDENT typ expr.
        Start symbol: prog. *)

  | MenhirState270 : (((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_array_elems, _menhir_box_prog) _menhir_state
    (** State 270.
        Stack shape : LET IDENT typ array_elems.
        Start symbol: prog. *)

  | MenhirState273 : ((('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 273.
        Stack shape : LPAREN typ.
        Start symbol: prog. *)

  | MenhirState280 : ((('s, _menhir_box_prog) _menhir_cell1_MATCH, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_option_BAR_, _menhir_box_prog) _menhir_state
    (** State 280.
        Stack shape : MATCH expr option(BAR).
        Start symbol: prog. *)

  | MenhirState283 : (('s, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 283.
        Stack shape : PBYTES IDENT.
        Start symbol: prog. *)

  | MenhirState285 : ((('s, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 285.
        Stack shape : PBYTES IDENT typ.
        Start symbol: prog. *)

  | MenhirState288 : (('s, _menhir_box_prog) _menhir_cell1_IDENT, _menhir_box_prog) _menhir_state
    (** State 288.
        Stack shape : IDENT.
        Start symbol: prog. *)

  | MenhirState294 : (('s, _menhir_box_prog) _menhir_cell1_bytes_field, _menhir_box_prog) _menhir_state
    (** State 294.
        Stack shape : bytes_field.
        Start symbol: prog. *)

  | MenhirState298 : ((('s, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ _menhir_cell0_bytes_fields, _menhir_box_prog) _menhir_state
    (** State 298.
        Stack shape : PBYTES IDENT typ bytes_fields.
        Start symbol: prog. *)

  | MenhirState302 : (('s, _menhir_box_prog) _menhir_cell1_OSOME _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 302.
        Stack shape : OSOME IDENT.
        Start symbol: prog. *)

  | MenhirState305 : (('s, _menhir_box_prog) _menhir_cell1_ONONE, _menhir_box_prog) _menhir_state
    (** State 305.
        Stack shape : ONONE.
        Start symbol: prog. *)

  | MenhirState309 : (('s, _menhir_box_prog) _menhir_cell1_clause, _menhir_box_prog) _menhir_state
    (** State 309.
        Stack shape : clause.
        Start symbol: prog. *)

  | MenhirState320 : (('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 320.
        Stack shape : annotations IDENT.
        Start symbol: prog. *)

  | MenhirState326 : ((('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_state
    (** State 326.
        Stack shape : annotations IDENT loption(separated_nonempty_list(COMMA,arg)).
        Start symbol: prog. *)

  | MenhirState328 : (((('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 328.
        Stack shape : annotations IDENT loption(separated_nonempty_list(COMMA,arg)) typ.
        Start symbol: prog. *)

  | MenhirState332 : ((((('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_effect_list, _menhir_box_prog) _menhir_state
    (** State 332.
        Stack shape : annotations IDENT loption(separated_nonempty_list(COMMA,arg)) typ effect_list.
        Start symbol: prog. *)

  | MenhirState336 : (('s, _menhir_box_prog) _menhir_cell1_arg, _menhir_box_prog) _menhir_state
    (** State 336.
        Stack shape : arg.
        Start symbol: prog. *)


and ('s, 'r) _menhir_cell1_annotations = 
  | MenhirCell1_annotations of 's * ('s, 'r) _menhir_state * (bool * string option)

and ('s, 'r) _menhir_cell1_arg = 
  | MenhirCell1_arg of 's * ('s, 'r) _menhir_state * (string * Beepl_ast.typ)

and ('s, 'r) _menhir_cell1_array_elems = 
  | MenhirCell1_array_elems of 's * ('s, 'r) _menhir_state * (Beepl_ast.expr list)

and ('s, 'r) _menhir_cell1_bytes_field = 
  | MenhirCell1_bytes_field of 's * ('s, 'r) _menhir_state * (string * Beepl_ast.typ)

and 's _menhir_cell0_bytes_fields = 
  | MenhirCell0_bytes_fields of 's * ((string * Beepl_ast.typ) list)

and ('s, 'r) _menhir_cell1_clause = 
  | MenhirCell1_clause of 's * ('s, 'r) _menhir_state * (Beepl_ast.pattern * Beepl_ast.expr)

and 's _menhir_cell0_dir = 
  | MenhirCell0_dir of 's * (Beepl_ast.dir)

and ('s, 'r) _menhir_cell1_effect = 
  | MenhirCell1_effect of 's * ('s, 'r) _menhir_state * (Beepl_ast.effect)

and ('s, 'r) _menhir_cell1_effect_list = 
  | MenhirCell1_effect_list of 's * ('s, 'r) _menhir_state * (Beepl_ast.effect list)

and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * (Beepl_ast.expr)

and ('s, 'r) _menhir_cell1_field_decl = 
  | MenhirCell1_field_decl of 's * ('s, 'r) _menhir_state * (string * Beepl_ast.typ)

and ('s, 'r) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__ = 
  | MenhirCell1_loption_separated_nonempty_list_COMMA_arg__ of 's * ('s, 'r) _menhir_state * ((string * Beepl_ast.typ) list)

and ('s, 'r) _menhir_cell1_loption_separated_nonempty_list_COMMA_effect__ = 
  | MenhirCell1_loption_separated_nonempty_list_COMMA_effect__ of 's * ('s, 'r) _menhir_state * (Beepl_ast.effect list)

and ('s, 'r) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__ = 
  | MenhirCell1_loption_separated_nonempty_list_COMMA_typ__ of 's * ('s, 'r) _menhir_state * (Beepl_ast.typ list)

and 's _menhir_cell0_option_BAR_ = 
  | MenhirCell0_option_BAR_ of 's * (unit option)

and ('s, 'r) _menhir_cell1_separated_nonempty_list_COMMA_IDENT_ = 
  | MenhirCell1_separated_nonempty_list_COMMA_IDENT_ of 's * ('s, 'r) _menhir_state * (string list)

and ('s, 'r) _menhir_cell1_toplevel = 
  | MenhirCell1_toplevel of 's * ('s, 'r) _menhir_state * (Beepl_ast.toplevel)

and ('s, 'r) _menhir_cell1_typ = 
  | MenhirCell1_typ of 's * ('s, 'r) _menhir_state * (Beepl_ast.typ)

and ('s, 'r) _menhir_cell1_DEREF = 
  | MenhirCell1_DEREF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_FOR = 
  | MenhirCell1_FOR of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_FUNTYPE = 
  | MenhirCell1_FUNTYPE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_HASHEBPF = 
  | MenhirCell1_HASHEBPF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_IDENT = 
  | MenhirCell1_IDENT of 's * ('s, 'r) _menhir_state * (
# 5 "bparser/beepl_parser.mly"
       (string)
# 605 "bparser/beepl_parser.ml"
)

and 's _menhir_cell0_IDENT = 
  | MenhirCell0_IDENT of 's * (
# 5 "bparser/beepl_parser.mly"
       (string)
# 612 "bparser/beepl_parser.ml"
)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LBRACE = 
  | MenhirCell1_LBRACE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LET = 
  | MenhirCell1_LET of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_MATCH = 
  | MenhirCell1_MATCH of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_MINUS = 
  | MenhirCell1_MINUS of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_ONONE = 
  | MenhirCell1_ONONE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_OSOME = 
  | MenhirCell1_OSOME of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_PBYTES = 
  | MenhirCell1_PBYTES of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_REF = 
  | MenhirCell1_REF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_SECTION = 
  | MenhirCell1_SECTION of 's * ('s, 'r) _menhir_state * (
# 38 "bparser/beepl_parser.mly"
       (string)
# 649 "bparser/beepl_parser.ml"
)

and ('s, 'r) _menhir_cell1_STRUCT = 
  | MenhirCell1_STRUCT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_TILDE = 
  | MenhirCell1_TILDE of 's * ('s, 'r) _menhir_state

and _menhir_box_prog = 
  | MenhirBox_prog of (Beepl_ast.program) [@@unboxed]

let _menhir_action_001 =
  fun rest ->
    (
# 87 "bparser/beepl_parser.mly"
                                    ( let (is_ebpf, section) = rest in (true, section) )
# 666 "bparser/beepl_parser.ml"
     : (bool * string option))

let _menhir_action_002 =
  fun rest secname ->
    (
# 88 "bparser/beepl_parser.mly"
                                             ( let (is_ebpf, _) = rest in (is_ebpf, Some secname) )
# 674 "bparser/beepl_parser.ml"
     : (bool * string option))

let _menhir_action_003 =
  fun () ->
    (
# 89 "bparser/beepl_parser.mly"
                ( (false, None) )
# 682 "bparser/beepl_parser.ml"
     : (bool * string option))

let _menhir_action_004 =
  fun anns ->
    (
# 84 "bparser/beepl_parser.mly"
                           ( anns )
# 690 "bparser/beepl_parser.ml"
     : (bool * string option))

let _menhir_action_005 =
  fun id t ->
    (
# 96 "bparser/beepl_parser.mly"
                       ( (id, t) )
# 698 "bparser/beepl_parser.ml"
     : (string * Beepl_ast.typ))

let _menhir_action_006 =
  fun xs ->
    let xs = 
# 241 "<standard.mly>"
    ( xs )
# 706 "bparser/beepl_parser.ml"
     in
    (
# 178 "bparser/beepl_parser.mly"
                                                   ( xs )
# 711 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_007 =
  fun id t ->
    (
# 181 "bparser/beepl_parser.mly"
                             ( (id, t) )
# 719 "bparser/beepl_parser.ml"
     : (string * Beepl_ast.typ))

let _menhir_action_008 =
  fun () ->
    (
# 185 "bparser/beepl_parser.mly"
                                                   ( [] )
# 727 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_009 =
  fun () ->
    (
# 187 "bparser/beepl_parser.mly"
                                                   ( [] )
# 735 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_010 =
  fun xs ->
    let xs = 
# 241 "<standard.mly>"
    ( xs )
# 743 "bparser/beepl_parser.ml"
     in
    (
# 189 "bparser/beepl_parser.mly"
                                                           ( xs )
# 748 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_011 =
  fun e id ->
    (
# 210 "bparser/beepl_parser.mly"
                                 ( (Psome id, e) )
# 756 "bparser/beepl_parser.ml"
     : (Beepl_ast.pattern * Beepl_ast.expr))

let _menhir_action_012 =
  fun e ->
    (
# 211 "bparser/beepl_parser.mly"
                                 ( (Pnone   , e) )
# 764 "bparser/beepl_parser.ml"
     : (Beepl_ast.pattern * Beepl_ast.expr))

let _menhir_action_013 =
  fun e fields id t ->
    (
# 214 "bparser/beepl_parser.mly"
    ( (Pbytes (id, t, fields), e) )
# 772 "bparser/beepl_parser.ml"
     : (Beepl_ast.pattern * Beepl_ast.expr))

let _menhir_action_014 =
  fun b ->
    (
# 171 "bparser/beepl_parser.mly"
             ( Cbool b )
# 780 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_015 =
  fun () ->
    (
# 172 "bparser/beepl_parser.mly"
             ( Cunit )
# 788 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_016 =
  fun i ->
    (
# 173 "bparser/beepl_parser.mly"
              ( Cint32 i )
# 796 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_017 =
  fun l ->
    (
# 174 "bparser/beepl_parser.mly"
              ( Clong l )
# 804 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_018 =
  fun s ->
    (
# 175 "bparser/beepl_parser.mly"
               ( Cstring s )
# 812 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_019 =
  fun () ->
    (
# 167 "bparser/beepl_parser.mly"
         ( Up )
# 820 "bparser/beepl_parser.ml"
     : (Beepl_ast.dir))

let _menhir_action_020 =
  fun () ->
    (
# 168 "bparser/beepl_parser.mly"
         ( Down )
# 828 "bparser/beepl_parser.ml"
     : (Beepl_ast.dir))

let _menhir_action_021 =
  fun () ->
    (
# 102 "bparser/beepl_parser.mly"
               ( Divergence )
# 836 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_022 =
  fun id ->
    (
# 103 "bparser/beepl_parser.mly"
                    ( Read id )
# 844 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_023 =
  fun id ->
    (
# 104 "bparser/beepl_parser.mly"
                     ( Write id )
# 852 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_024 =
  fun id ->
    (
# 105 "bparser/beepl_parser.mly"
                     ( Alloc id )
# 860 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_025 =
  fun () ->
    (
# 106 "bparser/beepl_parser.mly"
       ( Io )
# 868 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_026 =
  fun () ->
    (
# 92 "bparser/beepl_parser.mly"
                  ( [] )
# 876 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_027 =
  fun _1 ->
    (
# 93 "bparser/beepl_parser.mly"
                                           ( _1 )
# 884 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_028 =
  fun _2 ->
    (
# 217 "bparser/beepl_parser.mly"
                                ( _2 )
# 892 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_029 =
  fun id ->
    (
# 218 "bparser/beepl_parser.mly"
               ( Var id )
# 900 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_030 =
  fun c ->
    (
# 219 "bparser/beepl_parser.mly"
               ( Const c )
# 908 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_031 =
  fun e ->
    (
# 222 "bparser/beepl_parser.mly"
    ( Prim (Uop UOverloadTilde, [e]) )
# 916 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_032 =
  fun e ->
    (
# 224 "bparser/beepl_parser.mly"
    ( Prim (Uop Oneg, [e]) )
# 924 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_033 =
  fun e1 e2 ->
    (
# 227 "bparser/beepl_parser.mly"
    ( Prim (Bop Oadd, [e1; e2]) )
# 932 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_034 =
  fun e1 e2 ->
    (
# 229 "bparser/beepl_parser.mly"
    ( Prim (Bop Osub, [e1; e2]) )
# 940 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_035 =
  fun e1 e2 ->
    (
# 231 "bparser/beepl_parser.mly"
    ( Prim (Bop Omul, [e1; e2]) )
# 948 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_036 =
  fun e1 e2 ->
    (
# 233 "bparser/beepl_parser.mly"
    ( Prim (Bop Odiv, [e1; e2]) )
# 956 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_037 =
  fun e1 e2 ->
    (
# 235 "bparser/beepl_parser.mly"
    ( Prim (Bop Omod, [e1; e2]) )
# 964 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_038 =
  fun e1 e2 ->
    (
# 237 "bparser/beepl_parser.mly"
    ( Prim (Bop Oand, [e1; e2]) )
# 972 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_039 =
  fun e1 e2 ->
    (
# 239 "bparser/beepl_parser.mly"
    ( Prim (Bop Oor, [e1; e2]) )
# 980 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_040 =
  fun e1 e2 ->
    (
# 241 "bparser/beepl_parser.mly"
    ( Prim (Bop Oxor, [e1; e2]) )
# 988 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_041 =
  fun e1 e2 ->
    (
# 243 "bparser/beepl_parser.mly"
    ( Prim (Bop Oshl, [e1; e2]) )
# 996 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_042 =
  fun e1 e2 ->
    (
# 245 "bparser/beepl_parser.mly"
    ( Prim (Bop Oshr, [e1; e2]) )
# 1004 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_043 =
  fun e1 e2 ->
    (
# 247 "bparser/beepl_parser.mly"
    ( Prim (Bop Oeq, [e1; e2]) )
# 1012 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_044 =
  fun e1 e2 ->
    (
# 249 "bparser/beepl_parser.mly"
    ( Prim (Bop One, [e1; e2]) )
# 1020 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_045 =
  fun e1 e2 ->
    (
# 251 "bparser/beepl_parser.mly"
    ( Prim (Bop Olt, [e1; e2]) )
# 1028 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_046 =
  fun e1 e2 ->
    (
# 253 "bparser/beepl_parser.mly"
    ( Prim (Bop Ogt, [e1; e2]) )
# 1036 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_047 =
  fun e1 e2 ->
    (
# 255 "bparser/beepl_parser.mly"
    ( Prim (Bop Ole, [e1; e2]) )
# 1044 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_048 =
  fun e1 e2 ->
    (
# 257 "bparser/beepl_parser.mly"
    ( Prim (Bop Oge, [e1; e2]) )
# 1052 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_049 =
  fun e t ->
    (
# 259 "bparser/beepl_parser.mly"
    (Prim (Cast t, [e]) )
# 1060 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_050 =
  fun e ->
    (
# 261 "bparser/beepl_parser.mly"
    (Prim (Ref, [e]))
# 1068 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_051 =
  fun e ->
    (
# 263 "bparser/beepl_parser.mly"
    (Prim (Deref, [e]))
# 1076 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_052 =
  fun e1 e2 ->
    (
# 265 "bparser/beepl_parser.mly"
    ( Prim (Massgn, [e1; e2]) )
# 1084 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_053 =
  fun args fn ->
    (
# 268 "bparser/beepl_parser.mly"
    ( App(fn, args) )
# 1092 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_054 =
  fun fn ->
    (
# 270 "bparser/beepl_parser.mly"
    ( App(fn, []) )
# 1100 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_055 =
  fun e2 elems id t ->
    (
# 272 "bparser/beepl_parser.mly"
    ( 
      match t with
      | Atype (_, _) -> Let(id, t, Ainit(id, elems), e2)
      | _ -> failwith "Array initializer {..} can only initialize an array type"
    )
# 1112 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_056 =
  fun e1 e2 id t ->
    (
# 278 "bparser/beepl_parser.mly"
    ( Let(id, t, e1, e2) )
# 1120 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_057 =
  fun e1 e2 e3 ->
    (
# 280 "bparser/beepl_parser.mly"
    ( If(e1, e2, e3) )
# 1128 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_058 =
  fun d e1 e2 e3 ->
    (
# 282 "bparser/beepl_parser.mly"
    ( For(e1, e2, d, e3) )
# 1136 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_059 =
  fun args fields id ->
    (
# 285 "bparser/beepl_parser.mly"
    ( Sinit(id, fields, args) )
# 1144 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_060 =
  fun e id ->
    (
# 287 "bparser/beepl_parser.mly"
    ( Fget(e, id) )
# 1152 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_061 =
  fun id n ->
    (
# 289 "bparser/beepl_parser.mly"
    ( Aaccess(id, Int32.to_int n) )
# 1160 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_062 =
  fun cs e optbar ->
    (
# 291 "bparser/beepl_parser.mly"
    ( 
      let pats, bodies = List.split cs in
      Match(e, pats, bodies)
    )
# 1171 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_063 =
  fun e ->
    (
# 295 "bparser/beepl_parser.mly"
                   ( Esome e )
# 1179 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_064 =
  fun t ->
    (
# 296 "bparser/beepl_parser.mly"
                      ( Enone t)
# 1187 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_065 =
  fun id t ->
    (
# 99 "bparser/beepl_parser.mly"
                             ( (id, t) )
# 1195 "bparser/beepl_parser.ml"
     : (string * Beepl_ast.typ))

let _menhir_action_066 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1203 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_067 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1211 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_068 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1219 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_069 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1227 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_070 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1235 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_071 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1243 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_072 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1251 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_073 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1259 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_074 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1267 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_075 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1275 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_076 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1283 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ list))

let _menhir_action_077 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1291 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ list))

let _menhir_action_078 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 1299 "bparser/beepl_parser.ml"
     : (unit option))

let _menhir_action_079 =
  fun x ->
    (
# 114 "<standard.mly>"
    ( Some x )
# 1307 "bparser/beepl_parser.ml"
     : (unit option))

let _menhir_action_080 =
  fun tops ->
    (
# 58 "bparser/beepl_parser.mly"
                             ( tops )
# 1315 "bparser/beepl_parser.ml"
     : (Beepl_ast.program))

let _menhir_action_081 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1323 "bparser/beepl_parser.ml"
     : ((Beepl_ast.pattern * Beepl_ast.expr) list))

let _menhir_action_082 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1331 "bparser/beepl_parser.ml"
     : ((Beepl_ast.pattern * Beepl_ast.expr) list))

let _menhir_action_083 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1339 "bparser/beepl_parser.ml"
     : (string list))

let _menhir_action_084 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1347 "bparser/beepl_parser.ml"
     : (string list))

let _menhir_action_085 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1355 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_086 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1363 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_087 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1371 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_088 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1379 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_089 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1387 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_090 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1395 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_091 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1403 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_092 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1411 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_093 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1419 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_094 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1427 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_095 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1435 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ list))

let _menhir_action_096 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1443 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ list))

let _menhir_action_097 =
  fun anns body effs id ret xs ->
    let args = 
# 241 "<standard.mly>"
    ( xs )
# 1451 "bparser/beepl_parser.ml"
     in
    (
# 67 "bparser/beepl_parser.mly"
    (
      let f = Tfundecl(id, ret, effs, args, [], body) in
      match anns with
      | (false, sec) -> Internal (f, sec)
      | (true, sec)  -> EBPFInternal (f, sec)
    )
# 1461 "bparser/beepl_parser.ml"
     : (Beepl_ast.toplevel))

let _menhir_action_098 =
  fun id xs ->
    let fields = 
# 241 "<standard.mly>"
    ( xs )
# 1469 "bparser/beepl_parser.ml"
     in
    (
# 74 "bparser/beepl_parser.mly"
    ( StructDecl(id, fields) )
# 1474 "bparser/beepl_parser.ml"
     : (Beepl_ast.toplevel))

let _menhir_action_099 =
  fun anns e id t ->
    (
# 76 "bparser/beepl_parser.mly"
    (
      match anns with
      | (false, sec) -> GlobalLet(id, t, e, sec)
      | (true, sec)  -> failwith "Global let cannot be eBPF"
    )
# 1486 "bparser/beepl_parser.ml"
     : (Beepl_ast.toplevel))

let _menhir_action_100 =
  fun tl ->
    (
# 61 "bparser/beepl_parser.mly"
                  ( [tl] )
# 1494 "bparser/beepl_parser.ml"
     : (Beepl_ast.program))

let _menhir_action_101 =
  fun tl tlrest ->
    (
# 62 "bparser/beepl_parser.mly"
                                         ( tl :: tlrest )
# 1502 "bparser/beepl_parser.ml"
     : (Beepl_ast.program))

let _menhir_action_102 =
  fun () ->
    (
# 109 "bparser/beepl_parser.mly"
              ( Vtype Tbool )
# 1510 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_103 =
  fun () ->
    (
# 110 "bparser/beepl_parser.mly"
              ( Vtype Tuint8 )
# 1518 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_104 =
  fun () ->
    (
# 111 "bparser/beepl_parser.mly"
              ( Vtype Tint8 )
# 1526 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_105 =
  fun () ->
    (
# 112 "bparser/beepl_parser.mly"
               ( Vtype Tuint16 )
# 1534 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_106 =
  fun () ->
    (
# 113 "bparser/beepl_parser.mly"
              ( Vtype Tint16 )
# 1542 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_107 =
  fun () ->
    (
# 114 "bparser/beepl_parser.mly"
               ( Vtype Tuint32 )
# 1550 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_108 =
  fun () ->
    (
# 115 "bparser/beepl_parser.mly"
              ( Vtype Tint32 )
# 1558 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_109 =
  fun () ->
    (
# 116 "bparser/beepl_parser.mly"
              ( Vtype Tulong )
# 1566 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_110 =
  fun () ->
    (
# 117 "bparser/beepl_parser.mly"
              ( Vtype Tlong )
# 1574 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_111 =
  fun () ->
    (
# 118 "bparser/beepl_parser.mly"
                  ( Utype )
# 1582 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_112 =
  fun () ->
    (
# 119 "bparser/beepl_parser.mly"
              ( Utype )
# 1590 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_113 =
  fun () ->
    (
# 120 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ("h", (Bprim Tbool))) )
# 1598 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_114 =
  fun () ->
    (
# 121 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ("h", (Bprim Tint8))) )
# 1606 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_115 =
  fun () ->
    (
# 122 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ("h", (Bprim Tuint8))) )
# 1614 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_116 =
  fun () ->
    (
# 123 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ("h", (Bprim Tint16))) )
# 1622 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_117 =
  fun () ->
    (
# 124 "bparser/beepl_parser.mly"
                ( Ptr (Reftype ("h", (Bprim Tuint16))) )
# 1630 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_118 =
  fun () ->
    (
# 125 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ("h", (Bprim Tint32))) )
# 1638 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_119 =
  fun () ->
    (
# 126 "bparser/beepl_parser.mly"
                ( Ptr (Reftype ("h", (Bprim Tuint32))) )
# 1646 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_120 =
  fun () ->
    (
# 127 "bparser/beepl_parser.mly"
              ( Ptr (Reftype ("h", (Bprim Tlong))) )
# 1654 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_121 =
  fun () ->
    (
# 128 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ("h", (Bprim Tulong))) )
# 1662 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_122 =
  fun _2 ->
    (
# 129 "bparser/beepl_parser.mly"
                     ( Ptr (Reftype ("h", (Bstruct _2))) )
# 1670 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_123 =
  fun n ->
    (
# 130 "bparser/beepl_parser.mly"
                                   ( Ptr (Reftype ("h", (Barray (Tbool, Int32.to_int n)))) )
# 1678 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_124 =
  fun n ->
    (
# 131 "bparser/beepl_parser.mly"
                                   ( Ptr (Reftype ("h", (Barray (Tint8, Int32.to_int n)))) )
# 1686 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_125 =
  fun n ->
    (
# 132 "bparser/beepl_parser.mly"
                                    ( Ptr (Reftype ("h", (Barray (Tuint8, Int32.to_int n)))) )
# 1694 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_126 =
  fun n ->
    (
# 133 "bparser/beepl_parser.mly"
                                    ( Ptr (Reftype ("h", (Barray (Tint16, Int32.to_int n)))) )
# 1702 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_127 =
  fun n ->
    (
# 134 "bparser/beepl_parser.mly"
                                     ( Ptr (Reftype ("h", (Barray (Tuint16, Int32.to_int n)))) )
# 1710 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_128 =
  fun n ->
    (
# 135 "bparser/beepl_parser.mly"
                                    ( Ptr (Reftype ("h", (Barray (Tint32, Int32.to_int n)))) )
# 1718 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_129 =
  fun n ->
    (
# 136 "bparser/beepl_parser.mly"
                                     ( Ptr (Reftype ("h", (Barray (Tuint32, Int32.to_int n)))) )
# 1726 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_130 =
  fun n ->
    (
# 137 "bparser/beepl_parser.mly"
                                   ( Ptr (Reftype ("h", (Barray (Tlong, Int32.to_int n)))) )
# 1734 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_131 =
  fun n ->
    (
# 138 "bparser/beepl_parser.mly"
                                    ( Ptr (Reftype ("h", (Barray (Tulong, Int32.to_int n)))) )
# 1742 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_132 =
  fun () ->
    (
# 139 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ("h", (Bprim Tbool)))) )
# 1750 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_133 =
  fun () ->
    (
# 140 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ("h", (Bprim Tint8)))) )
# 1758 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_134 =
  fun () ->
    (
# 141 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ("h", (Bprim Tuint8)))) )
# 1766 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_135 =
  fun () ->
    (
# 142 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ("h", (Bprim Tint16)))) )
# 1774 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_136 =
  fun () ->
    (
# 143 "bparser/beepl_parser.mly"
                 ( Ptr (Otype (Reftype ("h", (Bprim Tuint16)))) )
# 1782 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_137 =
  fun () ->
    (
# 144 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ("h", (Bprim Tint32)))) )
# 1790 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_138 =
  fun () ->
    (
# 145 "bparser/beepl_parser.mly"
                 ( Ptr (Otype (Reftype ("h", (Bprim Tuint32)))) )
# 1798 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_139 =
  fun () ->
    (
# 146 "bparser/beepl_parser.mly"
               ( Ptr (Otype (Reftype ("h", (Bprim Tlong)))) )
# 1806 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_140 =
  fun () ->
    (
# 147 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ("h", (Bprim Tulong)))) )
# 1814 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_141 =
  fun _2 ->
    (
# 148 "bparser/beepl_parser.mly"
                       ( Ptr (Otype (Reftype ("h", (Bstruct _2)))) )
# 1822 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_142 =
  fun n ->
    (
# 149 "bparser/beepl_parser.mly"
                                    ( Ptr (Otype (Reftype ("h", (Barray (Tbool, Int32.to_int n))))) )
# 1830 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_143 =
  fun n ->
    (
# 150 "bparser/beepl_parser.mly"
                                    ( Ptr (Otype (Reftype ("h", (Barray (Tint8, Int32.to_int n))))) )
# 1838 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_144 =
  fun n ->
    (
# 151 "bparser/beepl_parser.mly"
                                     ( Ptr (Otype (Reftype ("h", (Barray (Tuint8, Int32.to_int n))))) )
# 1846 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_145 =
  fun n ->
    (
# 152 "bparser/beepl_parser.mly"
                                     ( Ptr (Otype (Reftype ("h", (Barray (Tint16, Int32.to_int n))))) )
# 1854 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_146 =
  fun n ->
    (
# 153 "bparser/beepl_parser.mly"
                                      ( Ptr (Otype (Reftype ("h", (Barray (Tuint16, Int32.to_int n))))) )
# 1862 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_147 =
  fun n ->
    (
# 154 "bparser/beepl_parser.mly"
                                     ( Ptr (Otype (Reftype ("h", (Barray (Tint32, Int32.to_int n))))) )
# 1870 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_148 =
  fun n ->
    (
# 155 "bparser/beepl_parser.mly"
                                      ( Ptr (Otype (Reftype ("h", (Barray (Tuint32, Int32.to_int n))))) )
# 1878 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_149 =
  fun n ->
    (
# 156 "bparser/beepl_parser.mly"
                                    ( Ptr (Otype (Reftype ("h", (Barray (Tlong, Int32.to_int n))))) )
# 1886 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_150 =
  fun n ->
    (
# 157 "bparser/beepl_parser.mly"
                                     ( Ptr (Otype ((Reftype ("h", (Barray (Tulong, Int32.to_int n)))))) )
# 1894 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_151 =
  fun id ->
    (
# 158 "bparser/beepl_parser.mly"
                      ( Stype id )
# 1902 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_152 =
  fun n t ->
    (
# 159 "bparser/beepl_parser.mly"
                                    ( Atype(t, Int32.to_int n) )
# 1910 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_153 =
  fun ret xs xs_inlined1 ->
    let eff =
      let xs = xs_inlined1 in
      
# 241 "<standard.mly>"
    ( xs )
# 1920 "bparser/beepl_parser.ml"
      
    in
    let args = 
# 241 "<standard.mly>"
    ( xs )
# 1926 "bparser/beepl_parser.ml"
     in
    (
# 161 "bparser/beepl_parser.mly"
                                                              ( Ftype(args, eff, ret) )
# 1931 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_154 =
  fun () ->
    (
# 162 "bparser/beepl_parser.mly"
          ( Bytes )
# 1939 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | AACEESS ->
        "AACEESS"
    | AINIT ->
        "AINIT"
    | ALLOC ->
        "ALLOC"
    | AND ->
        "AND"
    | ARRAY ->
        "ARRAY"
    | ARROW ->
        "ARROW"
    | BAR ->
        "BAR"
    | BOOL _ ->
        "BOOL"
    | BOOLTYPE ->
        "BOOLTYPE"
    | BYTES ->
        "BYTES"
    | CAST ->
        "CAST"
    | COLON ->
        "COLON"
    | COMMA ->
        "COMMA"
    | DEREF ->
        "DEREF"
    | DIV ->
        "DIV"
    | DIVERGENCE ->
        "DIVERGENCE"
    | DOT ->
        "DOT"
    | DOWN ->
        "DOWN"
    | ELSE ->
        "ELSE"
    | EMPTYBRACKETS ->
        "EMPTYBRACKETS"
    | EOF ->
        "EOF"
    | EQ ->
        "EQ"
    | FOR ->
        "FOR"
    | FUNC ->
        "FUNC"
    | FUNTYPE ->
        "FUNTYPE"
    | GE ->
        "GE"
    | GT ->
        "GT"
    | HASHEBPF ->
        "HASHEBPF"
    | IDENT _ ->
        "IDENT"
    | IF ->
        "IF"
    | IN ->
        "IN"
    | INT16TYPE ->
        "INT16TYPE"
    | INT32 _ ->
        "INT32"
    | INT32TYPE ->
        "INT32TYPE"
    | INT64 _ ->
        "INT64"
    | INT8TYPE ->
        "INT8TYPE"
    | IO ->
        "IO"
    | LBRACE ->
        "LBRACE"
    | LBRACK ->
        "LBRACK"
    | LE ->
        "LE"
    | LET ->
        "LET"
    | LONGTYPE ->
        "LONGTYPE"
    | LPAREN ->
        "LPAREN"
    | LT ->
        "LT"
    | MASSGN ->
        "MASSGN"
    | MATCH ->
        "MATCH"
    | MINUS ->
        "MINUS"
    | MOD ->
        "MOD"
    | MUL ->
        "MUL"
    | NEG ->
        "NEG"
    | NEQ ->
        "NEQ"
    | OEQ ->
        "OEQ"
    | ONONE ->
        "ONONE"
    | OR ->
        "OR"
    | ORABOOL ->
        "ORABOOL"
    | ORAINT16 ->
        "ORAINT16"
    | ORAINT32 ->
        "ORAINT32"
    | ORAINT8 ->
        "ORAINT8"
    | ORALONG ->
        "ORALONG"
    | ORARRAY ->
        "ORARRAY"
    | ORAUINT16 ->
        "ORAUINT16"
    | ORAUINT32 ->
        "ORAUINT32"
    | ORAUINT8 ->
        "ORAUINT8"
    | ORAULONG ->
        "ORAULONG"
    | ORBOOLTYPE ->
        "ORBOOLTYPE"
    | ORINT16TYPE ->
        "ORINT16TYPE"
    | ORINT32TYPE ->
        "ORINT32TYPE"
    | ORINT8TYPE ->
        "ORINT8TYPE"
    | ORLONGTYPE ->
        "ORLONGTYPE"
    | ORSTRUCT ->
        "ORSTRUCT"
    | ORUINT16TYPE ->
        "ORUINT16TYPE"
    | ORUINT32TYPE ->
        "ORUINT32TYPE"
    | ORUINT8TYPE ->
        "ORUINT8TYPE"
    | ORULONGTYPE ->
        "ORULONGTYPE"
    | OSOME ->
        "OSOME"
    | PBYTES ->
        "PBYTES"
    | PLUS ->
        "PLUS"
    | RABOOL ->
        "RABOOL"
    | RAINT16 ->
        "RAINT16"
    | RAINT32 ->
        "RAINT32"
    | RAINT8 ->
        "RAINT8"
    | RALONG ->
        "RALONG"
    | RARRAY ->
        "RARRAY"
    | RAUINT16 ->
        "RAUINT16"
    | RAUINT32 ->
        "RAUINT32"
    | RAUINT8 ->
        "RAUINT8"
    | RAULONG ->
        "RAULONG"
    | RBOOLTYPE ->
        "RBOOLTYPE"
    | RBRACE ->
        "RBRACE"
    | RBRACK ->
        "RBRACK"
    | READ ->
        "READ"
    | REF ->
        "REF"
    | RINT16TYPE ->
        "RINT16TYPE"
    | RINT32TYPE ->
        "RINT32TYPE"
    | RINT8TYPE ->
        "RINT8TYPE"
    | RLONGTYPE ->
        "RLONGTYPE"
    | RPAREN ->
        "RPAREN"
    | RSTRUCT ->
        "RSTRUCT"
    | RUINT16TYPE ->
        "RUINT16TYPE"
    | RUINT32TYPE ->
        "RUINT32TYPE"
    | RUINT8TYPE ->
        "RUINT8TYPE"
    | RULONGTYPE ->
        "RULONGTYPE"
    | SECTION _ ->
        "SECTION"
    | SHL ->
        "SHL"
    | SHR ->
        "SHR"
    | SINIT ->
        "SINIT"
    | STAR ->
        "STAR"
    | STRING _ ->
        "STRING"
    | STRUCT ->
        "STRUCT"
    | THEN ->
        "THEN"
    | TILDE ->
        "TILDE"
    | TSTRUCT ->
        "TSTRUCT"
    | UINT16TYPE ->
        "UINT16TYPE"
    | UINT32TYPE ->
        "UINT32TYPE"
    | UINT8TYPE ->
        "UINT8TYPE"
    | ULONGTYPE ->
        "ULONGTYPE"
    | UNIT ->
        "UNIT"
    | UP ->
        "UP"
    | WITH ->
        "WITH"
    | WRITE ->
        "WRITE"
    | XOR ->
        "XOR"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_153 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_prog =
    fun _menhir_stack _v ->
      let tops = _v in
      let _v = _menhir_action_080 tops in
      MenhirBox_prog _v
  
  let rec _menhir_goto_toplevel_list : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState155 ->
          _menhir_run_156 _menhir_stack _v
      | MenhirState000 ->
          _menhir_run_153 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_156 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_toplevel -> _ -> _menhir_box_prog =
    fun _menhir_stack _v ->
      let MenhirCell1_toplevel (_menhir_stack, _menhir_s, tl) = _menhir_stack in
      let tlrest = _v in
      let _v = _menhir_action_101 tl tlrest in
      _menhir_goto_toplevel_list _menhir_stack _v _menhir_s
  
  let rec _menhir_run_001 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_STRUCT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LBRACE ->
              let _menhir_s = MenhirState003 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v ->
                  _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | RBRACE ->
                  let _v = _menhir_action_074 () in
                  _menhir_goto_loption_separated_nonempty_list_COMMA_field_decl__ _menhir_stack _menhir_lexbuf _menhir_lexer _v
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_004 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState005 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULONGTYPE ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT8TYPE ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT32TYPE ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT16TYPE ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RULONGTYPE ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT8TYPE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT32TYPE ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT16TYPE ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RLONGTYPE ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT8TYPE ->
              _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT32TYPE ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT16TYPE ->
              _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RBOOLTYPE ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAULONG ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT8 ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT32 ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT16 ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RALONG ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT8 ->
              _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT32 ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT16 ->
              _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RABOOL ->
              _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORSTRUCT ->
              _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORLONGTYPE ->
              _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT8TYPE ->
              _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT32TYPE ->
              _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT16TYPE ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORBOOLTYPE ->
              _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAULONG ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT8 ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT32 ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT16 ->
              _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORALONG ->
              _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT8 ->
              _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT32 ->
              _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT16 ->
              _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORABOOL ->
              _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LONGTYPE ->
              _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT8TYPE ->
              _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT32TYPE ->
              _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT16TYPE ->
              _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FUNTYPE ->
              _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BYTES ->
              _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOLTYPE ->
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_006 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_112 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_typ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState326 ->
          _menhir_run_327 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState336 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState320 ->
          _menhir_run_321 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState288 ->
          _menhir_run_289 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState283 ->
          _menhir_run_284 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState181 ->
          _menhir_run_272 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState185 ->
          _menhir_run_272 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState188 ->
          _menhir_run_189 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState160 ->
          _menhir_run_161 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState005 ->
          _menhir_run_142 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState137 ->
          _menhir_run_138 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState121 ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState114 ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_327 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WRITE ->
              _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState328
          | READ ->
              _menhir_run_129 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState328
          | IO ->
              _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState328
          | EMPTYBRACKETS ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _menhir_s = MenhirState328 in
              let _v = _menhir_action_026 () in
              _menhir_goto_effect_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | DIVERGENCE ->
              _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState328
          | ALLOC ->
              _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState328
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_118 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | INT32 _v ->
          _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_119 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | RBRACK ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_typ (_menhir_stack, _menhir_s, t) = _menhir_stack in
          let n = _v in
          let _v = _menhir_action_152 n t in
          _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_127 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let id = _v in
          let _v = _menhir_action_023 id in
          _menhir_goto_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_effect : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_effect (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState140 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WRITE ->
              _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | READ ->
              _menhir_run_129 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IO ->
              _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DIVERGENCE ->
              _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ALLOC ->
              _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | LBRACE ->
          let x = _v in
          let _v = _menhir_action_089 x in
          _menhir_goto_separated_nonempty_list_COMMA_effect_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_129 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let id = _v in
          let _v = _menhir_action_022 id in
          _menhir_goto_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_131 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_025 () in
      _menhir_goto_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_132 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_021 () in
      _menhir_goto_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_133 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let id = _v in
          let _v = _menhir_action_024 id in
          _menhir_goto_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_effect_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState328 ->
          _menhir_run_330 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState140 ->
          _menhir_run_141 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState126 ->
          _menhir_run_135 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_330 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_027 _1 in
      _menhir_goto_effect_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_effect_list : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_effect_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _menhir_s = MenhirState332 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_163 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_015 () in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_const : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let c = _v in
      let _v = _menhir_action_030 c in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState332 ->
          _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState162 ->
          _menhir_run_317 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState164 ->
          _menhir_run_316 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState175 ->
          _menhir_run_313 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState176 ->
          _menhir_run_312 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState179 ->
          _menhir_run_311 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState305 ->
          _menhir_run_306 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState302 ->
          _menhir_run_303 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState298 ->
          _menhir_run_299 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState180 ->
          _menhir_run_277 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState181 ->
          _menhir_run_275 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState185 ->
          _menhir_run_275 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState273 ->
          _menhir_run_274 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState270 ->
          _menhir_run_271 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState267 ->
          _menhir_run_268 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState190 ->
          _menhir_run_266 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState261 ->
          _menhir_run_262 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState259 ->
          _menhir_run_260 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState194 ->
          _menhir_run_258 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState255 ->
          _menhir_run_256 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState249 ->
          _menhir_run_250 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState200 ->
          _menhir_run_248 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState244 ->
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState242 ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState240 ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState238 ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState236 ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState234 ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState232 ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState230 ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState228 ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState226 ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState224 ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState222 ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState220 ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState215 ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState213 ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState211 ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState209 ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState173 ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState191 ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState246 ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState204 ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState201 ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_333 : type  ttv_stack. (((((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_effect_list as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_effect_list (_menhir_stack, _, effs) = _menhir_stack in
          let MenhirCell1_typ (_menhir_stack, _, ret) = _menhir_stack in
          let MenhirCell1_loption_separated_nonempty_list_COMMA_arg__ (_menhir_stack, _, xs) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_annotations (_menhir_stack, _menhir_s, anns) = _menhir_stack in
          let body = _v in
          let _v = _menhir_action_097 anns body effs id ret xs in
          _menhir_goto_toplevel _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_209 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState209 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_164 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_TILDE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState164 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_165 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_STRUCT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              _menhir_run_167 _menhir_stack _menhir_lexbuf _menhir_lexer
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_167 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState167 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          _menhir_run_168 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_168 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState169 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              _menhir_run_168 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_083 x in
          _menhir_goto_separated_nonempty_list_COMMA_IDENT_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_IDENT_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState167 ->
          _menhir_run_171 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState169 ->
          _menhir_run_170 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_171 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_separated_nonempty_list_COMMA_IDENT_ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState173 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_174 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let s = _v in
      let _v = _menhir_action_018 s in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_175 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_REF (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState175 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_176 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_OSOME (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState176 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_177 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ONONE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState177 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ULONGTYPE ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT8TYPE ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT32TYPE ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT16TYPE ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RULONGTYPE ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT8TYPE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT32TYPE ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT16TYPE ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RLONGTYPE ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT8TYPE ->
          _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT32TYPE ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT16TYPE ->
          _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RBOOLTYPE ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAULONG ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT8 ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT32 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT16 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RALONG ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT8 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT32 ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT16 ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RABOOL ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORULONGTYPE ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT8TYPE ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT32TYPE ->
          _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT16TYPE ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORSTRUCT ->
          _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORLONGTYPE ->
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT8TYPE ->
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT32TYPE ->
          _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT16TYPE ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORBOOLTYPE ->
          _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAULONG ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT8 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT32 ->
          _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT16 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORALONG ->
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT8 ->
          _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT32 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT16 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORABOOL ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LONGTYPE ->
          _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT8TYPE ->
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT32TYPE ->
          _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT16TYPE ->
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FUNTYPE ->
          _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BYTES ->
          _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOLTYPE ->
          _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_007 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_109 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_008 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_103 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_009 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_107 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_010 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_105 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_011 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | MUL ->
              let _menhir_stack = MenhirCell1_STRUCT (_menhir_stack, _menhir_s) in
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer
          | AND | BAR | COMMA | DIV | DOT | ELSE | EMPTYBRACKETS | EOF | EQ | FUNC | GE | GT | HASHEBPF | IDENT _ | IN | LBRACK | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | NEQ | OEQ | OR | PLUS | RBRACE | RBRACK | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
              let id = _v in
              let _v = _menhir_action_151 id in
              _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_013 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_IDENT (_menhir_stack, _2) = _menhir_stack in
      let MenhirCell1_STRUCT (_menhir_stack, _menhir_s) = _menhir_stack in
      let _v = _menhir_action_122 _2 in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_014 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_121 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_015 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_115 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_016 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_119 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_017 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_117 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_018 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_120 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_019 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_114 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_020 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_118 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_021 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_116 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_022 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_113 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_023 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_131 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_027 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_125 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_031 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_129 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_035 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_127 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_039 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_130 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_043 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_124 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_047 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_128 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_051 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_126 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_055 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_123 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_059 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_140 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_060 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_134 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_061 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_138 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_062 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_136 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_063 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | MUL ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _2 = _v in
              let _v = _menhir_action_141 _2 in
              _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_066 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_139 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_067 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_133 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_068 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_137 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_069 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_135 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_070 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_132 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_071 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_150 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_075 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_144 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_079 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_148 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_083 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_146 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_087 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_149 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_091 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_143 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_095 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_147 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_099 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_145 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_103 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_142 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_107 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_108 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
      let _v = _menhir_action_111 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_109 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_110 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_110 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_104 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_111 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_108 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_112 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_106 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_113 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_FUNTYPE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState114 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULONGTYPE ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT8TYPE ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT32TYPE ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT16TYPE ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RULONGTYPE ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT8TYPE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT32TYPE ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT16TYPE ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RLONGTYPE ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT8TYPE ->
              _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT32TYPE ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT16TYPE ->
              _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RBOOLTYPE ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAULONG ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT8 ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT32 ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT16 ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RALONG ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT8 ->
              _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT32 ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT16 ->
              _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RABOOL ->
              _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORSTRUCT ->
              _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORLONGTYPE ->
              _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT8TYPE ->
              _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT32TYPE ->
              _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT16TYPE ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORBOOLTYPE ->
              _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAULONG ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT8 ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT32 ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT16 ->
              _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORALONG ->
              _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT8 ->
              _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT32 ->
              _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT16 ->
              _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORABOOL ->
              _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LONGTYPE ->
              _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT8TYPE ->
              _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT32TYPE ->
              _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT16TYPE ->
              _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FUNTYPE ->
              _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BYTES ->
              _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOLTYPE ->
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RPAREN ->
              let _v = _menhir_action_076 () in
              _menhir_goto_loption_separated_nonempty_list_COMMA_typ__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_115 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_154 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_116 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_102 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_typ__ : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_loption_separated_nonempty_list_COMMA_typ__ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState126 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WRITE ->
              _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | READ ->
              _menhir_run_129 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IO ->
              _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DIVERGENCE ->
              _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ALLOC ->
              _menhir_run_133 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | COMMA ->
              let _v = _menhir_action_070 () in
              _menhir_goto_loption_separated_nonempty_list_COMMA_effect__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_effect__ : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_loption_separated_nonempty_list_COMMA_effect__ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_s = MenhirState137 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULONGTYPE ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT8TYPE ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT32TYPE ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT16TYPE ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RULONGTYPE ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT8TYPE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT32TYPE ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT16TYPE ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RLONGTYPE ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT8TYPE ->
              _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT32TYPE ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT16TYPE ->
              _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RBOOLTYPE ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAULONG ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT8 ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT32 ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT16 ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RALONG ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT8 ->
              _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT32 ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT16 ->
              _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RABOOL ->
              _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORSTRUCT ->
              _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORLONGTYPE ->
              _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT8TYPE ->
              _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT32TYPE ->
              _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT16TYPE ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORBOOLTYPE ->
              _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAULONG ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT8 ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT32 ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT16 ->
              _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORALONG ->
              _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT8 ->
              _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT32 ->
              _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT16 ->
              _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORABOOL ->
              _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LONGTYPE ->
              _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT8TYPE ->
              _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT32TYPE ->
              _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT16TYPE ->
              _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FUNTYPE ->
              _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BYTES ->
              _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOLTYPE ->
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_179 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MINUS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState179 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_180 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MATCH (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState180 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_181 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState181 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ULONGTYPE ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT8TYPE ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT32TYPE ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT16TYPE ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_183 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | RULONGTYPE ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT8TYPE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT32TYPE ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT16TYPE ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RLONGTYPE ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT8TYPE ->
          _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT32TYPE ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT16TYPE ->
          _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RBOOLTYPE ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAULONG ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT8 ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT32 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT16 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RALONG ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT8 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT32 ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT16 ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RABOOL ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORULONGTYPE ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT8TYPE ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT32TYPE ->
          _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT16TYPE ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORSTRUCT ->
          _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORLONGTYPE ->
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT8TYPE ->
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT32TYPE ->
          _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT16TYPE ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORBOOLTYPE ->
          _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAULONG ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT8 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT32 ->
          _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT16 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORALONG ->
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT8 ->
          _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT32 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT16 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORABOOL ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LONGTYPE ->
          _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT8TYPE ->
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32TYPE ->
          _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT16TYPE ->
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FUNTYPE ->
          _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BYTES ->
          _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOLTYPE ->
          _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_182 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | AND | DIV | DOT | GE | GT | LE | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | SHL | SHR | XOR ->
          let _v = _menhir_action_015 () in
          _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | LBRACK | RPAREN ->
          let _v = _menhir_action_112 () in
          _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_183 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | MUL ->
              let _menhir_stack = MenhirCell1_STRUCT (_menhir_stack, _menhir_s) in
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer
          | LPAREN ->
              let _menhir_stack = MenhirCell1_STRUCT (_menhir_stack, _menhir_s) in
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              _menhir_run_167 _menhir_stack _menhir_lexbuf _menhir_lexer
          | LBRACK | RPAREN ->
              let id = _v in
              let _v = _menhir_action_151 id in
              _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_185 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState185 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ULONGTYPE ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT8TYPE ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT32TYPE ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT16TYPE ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_183 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | RULONGTYPE ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT8TYPE ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT32TYPE ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT16TYPE ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RPAREN ->
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RLONGTYPE ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT8TYPE ->
          _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT32TYPE ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT16TYPE ->
          _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RBOOLTYPE ->
          _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAULONG ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT8 ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT32 ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT16 ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RALONG ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT8 ->
          _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT32 ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT16 ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RABOOL ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORULONGTYPE ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT8TYPE ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT32TYPE ->
          _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT16TYPE ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORSTRUCT ->
          _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORLONGTYPE ->
          _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT8TYPE ->
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT32TYPE ->
          _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT16TYPE ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORBOOLTYPE ->
          _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAULONG ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT8 ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT32 ->
          _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT16 ->
          _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORALONG ->
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT8 ->
          _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT32 ->
          _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT16 ->
          _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORABOOL ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LONGTYPE ->
          _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT8TYPE ->
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32TYPE ->
          _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT16TYPE ->
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FUNTYPE ->
          _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BYTES ->
          _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOLTYPE ->
          _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_186 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LET (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | COLON ->
              let _menhir_s = MenhirState188 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ULONGTYPE ->
                  _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT8TYPE ->
                  _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT32TYPE ->
                  _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT16TYPE ->
                  _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RULONGTYPE ->
                  _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT8TYPE ->
                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT32TYPE ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT16TYPE ->
                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RLONGTYPE ->
                  _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT8TYPE ->
                  _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT32TYPE ->
                  _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT16TYPE ->
                  _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RBOOLTYPE ->
                  _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAULONG ->
                  _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT8 ->
                  _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT32 ->
                  _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT16 ->
                  _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RALONG ->
                  _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT8 ->
                  _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT32 ->
                  _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT16 ->
                  _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RABOOL ->
                  _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORULONGTYPE ->
                  _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT8TYPE ->
                  _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT32TYPE ->
                  _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT16TYPE ->
                  _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORSTRUCT ->
                  _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORLONGTYPE ->
                  _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT8TYPE ->
                  _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT32TYPE ->
                  _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT16TYPE ->
                  _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORBOOLTYPE ->
                  _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAULONG ->
                  _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT8 ->
                  _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT32 ->
                  _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT16 ->
                  _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORALONG ->
                  _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT8 ->
                  _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT32 ->
                  _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT16 ->
                  _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORABOOL ->
                  _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LONGTYPE ->
                  _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT8TYPE ->
                  _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT32TYPE ->
                  _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT16TYPE ->
                  _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | FUNTYPE ->
                  _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BYTES ->
                  _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOLTYPE ->
                  _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_192 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let l = _v in
      let _v = _menhir_action_017 l in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_193 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let i = _v in
      let _v = _menhir_action_016 i in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_194 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState194 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_195 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v_0 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACK ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let (id, n) = (_v, _v_0) in
                  let _v = _menhir_action_061 id n in
                  _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | AND | BAR | COMMA | DIV | DOT | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let id = _v in
          let _v = _menhir_action_029 id in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_199 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_FOR (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState200 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_201 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DEREF (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState201 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_202 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let b = _v in
      let _v = _menhir_action_014 b in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_170 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_IDENT -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_IDENT (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_084 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_IDENT_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_211 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState211 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_226 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState226 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_toplevel : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STRUCT ->
          let _menhir_stack = MenhirCell1_toplevel (_menhir_stack, _menhir_s, _v) in
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState155
      | SECTION _v_0 ->
          let _menhir_stack = MenhirCell1_toplevel (_menhir_stack, _menhir_s, _v) in
          _menhir_run_149 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState155
      | HASHEBPF ->
          let _menhir_stack = MenhirCell1_toplevel (_menhir_stack, _menhir_s, _v) in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState155
      | FUNC | LET ->
          let _menhir_stack = MenhirCell1_toplevel (_menhir_stack, _menhir_s, _v) in
          let _v_1 = _menhir_action_003 () in
          _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState155 _tok
      | EOF ->
          let tl = _v in
          let _v = _menhir_action_100 tl in
          _menhir_goto_toplevel_list _menhir_stack _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_149 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_SECTION (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SECTION _v_0 ->
          _menhir_run_149 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState149
      | HASHEBPF ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState149
      | FUNC | LET ->
          let _v_1 = _menhir_action_003 () in
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_150 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_HASHEBPF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SECTION _v ->
          _menhir_run_149 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState150
      | HASHEBPF ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState150
      | FUNC | LET ->
          let _v = _menhir_action_003 () in
          _menhir_run_151 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_151 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_HASHEBPF -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_HASHEBPF (_menhir_stack, _menhir_s) = _menhir_stack in
      let rest = _v in
      let _v = _menhir_action_001 rest in
      _menhir_goto_annotation_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_annotation_list : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState000 ->
          _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState155 ->
          _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState149 ->
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState150 ->
          _menhir_run_151 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_338 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let anns = _v in
      let _v = _menhir_action_004 anns in
      let _menhir_stack = MenhirCell1_annotations (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | COLON ->
                  let _menhir_s = MenhirState160 in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | UNIT ->
                      _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ULONGTYPE ->
                      _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | UINT8TYPE ->
                      _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | UINT32TYPE ->
                      _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | UINT16TYPE ->
                      _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | STRUCT ->
                      _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RULONGTYPE ->
                      _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RUINT8TYPE ->
                      _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RUINT32TYPE ->
                      _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RUINT16TYPE ->
                      _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RLONGTYPE ->
                      _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RINT8TYPE ->
                      _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RINT32TYPE ->
                      _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RINT16TYPE ->
                      _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RBOOLTYPE ->
                      _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAULONG ->
                      _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAUINT8 ->
                      _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAUINT32 ->
                      _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAUINT16 ->
                      _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RALONG ->
                      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAINT8 ->
                      _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAINT32 ->
                      _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAINT16 ->
                      _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RABOOL ->
                      _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORULONGTYPE ->
                      _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT8TYPE ->
                      _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT32TYPE ->
                      _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT16TYPE ->
                      _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORSTRUCT ->
                      _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORLONGTYPE ->
                      _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORINT8TYPE ->
                      _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORINT32TYPE ->
                      _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORINT16TYPE ->
                      _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORBOOLTYPE ->
                      _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAULONG ->
                      _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAUINT8 ->
                      _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAUINT32 ->
                      _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAUINT16 ->
                      _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORALONG ->
                      _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAINT8 ->
                      _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAINT32 ->
                      _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAINT16 ->
                      _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORABOOL ->
                      _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | LPAREN ->
                      _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | LONGTYPE ->
                      _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT8TYPE ->
                      _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT32TYPE ->
                      _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT16TYPE ->
                      _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | FUNTYPE ->
                      _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | BYTES ->
                      _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | BOOLTYPE ->
                      _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | FUNC ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | LPAREN ->
                  let _menhir_s = MenhirState320 in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | UNIT ->
                      _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ULONGTYPE ->
                      _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | UINT8TYPE ->
                      _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | UINT32TYPE ->
                      _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | UINT16TYPE ->
                      _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | STRUCT ->
                      _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RULONGTYPE ->
                      _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RUINT8TYPE ->
                      _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RUINT32TYPE ->
                      _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RUINT16TYPE ->
                      _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RLONGTYPE ->
                      _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RINT8TYPE ->
                      _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RINT32TYPE ->
                      _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RINT16TYPE ->
                      _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RBOOLTYPE ->
                      _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAULONG ->
                      _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAUINT8 ->
                      _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAUINT32 ->
                      _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAUINT16 ->
                      _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RALONG ->
                      _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAINT8 ->
                      _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAINT32 ->
                      _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAINT16 ->
                      _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RABOOL ->
                      _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORULONGTYPE ->
                      _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT8TYPE ->
                      _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT32TYPE ->
                      _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT16TYPE ->
                      _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORSTRUCT ->
                      _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORLONGTYPE ->
                      _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORINT8TYPE ->
                      _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORINT32TYPE ->
                      _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORINT16TYPE ->
                      _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORBOOLTYPE ->
                      _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAULONG ->
                      _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAUINT8 ->
                      _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAUINT32 ->
                      _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAUINT16 ->
                      _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORALONG ->
                      _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAINT8 ->
                      _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAINT32 ->
                      _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAINT16 ->
                      _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORABOOL ->
                      _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | LPAREN ->
                      _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | LONGTYPE ->
                      _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT8TYPE ->
                      _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT32TYPE ->
                      _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT16TYPE ->
                      _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | FUNTYPE ->
                      _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | BYTES ->
                      _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | BOOLTYPE ->
                      _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RPAREN ->
                      let _v = _menhir_action_066 () in
                      _menhir_goto_loption_separated_nonempty_list_COMMA_arg__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_arg__ : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_loption_separated_nonempty_list_COMMA_arg__ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState326 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULONGTYPE ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT8TYPE ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT32TYPE ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT16TYPE ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RULONGTYPE ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT8TYPE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT32TYPE ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT16TYPE ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RLONGTYPE ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT8TYPE ->
              _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT32TYPE ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT16TYPE ->
              _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RBOOLTYPE ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAULONG ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT8 ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT32 ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT16 ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RALONG ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT8 ->
              _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT32 ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT16 ->
              _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RABOOL ->
              _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORSTRUCT ->
              _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORLONGTYPE ->
              _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT8TYPE ->
              _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT32TYPE ->
              _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT16TYPE ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORBOOLTYPE ->
              _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAULONG ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT8 ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT32 ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT16 ->
              _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORALONG ->
              _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT8 ->
              _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT32 ->
              _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT16 ->
              _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORABOOL ->
              _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LONGTYPE ->
              _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT8TYPE ->
              _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT32TYPE ->
              _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT16TYPE ->
              _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FUNTYPE ->
              _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BYTES ->
              _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOLTYPE ->
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_152 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_SECTION -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_SECTION (_menhir_stack, _menhir_s, secname) = _menhir_stack in
      let rest = _v in
      let _v = _menhir_action_002 rest secname in
      _menhir_goto_annotation_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_213 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState213 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_242 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState242 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_228 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState228 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_238 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState238 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_215 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState215 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_220 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState220 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_224 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState224 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_244 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState244 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_230 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState230 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_204 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState204
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, fn) = _menhir_stack in
          let _v = _menhir_action_054 fn in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState204
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState204
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState204
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState204
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState204
      | _ ->
          _eRR ()
  
  and _menhir_run_232 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState232 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_234 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState234 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_236 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState236 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_217 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e) = _menhir_stack in
          let id = _v in
          let _v = _menhir_action_060 e id in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_222 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState222 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_240 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState240 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_317 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EOF | FUNC | HASHEBPF | LET | SECTION _ | STRUCT ->
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_annotations (_menhir_stack, _menhir_s, anns) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_099 anns e id t in
          _menhir_goto_toplevel _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_316 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_TILDE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_TILDE (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_031 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_313 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_REF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_REF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_050 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_312 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_OSOME as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_OSOME (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_063 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_311 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MINUS as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_MINUS (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_032 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_306 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_ONONE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_ONONE (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_012 e in
          _menhir_goto_clause _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_clause : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | BAR ->
          let _menhir_stack = MenhirCell1_clause (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState309 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PBYTES ->
              _menhir_run_281 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_300 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | AND | COMMA | DIV | DOT | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let x = _v in
          let _v = _menhir_action_081 x in
          _menhir_goto_separated_nonempty_list_BAR_clause_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_281 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PBYTES (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | COLON ->
              let _menhir_s = MenhirState283 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ULONGTYPE ->
                  _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT8TYPE ->
                  _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT32TYPE ->
                  _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT16TYPE ->
                  _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RULONGTYPE ->
                  _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT8TYPE ->
                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT32TYPE ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT16TYPE ->
                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RLONGTYPE ->
                  _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT8TYPE ->
                  _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT32TYPE ->
                  _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT16TYPE ->
                  _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RBOOLTYPE ->
                  _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAULONG ->
                  _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT8 ->
                  _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT32 ->
                  _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT16 ->
                  _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RALONG ->
                  _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT8 ->
                  _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT32 ->
                  _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT16 ->
                  _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RABOOL ->
                  _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORULONGTYPE ->
                  _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT8TYPE ->
                  _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT32TYPE ->
                  _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT16TYPE ->
                  _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORSTRUCT ->
                  _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORLONGTYPE ->
                  _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT8TYPE ->
                  _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT32TYPE ->
                  _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT16TYPE ->
                  _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORBOOLTYPE ->
                  _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAULONG ->
                  _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT8 ->
                  _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT32 ->
                  _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT16 ->
                  _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORALONG ->
                  _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT8 ->
                  _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT32 ->
                  _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT16 ->
                  _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORABOOL ->
                  _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LONGTYPE ->
                  _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT8TYPE ->
                  _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT32TYPE ->
                  _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT16TYPE ->
                  _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | FUNTYPE ->
                  _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BYTES ->
                  _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOLTYPE ->
                  _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_300 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_OSOME (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ARROW ->
              let _menhir_s = MenhirState302 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | TILDE ->
                  _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRING _v ->
                  _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | REF ->
                  _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | OSOME ->
                  _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ONONE ->
                  _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MATCH ->
                  _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LET ->
                  _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT64 _v ->
                  _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | INT32 _v ->
                  _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | IF ->
                  _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | IDENT _v ->
                  _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | FOR ->
                  _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | DEREF ->
                  _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOL _v ->
                  _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_304 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ONONE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ARROW ->
          let _menhir_s = MenhirState305 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_BAR_clause_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState309 ->
          _menhir_run_310 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState280 ->
          _menhir_run_307 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_310 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_clause -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_clause (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_082 x xs in
      _menhir_goto_separated_nonempty_list_BAR_clause_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_307 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MATCH, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_option_BAR_ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_option_BAR_ (_menhir_stack, optbar) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, e) = _menhir_stack in
      let MenhirCell1_MATCH (_menhir_stack, _menhir_s) = _menhir_stack in
      let cs = _v in
      let _v = _menhir_action_062 cs e optbar in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_303 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_OSOME _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_OSOME (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_011 e id in
          _menhir_goto_clause _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_299 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ _menhir_cell0_bytes_fields as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell0_bytes_fields (_menhir_stack, fields) = _menhir_stack in
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_PBYTES (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_013 e fields id t in
          _menhir_goto_clause _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_277 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MATCH as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | WITH ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | BAR ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let x = () in
              let _v = _menhir_action_079 x in
              _menhir_goto_option_BAR_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | ONONE | OSOME | PBYTES ->
              let _v = _menhir_action_078 () in
              _menhir_goto_option_BAR_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | SHR ->
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_option_BAR_ : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MATCH, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_option_BAR_ (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | PBYTES ->
          _menhir_run_281 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState280
      | OSOME ->
          _menhir_run_300 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState280
      | ONONE ->
          _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState280
      | _ ->
          _eRR ()
  
  and _menhir_run_275 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_028 _2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_274 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_049 e t in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_271 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_array_elems as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_array_elems (_menhir_stack, _, elems) = _menhir_stack in
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_055 e2 elems id t in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_268 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_056 e1 e2 id t in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_266 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IN ->
          let _menhir_s = MenhirState267 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | GT ->
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_262 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_expr (_menhir_stack, _, e2) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e3 = _v in
          let _v = _menhir_action_057 e1 e2 e3 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_260 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE ->
          let _menhir_s = MenhirState261 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | DOT ->
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_258 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | THEN ->
          let _menhir_s = MenhirState259 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | SHR ->
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_256 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_dir as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_dir (_menhir_stack, d) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, e2) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_FOR (_menhir_stack, _menhir_s) = _menhir_stack in
          let e3 = _v in
          let _v = _menhir_action_058 d e1 e2 e3 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_250 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UP ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_019 () in
              _menhir_goto_dir _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | DOWN ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_020 () in
              _menhir_goto_dir _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | AND ->
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_dir : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_dir (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_s = MenhirState255 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_248 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_FOR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_s = MenhirState249 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | AND ->
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_245 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_052 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_243 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_039 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_241 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_038 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_239 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_044 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_237 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_048 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_235 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_046 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_233 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_047 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_231 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_045 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_229 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_043 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_227 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_041 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_225 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_034 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_223 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_036 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_221 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_037 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_216 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_035 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_214 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_033 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_212 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_042 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_210 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_040 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_208 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState246 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RBRACE | RPAREN ->
          let x = _v in
          let _v = _menhir_action_091 x in
          _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_expr_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState173 ->
          _menhir_run_314 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState191 ->
          _menhir_run_263 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState246 ->
          _menhir_run_247 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState204 ->
          _menhir_run_206 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_314 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_separated_nonempty_list_COMMA_IDENT_ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_separated_nonempty_list_COMMA_IDENT_ (_menhir_stack, _, fields) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_STRUCT (_menhir_stack, _menhir_s) = _menhir_stack in
          let args = _v in
          let _v = _menhir_action_059 args fields id in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_263 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_LBRACE -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let x = _v in
      let _v = _menhir_action_073 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_LBRACE -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LBRACE (_menhir_stack, _menhir_s) = _menhir_stack in
          let xs = _v in
          let _v = _menhir_action_006 xs in
          let _menhir_stack = MenhirCell1_array_elems (_menhir_stack, _menhir_s, _v) in
          (match (_tok : MenhirBasics.token) with
          | IN ->
              let _menhir_s = MenhirState270 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | TILDE ->
                  _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRING _v ->
                  _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | REF ->
                  _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | OSOME ->
                  _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ONONE ->
                  _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MATCH ->
                  _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LET ->
                  _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT64 _v ->
                  _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | INT32 _v ->
                  _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | IF ->
                  _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | IDENT _v ->
                  _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | FOR ->
                  _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | DEREF ->
                  _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOL _v ->
                  _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_247 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_092 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_206 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, fn) = _menhir_stack in
          let args = _v in
          let _v = _menhir_action_053 args fn in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_203 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_DEREF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_DEREF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_051 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_141 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_effect -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_effect (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_090 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_effect_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_135 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let x = _v in
      let _v = _menhir_action_071 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_effect__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_321 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IDENT _v_0 ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (id, t) = (_v_0, _v) in
          let _v = _menhir_action_005 id t in
          (match (_tok : MenhirBasics.token) with
          | COMMA ->
              let _menhir_stack = MenhirCell1_arg (_menhir_stack, _menhir_s, _v) in
              let _menhir_s = MenhirState336 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ULONGTYPE ->
                  _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT8TYPE ->
                  _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT32TYPE ->
                  _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT16TYPE ->
                  _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RULONGTYPE ->
                  _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT8TYPE ->
                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT32TYPE ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT16TYPE ->
                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RLONGTYPE ->
                  _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT8TYPE ->
                  _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT32TYPE ->
                  _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT16TYPE ->
                  _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RBOOLTYPE ->
                  _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAULONG ->
                  _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT8 ->
                  _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT32 ->
                  _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT16 ->
                  _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RALONG ->
                  _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT8 ->
                  _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT32 ->
                  _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT16 ->
                  _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RABOOL ->
                  _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORULONGTYPE ->
                  _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT8TYPE ->
                  _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT32TYPE ->
                  _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT16TYPE ->
                  _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORSTRUCT ->
                  _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORLONGTYPE ->
                  _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT8TYPE ->
                  _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT32TYPE ->
                  _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT16TYPE ->
                  _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORBOOLTYPE ->
                  _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAULONG ->
                  _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT8 ->
                  _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT32 ->
                  _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT16 ->
                  _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORALONG ->
                  _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT8 ->
                  _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT32 ->
                  _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT16 ->
                  _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORABOOL ->
                  _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LONGTYPE ->
                  _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT8TYPE ->
                  _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT32TYPE ->
                  _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT16TYPE ->
                  _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | FUNTYPE ->
                  _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BYTES ->
                  _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOLTYPE ->
                  _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | RPAREN ->
              let x = _v in
              let _v = _menhir_action_085 x in
              _menhir_goto_separated_nonempty_list_COMMA_arg_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_arg_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState336 ->
          _menhir_run_337 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState320 ->
          _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_337 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_arg -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_arg (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_086 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_arg_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_323 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let x = _v in
      let _v = _menhir_action_067 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_arg__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_289 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RBRACK ->
          let MenhirCell1_IDENT (_menhir_stack, _menhir_s, id) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_007 id t in
          (match (_tok : MenhirBasics.token) with
          | COMMA ->
              let _menhir_stack = MenhirCell1_bytes_field (_menhir_stack, _menhir_s, _v) in
              let _menhir_s = MenhirState294 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v ->
                  _menhir_run_287 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | RBRACK ->
              let x = _v in
              let _v = _menhir_action_087 x in
              _menhir_goto_separated_nonempty_list_COMMA_bytes_field_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _menhir_fail ())
      | _ ->
          _eRR ()
  
  and _menhir_run_287 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState288 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULONGTYPE ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT8TYPE ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT32TYPE ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT16TYPE ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RULONGTYPE ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT8TYPE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT32TYPE ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT16TYPE ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RLONGTYPE ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT8TYPE ->
              _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT32TYPE ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT16TYPE ->
              _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RBOOLTYPE ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAULONG ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT8 ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT32 ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT16 ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RALONG ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT8 ->
              _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT32 ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT16 ->
              _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RABOOL ->
              _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORSTRUCT ->
              _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORLONGTYPE ->
              _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT8TYPE ->
              _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT32TYPE ->
              _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT16TYPE ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORBOOLTYPE ->
              _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAULONG ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT8 ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT32 ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT16 ->
              _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORALONG ->
              _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT8 ->
              _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT32 ->
              _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT16 ->
              _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORABOOL ->
              _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LONGTYPE ->
              _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT8TYPE ->
              _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT32TYPE ->
              _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT16TYPE ->
              _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FUNTYPE ->
              _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BYTES ->
              _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOLTYPE ->
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_bytes_field_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState294 ->
          _menhir_run_295 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState285 ->
          _menhir_run_290 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_295 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_bytes_field -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_bytes_field (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_088 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_bytes_field_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_290 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let x = _v in
      let _v = _menhir_action_069 x in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let xs = _v in
      let _v = _menhir_action_010 xs in
      _menhir_goto_bytes_fields _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_bytes_fields : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_bytes_fields (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | ARROW ->
          let _menhir_s = MenhirState298 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_284 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | RBRACK ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_009 () in
              _menhir_goto_bytes_fields _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INT32 _v_1 ->
              _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1
          | IDENT _v_2 ->
              _menhir_run_287 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState285
          | _ ->
              _eRR ())
      | EMPTYBRACKETS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_008 () in
          _menhir_goto_bytes_fields _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_272 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState273 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | LBRACK ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_189 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_s = MenhirState190 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              let _menhir_stack = MenhirCell1_LBRACE (_menhir_stack, _menhir_s) in
              let _menhir_s = MenhirState191 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | TILDE ->
                  _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRING _v ->
                  _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | REF ->
                  _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | OSOME ->
                  _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ONONE ->
                  _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MATCH ->
                  _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LET ->
                  _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT64 _v ->
                  _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | INT32 _v ->
                  _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | IF ->
                  _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | IDENT _v ->
                  _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | FOR ->
                  _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | DEREF ->
                  _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOL _v ->
                  _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | RBRACE ->
                  let _v = _menhir_action_072 () in
                  _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | _ ->
                  _eRR ())
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_178 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_ONONE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | DOT | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_ONONE (_menhir_stack, _menhir_s) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_064 t in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_161 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_s = MenhirState162 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_199 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_142 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RBRACE ->
          let MenhirCell1_IDENT (_menhir_stack, _menhir_s, id) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_065 id t in
          (match (_tok : MenhirBasics.token) with
          | COMMA ->
              let _menhir_stack = MenhirCell1_field_decl (_menhir_stack, _menhir_s, _v) in
              let _menhir_s = MenhirState147 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v ->
                  _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | RBRACE ->
              let x = _v in
              let _v = _menhir_action_093 x in
              _menhir_goto_separated_nonempty_list_COMMA_field_decl_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _menhir_fail ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_field_decl_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState147 ->
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState003 ->
          _menhir_run_143 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_148 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_field_decl -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_field_decl (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_094 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_field_decl_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_143 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let x = _v in
      let _v = _menhir_action_075 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_field_decl__ _menhir_stack _menhir_lexbuf _menhir_lexer _v
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_field_decl__ : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
      let MenhirCell1_STRUCT (_menhir_stack, _menhir_s) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_098 id xs in
      _menhir_goto_toplevel _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_138 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_effect__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | DOT | ELSE | EMPTYBRACKETS | EOF | EQ | FUNC | GE | GT | HASHEBPF | IDENT _ | IN | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RBRACK | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_loption_separated_nonempty_list_COMMA_effect__ (_menhir_stack, _, xs_inlined1) = _menhir_stack in
          let MenhirCell1_loption_separated_nonempty_list_COMMA_typ__ (_menhir_stack, _, xs) = _menhir_stack in
          let MenhirCell1_FUNTYPE (_menhir_stack, _menhir_s) = _menhir_stack in
          let ret = _v in
          let _v = _menhir_action_153 ret xs xs_inlined1 in
          _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_117 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState121 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULONGTYPE ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT8TYPE ->
              _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT32TYPE ->
              _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT16TYPE ->
              _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_011 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RULONGTYPE ->
              _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT8TYPE ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT32TYPE ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT16TYPE ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RLONGTYPE ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT8TYPE ->
              _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT32TYPE ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT16TYPE ->
              _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RBOOLTYPE ->
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAULONG ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT8 ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT32 ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT16 ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RALONG ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT8 ->
              _menhir_run_043 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT32 ->
              _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT16 ->
              _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RABOOL ->
              _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORSTRUCT ->
              _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORLONGTYPE ->
              _menhir_run_066 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT8TYPE ->
              _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT32TYPE ->
              _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT16TYPE ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORBOOLTYPE ->
              _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAULONG ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT8 ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT32 ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT16 ->
              _menhir_run_083 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORALONG ->
              _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT8 ->
              _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT32 ->
              _menhir_run_095 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT16 ->
              _menhir_run_099 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORABOOL ->
              _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LONGTYPE ->
              _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT8TYPE ->
              _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT32TYPE ->
              _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT16TYPE ->
              _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FUNTYPE ->
              _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BYTES ->
              _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOLTYPE ->
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_095 x in
          _menhir_goto_separated_nonempty_list_COMMA_typ_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_typ_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState114 ->
          _menhir_run_123 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState121 ->
          _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_123 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let x = _v in
      let _v = _menhir_action_077 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_typ__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_122 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_typ (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_096 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_typ_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  let _menhir_run_000 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRUCT ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | SECTION _v ->
          _menhir_run_149 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState000
      | HASHEBPF ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | FUNC | LET ->
          let _v = _menhir_action_003 () in
          _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState000 _tok
      | _ ->
          _eRR ()
  
end

let prog =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_prog v = _menhir_run_000 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
