
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
    | OSTRUCT
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
# 110 "bparser/beepl_parser.ml"
  )
    | INT32TYPE
    | INT32 of (
# 6 "bparser/beepl_parser.mly"
       (int32)
# 116 "bparser/beepl_parser.ml"
  )
    | INT16TYPE
    | IN
    | IF
    | IDENT of (
# 5 "bparser/beepl_parser.mly"
       (string)
# 124 "bparser/beepl_parser.ml"
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

  | MenhirState120 : (('s, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 120.
        Stack shape : typ.
        Start symbol: prog. *)

  | MenhirState125 : ((('s, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__, _menhir_box_prog) _menhir_state
    (** State 125.
        Stack shape : FUNTYPE loption(separated_nonempty_list(COMMA,typ)).
        Start symbol: prog. *)

  | MenhirState136 : (((('s, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_effect__, _menhir_box_prog) _menhir_state
    (** State 136.
        Stack shape : FUNTYPE loption(separated_nonempty_list(COMMA,typ)) loption(separated_nonempty_list(COMMA,effect)).
        Start symbol: prog. *)

  | MenhirState139 : (('s, _menhir_box_prog) _menhir_cell1_effect, _menhir_box_prog) _menhir_state
    (** State 139.
        Stack shape : effect.
        Start symbol: prog. *)

  | MenhirState146 : (('s, _menhir_box_prog) _menhir_cell1_field_decl, _menhir_box_prog) _menhir_state
    (** State 146.
        Stack shape : field_decl.
        Start symbol: prog. *)

  | MenhirState148 : (('s, _menhir_box_prog) _menhir_cell1_SECTION, _menhir_box_prog) _menhir_state
    (** State 148.
        Stack shape : SECTION.
        Start symbol: prog. *)

  | MenhirState149 : (('s, _menhir_box_prog) _menhir_cell1_HASHEBPF, _menhir_box_prog) _menhir_state
    (** State 149.
        Stack shape : HASHEBPF.
        Start symbol: prog. *)

  | MenhirState154 : (('s, _menhir_box_prog) _menhir_cell1_toplevel, _menhir_box_prog) _menhir_state
    (** State 154.
        Stack shape : toplevel.
        Start symbol: prog. *)

  | MenhirState159 : (('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 159.
        Stack shape : annotations IDENT.
        Start symbol: prog. *)

  | MenhirState161 : ((('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 161.
        Stack shape : annotations IDENT typ.
        Start symbol: prog. *)

  | MenhirState163 : (('s, _menhir_box_prog) _menhir_cell1_TILDE, _menhir_box_prog) _menhir_state
    (** State 163.
        Stack shape : TILDE.
        Start symbol: prog. *)

  | MenhirState166 : (('s, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 166.
        Stack shape : STRUCT IDENT.
        Start symbol: prog. *)

  | MenhirState168 : (('s, _menhir_box_prog) _menhir_cell1_IDENT, _menhir_box_prog) _menhir_state
    (** State 168.
        Stack shape : IDENT.
        Start symbol: prog. *)

  | MenhirState172 : ((('s, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_separated_nonempty_list_COMMA_IDENT_, _menhir_box_prog) _menhir_state
    (** State 172.
        Stack shape : STRUCT IDENT separated_nonempty_list(COMMA,IDENT).
        Start symbol: prog. *)

  | MenhirState174 : (('s, _menhir_box_prog) _menhir_cell1_REF, _menhir_box_prog) _menhir_state
    (** State 174.
        Stack shape : REF.
        Start symbol: prog. *)

  | MenhirState175 : (('s, _menhir_box_prog) _menhir_cell1_OSOME, _menhir_box_prog) _menhir_state
    (** State 175.
        Stack shape : OSOME.
        Start symbol: prog. *)

  | MenhirState176 : (('s, _menhir_box_prog) _menhir_cell1_ONONE, _menhir_box_prog) _menhir_state
    (** State 176.
        Stack shape : ONONE.
        Start symbol: prog. *)

  | MenhirState178 : (('s, _menhir_box_prog) _menhir_cell1_MINUS, _menhir_box_prog) _menhir_state
    (** State 178.
        Stack shape : MINUS.
        Start symbol: prog. *)

  | MenhirState179 : (('s, _menhir_box_prog) _menhir_cell1_MATCH, _menhir_box_prog) _menhir_state
    (** State 179.
        Stack shape : MATCH.
        Start symbol: prog. *)

  | MenhirState180 : (('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 180.
        Stack shape : LPAREN.
        Start symbol: prog. *)

  | MenhirState184 : ((('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 184.
        Stack shape : LPAREN LPAREN.
        Start symbol: prog. *)

  | MenhirState187 : (('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 187.
        Stack shape : LET IDENT.
        Start symbol: prog. *)

  | MenhirState189 : ((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 189.
        Stack shape : LET IDENT typ.
        Start symbol: prog. *)

  | MenhirState190 : (((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_LBRACE, _menhir_box_prog) _menhir_state
    (** State 190.
        Stack shape : LET IDENT typ LBRACE.
        Start symbol: prog. *)

  | MenhirState193 : (('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_state
    (** State 193.
        Stack shape : IF.
        Start symbol: prog. *)

  | MenhirState199 : (('s, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_state
    (** State 199.
        Stack shape : FOR.
        Start symbol: prog. *)

  | MenhirState200 : (('s, _menhir_box_prog) _menhir_cell1_DEREF, _menhir_box_prog) _menhir_state
    (** State 200.
        Stack shape : DEREF.
        Start symbol: prog. *)

  | MenhirState203 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 203.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState208 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 208.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState210 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 210.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState212 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 212.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState214 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 214.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState219 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 219.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState221 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 221.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState223 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 223.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState225 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 225.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState227 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 227.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState229 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 229.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState231 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 231.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState233 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 233.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState235 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 235.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState237 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 237.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState239 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 239.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState241 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 241.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState243 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 243.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState245 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 245.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState248 : ((('s, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 248.
        Stack shape : FOR expr.
        Start symbol: prog. *)

  | MenhirState254 : (((('s, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_dir, _menhir_box_prog) _menhir_state
    (** State 254.
        Stack shape : FOR expr expr dir.
        Start symbol: prog. *)

  | MenhirState258 : ((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 258.
        Stack shape : IF expr.
        Start symbol: prog. *)

  | MenhirState260 : (((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 260.
        Stack shape : IF expr expr.
        Start symbol: prog. *)

  | MenhirState266 : (((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 266.
        Stack shape : LET IDENT typ expr.
        Start symbol: prog. *)

  | MenhirState269 : (((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_array_elems, _menhir_box_prog) _menhir_state
    (** State 269.
        Stack shape : LET IDENT typ array_elems.
        Start symbol: prog. *)

  | MenhirState272 : ((('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 272.
        Stack shape : LPAREN typ.
        Start symbol: prog. *)

  | MenhirState279 : ((('s, _menhir_box_prog) _menhir_cell1_MATCH, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_option_BAR_, _menhir_box_prog) _menhir_state
    (** State 279.
        Stack shape : MATCH expr option(BAR).
        Start symbol: prog. *)

  | MenhirState282 : (('s, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 282.
        Stack shape : PBYTES IDENT.
        Start symbol: prog. *)

  | MenhirState284 : ((('s, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 284.
        Stack shape : PBYTES IDENT typ.
        Start symbol: prog. *)

  | MenhirState286 : (('s, _menhir_box_prog) _menhir_cell1_IDENT, _menhir_box_prog) _menhir_state
    (** State 286.
        Stack shape : IDENT.
        Start symbol: prog. *)

  | MenhirState291 : (((('s, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_bytes_field__, _menhir_box_prog) _menhir_state
    (** State 291.
        Stack shape : PBYTES IDENT typ loption(separated_nonempty_list(COMMA,bytes_field)).
        Start symbol: prog. *)

  | MenhirState294 : (('s, _menhir_box_prog) _menhir_cell1_bytes_field, _menhir_box_prog) _menhir_state
    (** State 294.
        Stack shape : bytes_field.
        Start symbol: prog. *)

  | MenhirState298 : (('s, _menhir_box_prog) _menhir_cell1_OSOME _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 298.
        Stack shape : OSOME IDENT.
        Start symbol: prog. *)

  | MenhirState301 : (('s, _menhir_box_prog) _menhir_cell1_ONONE, _menhir_box_prog) _menhir_state
    (** State 301.
        Stack shape : ONONE.
        Start symbol: prog. *)

  | MenhirState305 : (('s, _menhir_box_prog) _menhir_cell1_clause, _menhir_box_prog) _menhir_state
    (** State 305.
        Stack shape : clause.
        Start symbol: prog. *)

  | MenhirState316 : (('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 316.
        Stack shape : annotations IDENT.
        Start symbol: prog. *)

  | MenhirState322 : ((('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_state
    (** State 322.
        Stack shape : annotations IDENT loption(separated_nonempty_list(COMMA,arg)).
        Start symbol: prog. *)

  | MenhirState324 : (((('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 324.
        Stack shape : annotations IDENT loption(separated_nonempty_list(COMMA,arg)) typ.
        Start symbol: prog. *)

  | MenhirState328 : ((((('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_effect_list, _menhir_box_prog) _menhir_state
    (** State 328.
        Stack shape : annotations IDENT loption(separated_nonempty_list(COMMA,arg)) typ effect_list.
        Start symbol: prog. *)

  | MenhirState332 : (('s, _menhir_box_prog) _menhir_cell1_arg, _menhir_box_prog) _menhir_state
    (** State 332.
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

and ('s, 'r) _menhir_cell1_loption_separated_nonempty_list_COMMA_bytes_field__ = 
  | MenhirCell1_loption_separated_nonempty_list_COMMA_bytes_field__ of 's * ('s, 'r) _menhir_state * ((string * Beepl_ast.typ) list)

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
# 600 "bparser/beepl_parser.ml"
)

and 's _menhir_cell0_IDENT = 
  | MenhirCell0_IDENT of 's * (
# 5 "bparser/beepl_parser.mly"
       (string)
# 607 "bparser/beepl_parser.ml"
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
# 644 "bparser/beepl_parser.ml"
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
# 661 "bparser/beepl_parser.ml"
     : (bool * string option))

let _menhir_action_002 =
  fun rest secname ->
    (
# 88 "bparser/beepl_parser.mly"
                                             ( let (is_ebpf, _) = rest in (is_ebpf, Some secname) )
# 669 "bparser/beepl_parser.ml"
     : (bool * string option))

let _menhir_action_003 =
  fun () ->
    (
# 89 "bparser/beepl_parser.mly"
                ( (false, None) )
# 677 "bparser/beepl_parser.ml"
     : (bool * string option))

let _menhir_action_004 =
  fun anns ->
    (
# 84 "bparser/beepl_parser.mly"
                           ( anns )
# 685 "bparser/beepl_parser.ml"
     : (bool * string option))

let _menhir_action_005 =
  fun id t ->
    (
# 96 "bparser/beepl_parser.mly"
                       ( (id, t) )
# 693 "bparser/beepl_parser.ml"
     : (string * Beepl_ast.typ))

let _menhir_action_006 =
  fun xs ->
    let xs = 
# 241 "<standard.mly>"
    ( xs )
# 701 "bparser/beepl_parser.ml"
     in
    (
# 177 "bparser/beepl_parser.mly"
                                                   ( xs )
# 706 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_007 =
  fun id t ->
    (
# 180 "bparser/beepl_parser.mly"
                             ( (id, t) )
# 714 "bparser/beepl_parser.ml"
     : (string * Beepl_ast.typ))

let _menhir_action_008 =
  fun e id ->
    (
# 202 "bparser/beepl_parser.mly"
                                 ( (Psome id, e) )
# 722 "bparser/beepl_parser.ml"
     : (Beepl_ast.pattern * Beepl_ast.expr))

let _menhir_action_009 =
  fun e ->
    (
# 203 "bparser/beepl_parser.mly"
                                 ( (Pnone   , e) )
# 730 "bparser/beepl_parser.ml"
     : (Beepl_ast.pattern * Beepl_ast.expr))

let _menhir_action_010 =
  fun e id t xs ->
    let fields = 
# 241 "<standard.mly>"
    ( xs )
# 738 "bparser/beepl_parser.ml"
     in
    (
# 207 "bparser/beepl_parser.mly"
    ( (Pbytes (id, t, fields), e) )
# 743 "bparser/beepl_parser.ml"
     : (Beepl_ast.pattern * Beepl_ast.expr))

let _menhir_action_011 =
  fun b ->
    (
# 170 "bparser/beepl_parser.mly"
             ( Cbool b )
# 751 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_012 =
  fun () ->
    (
# 171 "bparser/beepl_parser.mly"
             ( Cunit )
# 759 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_013 =
  fun i ->
    (
# 172 "bparser/beepl_parser.mly"
              ( Cint32 i )
# 767 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_014 =
  fun l ->
    (
# 173 "bparser/beepl_parser.mly"
              ( Clong l )
# 775 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_015 =
  fun s ->
    (
# 174 "bparser/beepl_parser.mly"
               ( Cstring s )
# 783 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_016 =
  fun () ->
    (
# 166 "bparser/beepl_parser.mly"
         ( Up )
# 791 "bparser/beepl_parser.ml"
     : (Beepl_ast.dir))

let _menhir_action_017 =
  fun () ->
    (
# 167 "bparser/beepl_parser.mly"
         ( Down )
# 799 "bparser/beepl_parser.ml"
     : (Beepl_ast.dir))

let _menhir_action_018 =
  fun () ->
    (
# 102 "bparser/beepl_parser.mly"
               ( Divergence )
# 807 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_019 =
  fun id ->
    (
# 103 "bparser/beepl_parser.mly"
                    ( Read id )
# 815 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_020 =
  fun id ->
    (
# 104 "bparser/beepl_parser.mly"
                     ( Write id )
# 823 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_021 =
  fun id ->
    (
# 105 "bparser/beepl_parser.mly"
                     ( Alloc id )
# 831 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_022 =
  fun () ->
    (
# 106 "bparser/beepl_parser.mly"
       ( Io )
# 839 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_023 =
  fun () ->
    (
# 92 "bparser/beepl_parser.mly"
                  ( [] )
# 847 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_024 =
  fun _1 ->
    (
# 93 "bparser/beepl_parser.mly"
                                           ( _1 )
# 855 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_025 =
  fun _2 ->
    (
# 210 "bparser/beepl_parser.mly"
                                ( _2 )
# 863 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_026 =
  fun id ->
    (
# 211 "bparser/beepl_parser.mly"
               ( Var id )
# 871 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_027 =
  fun c ->
    (
# 212 "bparser/beepl_parser.mly"
               ( Const c )
# 879 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_028 =
  fun e ->
    (
# 215 "bparser/beepl_parser.mly"
    ( Prim (Uop UOverloadTilde, [e]) )
# 887 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_029 =
  fun e ->
    (
# 217 "bparser/beepl_parser.mly"
    ( Prim (Uop Oneg, [e]) )
# 895 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_030 =
  fun e1 e2 ->
    (
# 220 "bparser/beepl_parser.mly"
    ( Prim (Bop Oadd, [e1; e2]) )
# 903 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_031 =
  fun e1 e2 ->
    (
# 222 "bparser/beepl_parser.mly"
    ( Prim (Bop Osub, [e1; e2]) )
# 911 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_032 =
  fun e1 e2 ->
    (
# 224 "bparser/beepl_parser.mly"
    ( Prim (Bop Omul, [e1; e2]) )
# 919 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_033 =
  fun e1 e2 ->
    (
# 226 "bparser/beepl_parser.mly"
    ( Prim (Bop Odiv, [e1; e2]) )
# 927 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_034 =
  fun e1 e2 ->
    (
# 228 "bparser/beepl_parser.mly"
    ( Prim (Bop Omod, [e1; e2]) )
# 935 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_035 =
  fun e1 e2 ->
    (
# 230 "bparser/beepl_parser.mly"
    ( Prim (Bop Oand, [e1; e2]) )
# 943 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_036 =
  fun e1 e2 ->
    (
# 232 "bparser/beepl_parser.mly"
    ( Prim (Bop Oor, [e1; e2]) )
# 951 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_037 =
  fun e1 e2 ->
    (
# 234 "bparser/beepl_parser.mly"
    ( Prim (Bop Oxor, [e1; e2]) )
# 959 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_038 =
  fun e1 e2 ->
    (
# 236 "bparser/beepl_parser.mly"
    ( Prim (Bop Oshl, [e1; e2]) )
# 967 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_039 =
  fun e1 e2 ->
    (
# 238 "bparser/beepl_parser.mly"
    ( Prim (Bop Oshr, [e1; e2]) )
# 975 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_040 =
  fun e1 e2 ->
    (
# 240 "bparser/beepl_parser.mly"
    ( Prim (Bop Oeq, [e1; e2]) )
# 983 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_041 =
  fun e1 e2 ->
    (
# 242 "bparser/beepl_parser.mly"
    ( Prim (Bop One, [e1; e2]) )
# 991 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_042 =
  fun e1 e2 ->
    (
# 244 "bparser/beepl_parser.mly"
    ( Prim (Bop Olt, [e1; e2]) )
# 999 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_043 =
  fun e1 e2 ->
    (
# 246 "bparser/beepl_parser.mly"
    ( Prim (Bop Ogt, [e1; e2]) )
# 1007 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_044 =
  fun e1 e2 ->
    (
# 248 "bparser/beepl_parser.mly"
    ( Prim (Bop Ole, [e1; e2]) )
# 1015 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_045 =
  fun e1 e2 ->
    (
# 250 "bparser/beepl_parser.mly"
    ( Prim (Bop Oge, [e1; e2]) )
# 1023 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_046 =
  fun e t ->
    (
# 252 "bparser/beepl_parser.mly"
    (Prim (Cast t, [e]) )
# 1031 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_047 =
  fun e ->
    (
# 254 "bparser/beepl_parser.mly"
    (Prim (Ref, [e]))
# 1039 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_048 =
  fun e ->
    (
# 256 "bparser/beepl_parser.mly"
    (Prim (Deref, [e]))
# 1047 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_049 =
  fun e1 e2 ->
    (
# 258 "bparser/beepl_parser.mly"
    ( Prim (Massgn, [e1; e2]) )
# 1055 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_050 =
  fun args fn ->
    (
# 261 "bparser/beepl_parser.mly"
    ( App(fn, args) )
# 1063 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_051 =
  fun fn ->
    (
# 263 "bparser/beepl_parser.mly"
    ( App(fn, []) )
# 1071 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_052 =
  fun e2 elems id t ->
    (
# 265 "bparser/beepl_parser.mly"
    ( 
      match t with
      | Atype (_, _) -> Let(id, t, Ainit(id, elems), e2)
      | _ -> failwith "Array initializer {..} can only initialize an array type"
    )
# 1083 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_053 =
  fun e1 e2 id t ->
    (
# 271 "bparser/beepl_parser.mly"
    ( Let(id, t, e1, e2) )
# 1091 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_054 =
  fun e1 e2 e3 ->
    (
# 273 "bparser/beepl_parser.mly"
    ( If(e1, e2, e3) )
# 1099 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_055 =
  fun d e1 e2 e3 ->
    (
# 275 "bparser/beepl_parser.mly"
    ( For(e1, e2, d, e3) )
# 1107 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_056 =
  fun args fields id ->
    (
# 278 "bparser/beepl_parser.mly"
    ( Sinit(id, fields, args) )
# 1115 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_057 =
  fun e id ->
    (
# 280 "bparser/beepl_parser.mly"
    ( Fget(e, id) )
# 1123 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_058 =
  fun id n ->
    (
# 282 "bparser/beepl_parser.mly"
    ( Aaccess(id, Int32.to_int n) )
# 1131 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_059 =
  fun cs e optbar ->
    (
# 284 "bparser/beepl_parser.mly"
    ( 
      let pats, bodies = List.split cs in
      Match(e, pats, bodies)
    )
# 1142 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_060 =
  fun e ->
    (
# 288 "bparser/beepl_parser.mly"
                   ( Esome e )
# 1150 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_061 =
  fun t ->
    (
# 289 "bparser/beepl_parser.mly"
                      ( Enone t)
# 1158 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_062 =
  fun id t ->
    (
# 99 "bparser/beepl_parser.mly"
                             ( (id, t) )
# 1166 "bparser/beepl_parser.ml"
     : (string * Beepl_ast.typ))

let _menhir_action_063 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1174 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_064 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1182 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_065 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1190 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_066 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1198 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_067 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1206 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_068 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1214 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_069 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1222 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_070 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1230 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_071 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1238 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_072 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1246 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_073 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1254 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ list))

let _menhir_action_074 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1262 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ list))

let _menhir_action_075 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 1270 "bparser/beepl_parser.ml"
     : (unit option))

let _menhir_action_076 =
  fun x ->
    (
# 114 "<standard.mly>"
    ( Some x )
# 1278 "bparser/beepl_parser.ml"
     : (unit option))

let _menhir_action_077 =
  fun tops ->
    (
# 58 "bparser/beepl_parser.mly"
                             ( tops )
# 1286 "bparser/beepl_parser.ml"
     : (Beepl_ast.program))

let _menhir_action_078 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1294 "bparser/beepl_parser.ml"
     : ((Beepl_ast.pattern * Beepl_ast.expr) list))

let _menhir_action_079 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1302 "bparser/beepl_parser.ml"
     : ((Beepl_ast.pattern * Beepl_ast.expr) list))

let _menhir_action_080 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1310 "bparser/beepl_parser.ml"
     : (string list))

let _menhir_action_081 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1318 "bparser/beepl_parser.ml"
     : (string list))

let _menhir_action_082 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1326 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_083 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1334 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_084 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1342 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_085 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1350 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_086 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1358 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_087 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1366 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_088 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1374 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_089 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1382 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_090 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1390 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_091 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1398 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_092 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1406 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ list))

let _menhir_action_093 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1414 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ list))

let _menhir_action_094 =
  fun anns body effs id ret xs ->
    let args = 
# 241 "<standard.mly>"
    ( xs )
# 1422 "bparser/beepl_parser.ml"
     in
    (
# 67 "bparser/beepl_parser.mly"
    (
      let f = Tfundecl(id, ret, effs, args, [], body) in
      match anns with
      | (false, sec) -> Internal (f, sec)
      | (true, sec)  -> EBPFInternal (f, sec)
    )
# 1432 "bparser/beepl_parser.ml"
     : (Beepl_ast.toplevel))

let _menhir_action_095 =
  fun id xs ->
    let fields = 
# 241 "<standard.mly>"
    ( xs )
# 1440 "bparser/beepl_parser.ml"
     in
    (
# 74 "bparser/beepl_parser.mly"
    ( StructDecl(id, fields) )
# 1445 "bparser/beepl_parser.ml"
     : (Beepl_ast.toplevel))

let _menhir_action_096 =
  fun anns e id t ->
    (
# 76 "bparser/beepl_parser.mly"
    (
      match anns with
      | (false, sec) -> GlobalLet(id, t, e, sec)
      | (true, sec)  -> failwith "Global let cannot be eBPF"
    )
# 1457 "bparser/beepl_parser.ml"
     : (Beepl_ast.toplevel))

let _menhir_action_097 =
  fun tl ->
    (
# 61 "bparser/beepl_parser.mly"
                  ( [tl] )
# 1465 "bparser/beepl_parser.ml"
     : (Beepl_ast.program))

let _menhir_action_098 =
  fun tl tlrest ->
    (
# 62 "bparser/beepl_parser.mly"
                                         ( tl :: tlrest )
# 1473 "bparser/beepl_parser.ml"
     : (Beepl_ast.program))

let _menhir_action_099 =
  fun () ->
    (
# 109 "bparser/beepl_parser.mly"
              ( Vtype Tbool )
# 1481 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_100 =
  fun () ->
    (
# 110 "bparser/beepl_parser.mly"
              ( Vtype Tuint8 )
# 1489 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_101 =
  fun () ->
    (
# 111 "bparser/beepl_parser.mly"
              ( Vtype Tint8 )
# 1497 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_102 =
  fun () ->
    (
# 112 "bparser/beepl_parser.mly"
               ( Vtype Tuint16 )
# 1505 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_103 =
  fun () ->
    (
# 113 "bparser/beepl_parser.mly"
              ( Vtype Tint16 )
# 1513 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_104 =
  fun () ->
    (
# 114 "bparser/beepl_parser.mly"
               ( Vtype Tuint32 )
# 1521 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_105 =
  fun () ->
    (
# 115 "bparser/beepl_parser.mly"
              ( Vtype Tint32 )
# 1529 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_106 =
  fun () ->
    (
# 116 "bparser/beepl_parser.mly"
              ( Vtype Tulong )
# 1537 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_107 =
  fun () ->
    (
# 117 "bparser/beepl_parser.mly"
              ( Vtype Tlong )
# 1545 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_108 =
  fun () ->
    (
# 118 "bparser/beepl_parser.mly"
                  ( Utype )
# 1553 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_109 =
  fun () ->
    (
# 119 "bparser/beepl_parser.mly"
              ( Utype )
# 1561 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_110 =
  fun () ->
    (
# 120 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ("h", (Bprim Tbool))) )
# 1569 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_111 =
  fun () ->
    (
# 121 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ("h", (Bprim Tint8))) )
# 1577 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_112 =
  fun () ->
    (
# 122 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ("h", (Bprim Tuint8))) )
# 1585 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_113 =
  fun () ->
    (
# 123 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ("h", (Bprim Tint16))) )
# 1593 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_114 =
  fun () ->
    (
# 124 "bparser/beepl_parser.mly"
                ( Ptr (Reftype ("h", (Bprim Tuint16))) )
# 1601 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_115 =
  fun () ->
    (
# 125 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ("h", (Bprim Tint32))) )
# 1609 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_116 =
  fun () ->
    (
# 126 "bparser/beepl_parser.mly"
                ( Ptr (Reftype ("h", (Bprim Tuint32))) )
# 1617 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_117 =
  fun () ->
    (
# 127 "bparser/beepl_parser.mly"
              ( Ptr (Reftype ("h", (Bprim Tlong))) )
# 1625 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_118 =
  fun () ->
    (
# 128 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ("h", (Bprim Tulong))) )
# 1633 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_119 =
  fun _2 ->
    (
# 129 "bparser/beepl_parser.mly"
                     ( Ptr (Reftype ("h", (Bstruct _2))) )
# 1641 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_120 =
  fun n ->
    (
# 130 "bparser/beepl_parser.mly"
                                   ( Ptr (Reftype ("h", (Barray (Tbool, Int32.to_int n)))) )
# 1649 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_121 =
  fun n ->
    (
# 131 "bparser/beepl_parser.mly"
                                   ( Ptr (Reftype ("h", (Barray (Tint8, Int32.to_int n)))) )
# 1657 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_122 =
  fun n ->
    (
# 132 "bparser/beepl_parser.mly"
                                    ( Ptr (Reftype ("h", (Barray (Tuint8, Int32.to_int n)))) )
# 1665 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_123 =
  fun n ->
    (
# 133 "bparser/beepl_parser.mly"
                                    ( Ptr (Reftype ("h", (Barray (Tint16, Int32.to_int n)))) )
# 1673 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_124 =
  fun n ->
    (
# 134 "bparser/beepl_parser.mly"
                                     ( Ptr (Reftype ("h", (Barray (Tuint16, Int32.to_int n)))) )
# 1681 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_125 =
  fun n ->
    (
# 135 "bparser/beepl_parser.mly"
                                    ( Ptr (Reftype ("h", (Barray (Tint32, Int32.to_int n)))) )
# 1689 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_126 =
  fun n ->
    (
# 136 "bparser/beepl_parser.mly"
                                     ( Ptr (Reftype ("h", (Barray (Tuint32, Int32.to_int n)))) )
# 1697 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_127 =
  fun n ->
    (
# 137 "bparser/beepl_parser.mly"
                                   ( Ptr (Reftype ("h", (Barray (Tlong, Int32.to_int n)))) )
# 1705 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_128 =
  fun n ->
    (
# 138 "bparser/beepl_parser.mly"
                                    ( Ptr (Reftype ("h", (Barray (Tulong, Int32.to_int n)))) )
# 1713 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_129 =
  fun () ->
    (
# 139 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ("h", (Bprim Tbool)))) )
# 1721 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_130 =
  fun () ->
    (
# 140 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ("h", (Bprim Tint8)))) )
# 1729 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_131 =
  fun () ->
    (
# 141 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ("h", (Bprim Tuint8)))) )
# 1737 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_132 =
  fun () ->
    (
# 142 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ("h", (Bprim Tint16)))) )
# 1745 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_133 =
  fun () ->
    (
# 143 "bparser/beepl_parser.mly"
                 ( Ptr (Otype (Reftype ("h", (Bprim Tuint16)))) )
# 1753 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_134 =
  fun () ->
    (
# 144 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ("h", (Bprim Tint32)))) )
# 1761 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_135 =
  fun () ->
    (
# 145 "bparser/beepl_parser.mly"
                 ( Ptr (Otype (Reftype ("h", (Bprim Tuint32)))) )
# 1769 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_136 =
  fun () ->
    (
# 146 "bparser/beepl_parser.mly"
               ( Ptr (Otype (Reftype ("h", (Bprim Tlong)))) )
# 1777 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_137 =
  fun () ->
    (
# 147 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ("h", (Bprim Tulong)))) )
# 1785 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_138 =
  fun _2 ->
    (
# 148 "bparser/beepl_parser.mly"
                       ( Ptr (Otype (Reftype ("h", (Bstruct _2)))) )
# 1793 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_139 =
  fun n ->
    (
# 149 "bparser/beepl_parser.mly"
                                    ( Ptr (Otype (Reftype ("h", (Barray (Tbool, Int32.to_int n))))) )
# 1801 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_140 =
  fun n ->
    (
# 150 "bparser/beepl_parser.mly"
                                    ( Ptr (Otype (Reftype ("h", (Barray (Tint8, Int32.to_int n))))) )
# 1809 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_141 =
  fun n ->
    (
# 151 "bparser/beepl_parser.mly"
                                     ( Ptr (Otype (Reftype ("h", (Barray (Tuint8, Int32.to_int n))))) )
# 1817 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_142 =
  fun n ->
    (
# 152 "bparser/beepl_parser.mly"
                                     ( Ptr (Otype (Reftype ("h", (Barray (Tint16, Int32.to_int n))))) )
# 1825 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_143 =
  fun n ->
    (
# 153 "bparser/beepl_parser.mly"
                                      ( Ptr (Otype (Reftype ("h", (Barray (Tuint16, Int32.to_int n))))) )
# 1833 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_144 =
  fun n ->
    (
# 154 "bparser/beepl_parser.mly"
                                     ( Ptr (Otype (Reftype ("h", (Barray (Tint32, Int32.to_int n))))) )
# 1841 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_145 =
  fun n ->
    (
# 155 "bparser/beepl_parser.mly"
                                      ( Ptr (Otype (Reftype ("h", (Barray (Tuint32, Int32.to_int n))))) )
# 1849 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_146 =
  fun n ->
    (
# 156 "bparser/beepl_parser.mly"
                                    ( Ptr (Otype (Reftype ("h", (Barray (Tlong, Int32.to_int n))))) )
# 1857 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_147 =
  fun n ->
    (
# 157 "bparser/beepl_parser.mly"
                                     ( Ptr (Otype ((Reftype ("h", (Barray (Tulong, Int32.to_int n)))))) )
# 1865 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_148 =
  fun id ->
    (
# 158 "bparser/beepl_parser.mly"
                      ( Stype id )
# 1873 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_149 =
  fun n t ->
    (
# 159 "bparser/beepl_parser.mly"
                                    ( Atype(t, Int32.to_int n) )
# 1881 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_150 =
  fun ret xs xs_inlined1 ->
    let eff =
      let xs = xs_inlined1 in
      
# 241 "<standard.mly>"
    ( xs )
# 1891 "bparser/beepl_parser.ml"
      
    in
    let args = 
# 241 "<standard.mly>"
    ( xs )
# 1897 "bparser/beepl_parser.ml"
     in
    (
# 161 "bparser/beepl_parser.mly"
                                                              ( Ftype(args, eff, ret) )
# 1902 "bparser/beepl_parser.ml"
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
    | OSTRUCT ->
        "OSTRUCT"
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
  
  let _menhir_run_152 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_prog =
    fun _menhir_stack _v ->
      let tops = _v in
      let _v = _menhir_action_077 tops in
      MenhirBox_prog _v
  
  let rec _menhir_goto_toplevel_list : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState154 ->
          _menhir_run_155 _menhir_stack _v
      | MenhirState000 ->
          _menhir_run_152 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_155 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_toplevel -> _ -> _menhir_box_prog =
    fun _menhir_stack _v ->
      let MenhirCell1_toplevel (_menhir_stack, _menhir_s, tl) = _menhir_stack in
      let tlrest = _v in
      let _v = _menhir_action_098 tl tlrest in
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
                  let _v = _menhir_action_071 () in
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
          | OSTRUCT ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
          | BOOLTYPE ->
              _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_006 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_109 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_typ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState322 ->
          _menhir_run_323 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState332 ->
          _menhir_run_317 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState316 ->
          _menhir_run_317 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState286 ->
          _menhir_run_287 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState282 ->
          _menhir_run_283 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState180 ->
          _menhir_run_271 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState184 ->
          _menhir_run_271 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState187 ->
          _menhir_run_188 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState176 ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState159 ->
          _menhir_run_160 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState005 ->
          _menhir_run_141 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState136 ->
          _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState120 ->
          _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState114 ->
          _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_323 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WRITE ->
              _menhir_run_126 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState324
          | READ ->
              _menhir_run_128 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState324
          | IO ->
              _menhir_run_130 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState324
          | EMPTYBRACKETS ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _menhir_s = MenhirState324 in
              let _v = _menhir_action_023 () in
              _menhir_goto_effect_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | DIVERGENCE ->
              _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState324
          | ALLOC ->
              _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState324
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_117 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | INT32 _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | RBRACK ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let MenhirCell1_typ (_menhir_stack, _menhir_s, t) = _menhir_stack in
              let n = _v in
              let _v = _menhir_action_149 n t in
              _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_126 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let id = _v in
          let _v = _menhir_action_020 id in
          _menhir_goto_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_effect : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_effect (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState139 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WRITE ->
              _menhir_run_126 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | READ ->
              _menhir_run_128 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IO ->
              _menhir_run_130 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DIVERGENCE ->
              _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ALLOC ->
              _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | LBRACE ->
          let x = _v in
          let _v = _menhir_action_086 x in
          _menhir_goto_separated_nonempty_list_COMMA_effect_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_128 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let id = _v in
          let _v = _menhir_action_019 id in
          _menhir_goto_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_130 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_022 () in
      _menhir_goto_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_131 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_018 () in
      _menhir_goto_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_132 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let id = _v in
          let _v = _menhir_action_021 id in
          _menhir_goto_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_effect_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState324 ->
          _menhir_run_326 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState139 ->
          _menhir_run_140 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState125 ->
          _menhir_run_134 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_326 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_024 _1 in
      _menhir_goto_effect_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_effect_list : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_effect_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _menhir_s = MenhirState328 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_162 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_012 () in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_const : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let c = _v in
      let _v = _menhir_action_027 c in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState328 ->
          _menhir_run_329 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState161 ->
          _menhir_run_313 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState163 ->
          _menhir_run_312 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState174 ->
          _menhir_run_309 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState175 ->
          _menhir_run_308 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState178 ->
          _menhir_run_307 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState301 ->
          _menhir_run_302 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState298 ->
          _menhir_run_299 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState291 ->
          _menhir_run_292 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState179 ->
          _menhir_run_276 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState180 ->
          _menhir_run_274 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState184 ->
          _menhir_run_274 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState272 ->
          _menhir_run_273 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState269 ->
          _menhir_run_270 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState266 ->
          _menhir_run_267 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState189 ->
          _menhir_run_265 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState260 ->
          _menhir_run_261 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState258 ->
          _menhir_run_259 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState193 ->
          _menhir_run_257 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState254 ->
          _menhir_run_255 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState248 ->
          _menhir_run_249 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState199 ->
          _menhir_run_247 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState243 ->
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState241 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState239 ->
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState237 ->
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState233 ->
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState231 ->
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState229 ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState227 ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState225 ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState223 ->
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState221 ->
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState219 ->
          _menhir_run_220 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState214 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState212 ->
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState208 ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState172 ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState190 ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState245 ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState203 ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState200 ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_329 : type  ttv_stack. (((((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_effect_list as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_effect_list (_menhir_stack, _, effs) = _menhir_stack in
          let MenhirCell1_typ (_menhir_stack, _, ret) = _menhir_stack in
          let MenhirCell1_loption_separated_nonempty_list_COMMA_arg__ (_menhir_stack, _, xs) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_annotations (_menhir_stack, _menhir_s, anns) = _menhir_stack in
          let body = _v in
          let _v = _menhir_action_094 anns body effs id ret xs in
          _menhir_goto_toplevel _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_208 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState208 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_163 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_TILDE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState163 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_164 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_STRUCT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_166 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState166 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          _menhir_run_167 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_167 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState168 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              _menhir_run_167 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_080 x in
          _menhir_goto_separated_nonempty_list_COMMA_IDENT_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_IDENT_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState166 ->
          _menhir_run_170 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState168 ->
          _menhir_run_169 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_170 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_separated_nonempty_list_COMMA_IDENT_ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState172 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_173 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let s = _v in
      let _v = _menhir_action_015 s in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_174 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_REF (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState174 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_175 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_OSOME (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState175 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_176 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ONONE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState176 in
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
      | OSTRUCT ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORULONGTYPE ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT8TYPE ->
          _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT32TYPE ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT16TYPE ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
      | BOOLTYPE ->
          _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_007 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_106 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_008 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_100 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_009 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_104 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_010 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_102 () in
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
          | AND | BAR | COMMA | DIV | DOT | ELSE | EOF | EQ | FUNC | GE | GT | HASHEBPF | IDENT _ | IN | LBRACK | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
              let id = _v in
              let _v = _menhir_action_148 id in
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
      let _v = _menhir_action_119 _2 in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_014 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_118 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_015 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_112 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_016 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_116 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_017 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_114 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_018 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_117 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_019 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_111 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_020 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_115 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_021 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_113 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_022 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_110 () in
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
                  let _v = _menhir_action_128 n in
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
                  let _v = _menhir_action_122 n in
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
                  let _v = _menhir_action_126 n in
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
                  let _v = _menhir_action_124 n in
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
                  let _v = _menhir_action_127 n in
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
                  let _v = _menhir_action_121 n in
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
                  let _v = _menhir_action_125 n in
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
                  let _v = _menhir_action_123 n in
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
                  let _v = _menhir_action_120 n in
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
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | STAR ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _2 = _v in
              let _v = _menhir_action_138 _2 in
              _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_062 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_137 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_063 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_131 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_064 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_135 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_065 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_133 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_066 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_136 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_067 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_130 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_068 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_134 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_069 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_132 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_070 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_129 () in
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
                  let _v = _menhir_action_147 n in
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
                  let _v = _menhir_action_141 n in
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
                  let _v = _menhir_action_145 n in
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
                  let _v = _menhir_action_143 n in
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
                  let _v = _menhir_action_146 n in
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
                  let _v = _menhir_action_140 n in
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
                  let _v = _menhir_action_144 n in
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
                  let _v = _menhir_action_142 n in
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
                  let _v = _menhir_action_139 n in
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
      let _v = _menhir_action_108 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_109 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_107 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_110 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_101 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_111 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_105 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_112 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_103 () in
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
          | OSTRUCT ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
          | BOOLTYPE ->
              _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RPAREN ->
              let _v = _menhir_action_073 () in
              _menhir_goto_loption_separated_nonempty_list_COMMA_typ__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_115 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_099 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_typ__ : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_loption_separated_nonempty_list_COMMA_typ__ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState125 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WRITE ->
              _menhir_run_126 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | READ ->
              _menhir_run_128 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IO ->
              _menhir_run_130 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DIVERGENCE ->
              _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ALLOC ->
              _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | COMMA ->
              let _v = _menhir_action_067 () in
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
          let _menhir_s = MenhirState136 in
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
          | OSTRUCT ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
          | BOOLTYPE ->
              _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_178 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MINUS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState178 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_179 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MATCH (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState179 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_180 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState180 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ULONGTYPE ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT8TYPE ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT32TYPE ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT16TYPE ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
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
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
      | OSTRUCT ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORULONGTYPE ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT8TYPE ->
          _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT32TYPE ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT16TYPE ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_184 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LONGTYPE ->
          _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT8TYPE ->
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32TYPE ->
          _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT16TYPE ->
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FUNTYPE ->
          _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOLTYPE ->
          _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_181 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | AND | DIV | DOT | GE | GT | LE | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | SHL | SHR | XOR ->
          let _v = _menhir_action_012 () in
          _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | LBRACK | RPAREN ->
          let _v = _menhir_action_109 () in
          _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_182 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
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
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer
          | LBRACK | RPAREN ->
              let id = _v in
              let _v = _menhir_action_148 id in
              _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_184 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState184 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ULONGTYPE ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT8TYPE ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT32TYPE ->
          _menhir_run_009 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT16TYPE ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
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
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
      | OSTRUCT ->
          _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORULONGTYPE ->
          _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT8TYPE ->
          _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT32TYPE ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT16TYPE ->
          _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_184 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LONGTYPE ->
          _menhir_run_109 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT8TYPE ->
          _menhir_run_110 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32TYPE ->
          _menhir_run_111 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT16TYPE ->
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FUNTYPE ->
          _menhir_run_113 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOLTYPE ->
          _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_185 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LET (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | COLON ->
              let _menhir_s = MenhirState187 in
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
              | OSTRUCT ->
                  _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORULONGTYPE ->
                  _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT8TYPE ->
                  _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT32TYPE ->
                  _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT16TYPE ->
                  _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
              | BOOLTYPE ->
                  _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_191 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let l = _v in
      let _v = _menhir_action_014 l in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_192 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let i = _v in
      let _v = _menhir_action_013 i in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_193 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState193 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_194 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
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
                  let _v = _menhir_action_058 id n in
                  _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | AND | BAR | COMMA | DIV | DOT | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let id = _v in
          let _v = _menhir_action_026 id in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_198 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_FOR (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState199 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_200 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DEREF (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState200 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_201 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let b = _v in
      let _v = _menhir_action_011 b in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_169 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_IDENT -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_IDENT (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_081 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_IDENT_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_210 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState210 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_225 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState225 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_toplevel : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STRUCT ->
          let _menhir_stack = MenhirCell1_toplevel (_menhir_stack, _menhir_s, _v) in
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState154
      | SECTION _v_0 ->
          let _menhir_stack = MenhirCell1_toplevel (_menhir_stack, _menhir_s, _v) in
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState154
      | HASHEBPF ->
          let _menhir_stack = MenhirCell1_toplevel (_menhir_stack, _menhir_s, _v) in
          _menhir_run_149 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState154
      | FUNC | LET ->
          let _menhir_stack = MenhirCell1_toplevel (_menhir_stack, _menhir_s, _v) in
          let _v_1 = _menhir_action_003 () in
          _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState154 _tok
      | EOF ->
          let tl = _v in
          let _v = _menhir_action_097 tl in
          _menhir_goto_toplevel_list _menhir_stack _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_148 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_SECTION (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SECTION _v_0 ->
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState148
      | HASHEBPF ->
          _menhir_run_149 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState148
      | FUNC | LET ->
          let _v_1 = _menhir_action_003 () in
          _menhir_run_151 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_149 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_HASHEBPF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SECTION _v ->
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState149
      | HASHEBPF ->
          _menhir_run_149 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState149
      | FUNC | LET ->
          let _v = _menhir_action_003 () in
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_150 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_HASHEBPF -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_HASHEBPF (_menhir_stack, _menhir_s) = _menhir_stack in
      let rest = _v in
      let _v = _menhir_action_001 rest in
      _menhir_goto_annotation_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_annotation_list : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState000 ->
          _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState154 ->
          _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState148 ->
          _menhir_run_151 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState149 ->
          _menhir_run_150 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_334 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
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
                  let _menhir_s = MenhirState159 in
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
                  | OSTRUCT ->
                      _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORULONGTYPE ->
                      _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT8TYPE ->
                      _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT32TYPE ->
                      _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT16TYPE ->
                      _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
                  | BOOLTYPE ->
                      _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
                  let _menhir_s = MenhirState316 in
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
                  | OSTRUCT ->
                      _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORULONGTYPE ->
                      _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT8TYPE ->
                      _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT32TYPE ->
                      _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT16TYPE ->
                      _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
                  | BOOLTYPE ->
                      _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RPAREN ->
                      let _v = _menhir_action_063 () in
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
          let _menhir_s = MenhirState322 in
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
          | OSTRUCT ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
          | BOOLTYPE ->
              _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_151 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_SECTION -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_SECTION (_menhir_stack, _menhir_s, secname) = _menhir_stack in
      let rest = _v in
      let _v = _menhir_action_002 rest secname in
      _menhir_goto_annotation_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_212 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState212 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_241 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState241 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_227 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState227 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_237 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState237 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_214 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState214 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_219 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState219 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_223 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState223 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_243 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState243 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_229 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState229 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_203 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState203
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, fn) = _menhir_stack in
          let _v = _menhir_action_051 fn in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState203
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState203
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState203
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState203
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState203
      | _ ->
          _eRR ()
  
  and _menhir_run_231 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState231 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_233 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState233 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_235 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState235 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_216 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e) = _menhir_stack in
          let id = _v in
          let _v = _menhir_action_057 e id in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_221 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState221 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_239 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState239 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_313 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EOF | FUNC | HASHEBPF | LET | SECTION _ | STRUCT ->
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_annotations (_menhir_stack, _menhir_s, anns) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_096 anns e id t in
          _menhir_goto_toplevel _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_312 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_TILDE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_TILDE (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_028 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_309 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_REF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_REF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_047 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_308 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_OSOME as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_OSOME (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_060 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_307 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MINUS as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_MINUS (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_029 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_302 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_ONONE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_ONONE (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_009 e in
          _menhir_goto_clause _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_clause : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | BAR ->
          let _menhir_stack = MenhirCell1_clause (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState305 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PBYTES ->
              _menhir_run_280 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_296 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_300 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | AND | COMMA | DIV | DOT | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let x = _v in
          let _v = _menhir_action_078 x in
          _menhir_goto_separated_nonempty_list_BAR_clause_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_280 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PBYTES (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | COLON ->
              let _menhir_s = MenhirState282 in
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
              | OSTRUCT ->
                  _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORULONGTYPE ->
                  _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT8TYPE ->
                  _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT32TYPE ->
                  _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT16TYPE ->
                  _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
              | BOOLTYPE ->
                  _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_296 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_OSOME (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ARROW ->
              let _menhir_s = MenhirState298 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | TILDE ->
                  _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRING _v ->
                  _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | REF ->
                  _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | OSOME ->
                  _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ONONE ->
                  _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MATCH ->
                  _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LET ->
                  _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT64 _v ->
                  _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | INT32 _v ->
                  _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | IF ->
                  _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | IDENT _v ->
                  _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | FOR ->
                  _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | DEREF ->
                  _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOL _v ->
                  _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_300 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ONONE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ARROW ->
          let _menhir_s = MenhirState301 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_BAR_clause_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState305 ->
          _menhir_run_306 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState279 ->
          _menhir_run_303 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_306 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_clause -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_clause (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_079 x xs in
      _menhir_goto_separated_nonempty_list_BAR_clause_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_303 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MATCH, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_option_BAR_ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_option_BAR_ (_menhir_stack, optbar) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, e) = _menhir_stack in
      let MenhirCell1_MATCH (_menhir_stack, _menhir_s) = _menhir_stack in
      let cs = _v in
      let _v = _menhir_action_059 cs e optbar in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_299 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_OSOME _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_OSOME (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_008 e id in
          _menhir_goto_clause _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_292 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_bytes_field__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_loption_separated_nonempty_list_COMMA_bytes_field__ (_menhir_stack, _, xs) = _menhir_stack in
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_PBYTES (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_010 e id t xs in
          _menhir_goto_clause _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_276 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MATCH as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | WITH ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | BAR ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let x = () in
              let _v = _menhir_action_076 x in
              _menhir_goto_option_BAR_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | ONONE | OSOME | PBYTES ->
              let _v = _menhir_action_075 () in
              _menhir_goto_option_BAR_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | SHR ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_option_BAR_ : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MATCH, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_option_BAR_ (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | PBYTES ->
          _menhir_run_280 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState279
      | OSOME ->
          _menhir_run_296 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState279
      | ONONE ->
          _menhir_run_300 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState279
      | _ ->
          _eRR ()
  
  and _menhir_run_274 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_025 _2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_273 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_046 e t in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_270 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_array_elems as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_array_elems (_menhir_stack, _, elems) = _menhir_stack in
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_052 e2 elems id t in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_267 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_053 e1 e2 id t in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_265 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IN ->
          let _menhir_s = MenhirState266 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | GT ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_261 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_expr (_menhir_stack, _, e2) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e3 = _v in
          let _v = _menhir_action_054 e1 e2 e3 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_259 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE ->
          let _menhir_s = MenhirState260 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | DOT ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_257 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | THEN ->
          let _menhir_s = MenhirState258 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | SHR ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_255 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_dir as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_dir (_menhir_stack, d) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, e2) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_FOR (_menhir_stack, _menhir_s) = _menhir_stack in
          let e3 = _v in
          let _v = _menhir_action_055 d e1 e2 e3 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_249 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UP ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_016 () in
              _menhir_goto_dir _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | DOWN ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_017 () in
              _menhir_goto_dir _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | AND ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_dir : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_dir (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_s = MenhirState254 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_247 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_FOR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_s = MenhirState248 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | AND ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_244 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_049 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_242 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_036 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_240 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_035 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_238 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_041 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_236 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_045 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_234 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_043 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_232 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_044 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_230 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_042 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_228 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_040 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_226 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_038 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_224 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_031 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_222 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_033 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_220 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_034 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_215 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_032 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_213 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_030 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_211 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_039 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_209 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_037 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_207 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_208 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_219 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState245 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RBRACE | RPAREN ->
          let x = _v in
          let _v = _menhir_action_088 x in
          _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_expr_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState172 ->
          _menhir_run_310 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState190 ->
          _menhir_run_262 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState245 ->
          _menhir_run_246 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState203 ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_310 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_separated_nonempty_list_COMMA_IDENT_ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_separated_nonempty_list_COMMA_IDENT_ (_menhir_stack, _, fields) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_STRUCT (_menhir_stack, _menhir_s) = _menhir_stack in
          let args = _v in
          let _v = _menhir_action_056 args fields id in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_262 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_LBRACE -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let x = _v in
      let _v = _menhir_action_070 x in
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
              let _menhir_s = MenhirState269 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | TILDE ->
                  _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRING _v ->
                  _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | REF ->
                  _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | OSOME ->
                  _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ONONE ->
                  _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MATCH ->
                  _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LET ->
                  _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT64 _v ->
                  _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | INT32 _v ->
                  _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | IF ->
                  _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | IDENT _v ->
                  _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | FOR ->
                  _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | DEREF ->
                  _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOL _v ->
                  _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_246 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_089 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_205 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, fn) = _menhir_stack in
          let args = _v in
          let _v = _menhir_action_050 args fn in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_202 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_DEREF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_DEREF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_048 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_140 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_effect -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_effect (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_087 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_effect_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_134 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let x = _v in
      let _v = _menhir_action_068 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_effect__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_317 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IDENT _v_0 ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (id, t) = (_v_0, _v) in
          let _v = _menhir_action_005 id t in
          (match (_tok : MenhirBasics.token) with
          | COMMA ->
              let _menhir_stack = MenhirCell1_arg (_menhir_stack, _menhir_s, _v) in
              let _menhir_s = MenhirState332 in
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
              | OSTRUCT ->
                  _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORULONGTYPE ->
                  _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT8TYPE ->
                  _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT32TYPE ->
                  _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT16TYPE ->
                  _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
              | BOOLTYPE ->
                  _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | RPAREN ->
              let x = _v in
              let _v = _menhir_action_082 x in
              _menhir_goto_separated_nonempty_list_COMMA_arg_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_arg_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState332 ->
          _menhir_run_333 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState316 ->
          _menhir_run_319 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_333 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_arg -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_arg (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_083 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_arg_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_319 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let x = _v in
      let _v = _menhir_action_064 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_arg__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_287 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RPAREN ->
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
                  _menhir_run_285 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | RPAREN ->
              let x = _v in
              let _v = _menhir_action_084 x in
              _menhir_goto_separated_nonempty_list_COMMA_bytes_field_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _menhir_fail ())
      | _ ->
          _eRR ()
  
  and _menhir_run_285 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState286 in
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
          | OSTRUCT ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
          | BOOLTYPE ->
              _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_bytes_field_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState294 ->
          _menhir_run_295 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState284 ->
          _menhir_run_288 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_295 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_bytes_field -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_bytes_field (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_085 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_bytes_field_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_288 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let x = _v in
      let _v = _menhir_action_066 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_bytes_field__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_bytes_field__ : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_loption_separated_nonempty_list_COMMA_bytes_field__ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ARROW ->
          let _menhir_s = MenhirState291 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_283 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState284 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              _menhir_run_285 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | RPAREN ->
              let _v = _menhir_action_065 () in
              _menhir_goto_loption_separated_nonempty_list_COMMA_bytes_field__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | LBRACK ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_271 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState272 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | LBRACK ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_188 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_s = MenhirState189 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              let _menhir_stack = MenhirCell1_LBRACE (_menhir_stack, _menhir_s) in
              let _menhir_s = MenhirState190 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | TILDE ->
                  _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRING _v ->
                  _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | REF ->
                  _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | OSOME ->
                  _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ONONE ->
                  _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MATCH ->
                  _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LET ->
                  _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT64 _v ->
                  _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | INT32 _v ->
                  _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | IF ->
                  _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | IDENT _v ->
                  _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | FOR ->
                  _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | DEREF ->
                  _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOL _v ->
                  _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | RBRACE ->
                  let _v = _menhir_action_069 () in
                  _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | _ ->
                  _eRR ())
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_177 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_ONONE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | DOT | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_ONONE (_menhir_stack, _menhir_s) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_061 t in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_160 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_s = MenhirState161 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_163 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_173 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_174 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_185 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_191 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_192 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_198 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_201 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_141 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RBRACE ->
          let MenhirCell1_IDENT (_menhir_stack, _menhir_s, id) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_062 id t in
          (match (_tok : MenhirBasics.token) with
          | COMMA ->
              let _menhir_stack = MenhirCell1_field_decl (_menhir_stack, _menhir_s, _v) in
              let _menhir_s = MenhirState146 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v ->
                  _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | RBRACE ->
              let x = _v in
              let _v = _menhir_action_090 x in
              _menhir_goto_separated_nonempty_list_COMMA_field_decl_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _menhir_fail ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_field_decl_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState146 ->
          _menhir_run_147 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState003 ->
          _menhir_run_142 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_147 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_field_decl -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_field_decl (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_091 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_field_decl_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_142 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let x = _v in
      let _v = _menhir_action_072 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_field_decl__ _menhir_stack _menhir_lexbuf _menhir_lexer _v
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_field_decl__ : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
      let MenhirCell1_STRUCT (_menhir_stack, _menhir_s) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_095 id xs in
      _menhir_goto_toplevel _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_137 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_effect__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | DOT | ELSE | EOF | EQ | FUNC | GE | GT | HASHEBPF | IDENT _ | IN | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_loption_separated_nonempty_list_COMMA_effect__ (_menhir_stack, _, xs_inlined1) = _menhir_stack in
          let MenhirCell1_loption_separated_nonempty_list_COMMA_typ__ (_menhir_stack, _, xs) = _menhir_stack in
          let MenhirCell1_FUNTYPE (_menhir_stack, _menhir_s) = _menhir_stack in
          let ret = _v in
          let _v = _menhir_action_150 ret xs xs_inlined1 in
          _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_116 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState120 in
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
          | OSTRUCT ->
              _menhir_run_059 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_062 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_065 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
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
          | BOOLTYPE ->
              _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_092 x in
          _menhir_goto_separated_nonempty_list_COMMA_typ_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_typ_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState114 ->
          _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState120 ->
          _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_122 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let x = _v in
      let _v = _menhir_action_074 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_typ__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_121 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_typ (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_093 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_typ_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  let _menhir_run_000 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | STRUCT ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | SECTION _v ->
          _menhir_run_148 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState000
      | HASHEBPF ->
          _menhir_run_149 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | FUNC | LET ->
          let _v = _menhir_action_003 () in
          _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState000 _tok
      | _ ->
          _eRR ()
  
end

let prog =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_prog v = _menhir_run_000 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
