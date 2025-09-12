
(* The type of tokens. *)

type token = 
  | XOR
  | WRITE
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
  | STRING of (string)
  | STAR
  | SINIT
  | SHR
  | SHL
  | SECTION of (string)
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
  | OSTRUCT
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
  | OEQ
  | NEQ
  | NEG
  | MUL
  | MOD
  | MINUS
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
  | INT64 of (int64)
  | INT32TYPE
  | INT32 of (int32)
  | INT16TYPE
  | IN
  | IF
  | IDENT of (string)
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
  | BOOL of (bool)
  | ARRAY
  | AND
  | ALLOC
  | AINIT
  | AACEESS

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Beepl_ast.program)
