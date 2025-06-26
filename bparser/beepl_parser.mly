%{
open Beepl_ast
%}

%token <string> IDENT
%token <int32> INT32
%token <int64> INT64
%token <bool> BOOL
%token INT8TYPE UINT8TYPE
%token INT16TYPE UINT16TYPE 
%token BOOLTYPE INT32TYPE UINT32TYPE ULONGTYPE LONGTYPE
%token UNIT
%token RBOOLTYPE RINT8TYPE RUINT8TYPE  
%token RINT16TYPE RUINT16TYPE RINT32TYPE RUINT32TYPE
%token RLONGTYPE RULONGTYPE RARRAY RSTRUCT
%token RABOOL RAINT8 RAUINT8 RAUINT16 RAINT16 RAINT32 RAUINT32 RALONG RAULONG
%token FUNTYPE
%token FUNC LET IN IF THEN ELSE 
%token LPAREN RPAREN COLON COMMA EQ
%token LBRACE RBRACE
%token IO DIVERGENCE READ WRITE ALLOC EMPTYBRACKETS
%token STRUCT
%token HASHEBPF
%token <string> SECTION
%token STAR    
%token EOF

%start <Beepl_ast.program> prog

%%

prog:
  | tops = toplevel_list EOF { tops }

toplevel_list:
  | tl = toplevel { [tl] }
  | tl = toplevel tlrest = toplevel_list { tl :: tlrest }

toplevel:
  | anns = annotations FUNC id = IDENT LPAREN args = separated_list(COMMA, arg) RPAREN
    COLON ret = typ COMMA effs = effect_list LBRACE body = expr RBRACE
    {
      let f = Tfundecl(id, ret, effs, args, [], body) in
      match anns with
      | (false, sec) -> Internal (f, sec)
      | (true, sec)  -> EBPFInternal (f, sec)
    }
  | STRUCT id = IDENT LBRACE fields = separated_list(COMMA, field_decl) RBRACE
    { StructDecl(id, fields) }

annotations:
  | anns = annotation_list { anns }

annotation_list:
  | HASHEBPF rest = annotation_list { let (is_ebpf, section) = rest in (true, section) }
  | secname = SECTION rest = annotation_list { let (is_ebpf, _) = rest in (is_ebpf, Some secname) }
  | /* empty */ { (false, None) }

effect_list:
  | EMPTYBRACKETS { [] }
  | separated_nonempty_list(COMMA, effect) { $1 }

arg:
  | t = typ id = IDENT { (id, t) }

field_decl:
  | id = IDENT COLON t = typ { (id, t) }

effect:
  | DIVERGENCE { Divergence }
  | READ id = IDENT { Read id }
  | WRITE id = IDENT { Write id }
  | ALLOC id = IDENT { Alloc id }
  | IO { Io }

typ:
  | BOOLTYPE  { Vtype Tbool }
  | UINT8TYPE { Vtype Tuint8 }
  | INT8TYPE  { Vtype Tint8 }
  | UINT16TYPE { Vtype Tuint16 }
  | INT16TYPE { Vtype Tint16 }
  | UINT32TYPE { Vtype Tuint32 }
  | INT32TYPE { Vtype Tint32 }
  | ULONGTYPE { Vtype Tulong }
  | LONGTYPE  { Vtype Tlong }
  | UNIT      { Utype }
  | RBOOLTYPE  { Ptr (Reftype ("h", (Bprim Tbool))) }
  | RINT8TYPE  { Ptr (Reftype ("h", (Bprim Tint8))) }
  | RUINT8TYPE { Ptr (Reftype ("h", (Bprim Tuint8))) }
  | RINT16TYPE { Ptr (Reftype ("h", (Bprim Tint16))) }
  | RUINT16TYPE { Ptr (Reftype ("h", (Bprim Tuint16))) }
  | RINT32TYPE { Ptr (Reftype ("h", (Bprim Tint32))) }
  | RUINT32TYPE { Ptr (Reftype ("h", (Bprim Tuint32))) }
  | RLONGTYPE { Ptr (Reftype ("h", (Bprim Tlong))) }
  | RULONGTYPE { Ptr (Reftype ("h", (Bprim Tulong))) }
  | STRUCT IDENT STAR { Ptr (Reftype ("h", (Bstruct $2))) }
  | RABOOL LBRACE n = INT32 RBRACE { Ptr (Reftype ("h", (Barray (Tbool, Int32.to_int n)))) }
  | RAINT8 LBRACE n = INT32 RBRACE { Ptr (Reftype ("h", (Barray (Tint8, Int32.to_int n)))) }
  | RAUINT8 LBRACE n = INT32 RBRACE { Ptr (Reftype ("h", (Barray (Tuint8, Int32.to_int n)))) }
  | RAINT16 LBRACE n = INT32 RBRACE { Ptr (Reftype ("h", (Barray (Tint16, Int32.to_int n)))) }
  | RAUINT16 LBRACE n = INT32 RBRACE { Ptr (Reftype ("h", (Barray (Tuint16, Int32.to_int n)))) }
  | RAINT32 LBRACE n = INT32 RBRACE { Ptr (Reftype ("h", (Barray (Tint32, Int32.to_int n)))) }
  | RAUINT32 LBRACE n = INT32 RBRACE { Ptr (Reftype ("h", (Barray (Tuint32, Int32.to_int n)))) }
  | RALONG LBRACE n = INT32 RBRACE { Ptr (Reftype ("h", (Barray (Tlong, Int32.to_int n)))) }
  | RAULONG LBRACE n = INT32 RBRACE { Ptr (Reftype ("h", (Barray (Tulong, Int32.to_int n)))) }
  | FUNTYPE LPAREN args = separated_list(COMMA, typ) RPAREN
    COLON eff = separated_list(COMMA, effect) COMMA ret = typ { Ftype(args, eff, ret) }

(* --- END OF typ --- *)

const:
  | b = BOOL { Cbool b }
  | UNIT     { Cunit }
  | i = INT32 { Cint32 i }
  | l = INT64 { Clong l }

expr:
  | id = IDENT { Var id }
  | c = const  { Const c }
  | fn = expr LPAREN args = separated_nonempty_list(COMMA, expr) RPAREN
    { App(fn, args) }
  | fn = expr LPAREN RPAREN
    { App(fn, []) }
  | LET id = IDENT COLON t = typ EQ e1 = expr IN e2 = expr
    { Let(id, t, e1, e2) }
  | IF e1 = expr THEN e2 = expr ELSE e3 = expr
    { If(e1, e2, e3) }
