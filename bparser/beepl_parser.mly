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
%token ORBOOLTYPE ORINT8TYPE ORUINT8TYPE  
%token ORINT16TYPE ORUINT16TYPE ORINT32TYPE ORUINT32TYPE
%token ORLONGTYPE ORULONGTYPE ORARRAY ORSTRUCT OSTRUCT
%token ORABOOL ORAINT8 ORAUINT8 ORAUINT16 ORAINT16 ORAINT32 ORAUINT32 ORALONG ORAULONG
%token FUNTYPE
%token FUNC LET IN IF THEN ELSE 
%token REF DEREF MASSGN
%token TILDE NEG PLUS MINUS MUL DIV MOD AND OR XOR SHL SHR OEQ NEQ LT GT LE GE
%token CAST
%token LPAREN RPAREN COLON COMMA EQ
%token LBRACE RBRACE
%token IO DIVERGENCE READ WRITE ALLOC EMPTYBRACKETS
%token STRUCT
%token HASHEBPF
%token <string> STRING
%token <string> SECTION
%token STAR    
%token EOF

%left PLUS MINUS       /* operators are left associative (a - b) - c */
%left MUL DIV MOD 
%left AND 
%left OR 
%left XOR
%left SHL
%left SHR
%nonassoc OEQ               /* comparison is non-associative a == b == c is not allowed */
%nonassoc NEQ              /* comparison is non-associative a != b != c is not allowed */
%nonassoc LT GT LE
%nonassoc DEREF REF UMINUS TILDE  /* unary operators are non-associative */
%right MASSGN

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
  | LET id = IDENT COLON t = typ EQ e = expr
    { GlobalLet(id, t, e) }

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
  | LPAREN RPAREN { Utype }   (* Allow () to mean unit *)
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
  | ORBOOLTYPE  { Ptr (Otype (Reftype ("h", (Bprim Tbool)))) }
  | ORINT8TYPE  { Ptr (Otype (Reftype ("h", (Bprim Tint8)))) }
  | ORUINT8TYPE { Ptr (Otype (Reftype ("h", (Bprim Tuint8)))) }
  | ORINT16TYPE { Ptr (Otype (Reftype ("h", (Bprim Tint16)))) }
  | ORUINT16TYPE { Ptr (Otype (Reftype ("h", (Bprim Tuint16)))) }
  | ORINT32TYPE { Ptr (Otype (Reftype ("h", (Bprim Tint32)))) }
  | ORUINT32TYPE { Ptr (Otype (Reftype ("h", (Bprim Tuint32)))) }
  | ORLONGTYPE { Ptr (Otype (Reftype ("h", (Bprim Tlong)))) }
  | ORULONGTYPE { Ptr (Otype (Reftype ("h", (Bprim Tulong)))) }
  | OSTRUCT IDENT STAR { Ptr (Otype (Reftype ("h", (Bstruct $2)))) }
  | ORABOOL LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tbool, Int32.to_int n))))) }
  | ORAINT8 LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tint8, Int32.to_int n))))) }
  | ORAUINT8 LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tuint8, Int32.to_int n))))) }
  | ORAINT16 LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tint16, Int32.to_int n))))) }
  | ORAUINT16 LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tuint16, Int32.to_int n))))) }
  | ORAINT32 LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tint32, Int32.to_int n))))) }
  | ORAUINT32 LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tuint32, Int32.to_int n))))) }
  | ORALONG LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tlong, Int32.to_int n))))) }
  | ORAULONG LBRACE n = INT32 RBRACE { Ptr (Otype ((Reftype ("h", (Barray (Tulong, Int32.to_int n)))))) }
  | FUNTYPE LPAREN args = separated_list(COMMA, typ) RPAREN
    COLON eff = separated_list(COMMA, effect) COMMA ret = typ { Ftype(args, eff, ret) }

(* --- END OF typ --- *)

const:
  | b = BOOL { Cbool b }
  | UNIT     { Cunit }
  | i = INT32 { Cint32 i }
  | l = INT64 { Clong l }
  | s = STRING { Cstring s }

expr:
  | LPAREN expr RPAREN          { $2 }
  | id = IDENT { Var id }
  | c = const  { Const c }
   (* Unary operators *)
  | TILDE e = expr
    { Prim (Uop UOverloadTilde, [e]) }
  | MINUS e = expr %prec UMINUS
    { Prim (Uop Oneg, [e]) } 
    (* Binary operators *)
  | e1 = expr PLUS e2= expr 
    { Prim (Bop Oadd, [e1; e2]) }
  | e1 = expr MINUS e2= expr 
    { Prim (Bop Osub, [e1; e2]) }
  | e1 = expr MUL e2= expr 
    { Prim (Bop Omul, [e1; e2]) }
  | e1 = expr DIV e2= expr 
    { Prim (Bop Odiv, [e1; e2]) }
  | e1 = expr MOD e2= expr 
    { Prim (Bop Omod, [e1; e2]) }
  | e1 = expr AND e2= expr 
    { Prim (Bop Oand, [e1; e2]) }
  | e1 = expr OR e2= expr 
    { Prim (Bop Oor, [e1; e2]) }
  | e1 = expr XOR e2 = expr
    { Prim (Bop Oxor, [e1; e2]) }
  | e1 = expr SHL e2 = expr
    { Prim (Bop Oshl, [e1; e2]) }
  | e1 = expr SHR e2 = expr
    { Prim (Bop Oshr, [e1; e2]) }
  | e1 = expr OEQ e2 = expr
    { Prim (Bop Oeq, [e1; e2]) }
  | e1 = expr NEQ e2 = expr
    { Prim (Bop One, [e1; e2]) } 
  | e1 = expr LT e2 = expr
    { Prim (Bop Olt, [e1; e2]) }
  | e1 = expr GT e2 = expr
    { Prim (Bop Ogt, [e1; e2]) }  
  | e1 = expr LE e2 = expr
    { Prim (Bop Ole, [e1; e2]) } 
  | e1 = expr GE e2 = expr
    { Prim (Bop Oge, [e1; e2]) }
  | LPAREN t = typ RPAREN e = expr 
    {Prim (Cast t, [e]) }
  | REF e = expr 
    {Prim (Ref, [e])}
  | DEREF e = expr 
    {Prim (Deref, [e])}
  | e1 = expr MASSGN e2 = expr
    { Prim (Massgn, [e1; e2]) }
  (* Function application *)
  | fn = expr LPAREN args = separated_nonempty_list(COMMA, expr) RPAREN
    { App(fn, args) }
  | fn = expr LPAREN RPAREN
    { App(fn, []) }
  | LET id = IDENT COLON t = typ EQ e1 = expr IN e2 = expr
    { Let(id, t, e1, e2) }
  | IF e1 = expr THEN e2 = expr ELSE e3 = expr
    { If(e1, e2, e3) }
