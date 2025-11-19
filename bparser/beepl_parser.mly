%{
open Beepl_ast
%}

%token <string> IDENT
%token <int32> INT32
%token <int64> INT64
%token <bool> BOOL
%token UP DOWN DOT
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
%token ORLONGTYPE ORULONGTYPE ORARRAY ORSTRUCT
%token ORABOOL ORAINT8 ORAUINT8 ORAUINT16 ORAINT16 ORAINT32 ORAUINT32 ORALONG ORAULONG
%token FUNTYPE TSTRUCT BYTES
%token FUNC LET IN IF THEN ELSE 
%token REF DEREF MASSGN
%token BAR OSOME ONONE
%token SINIT MATCH PBYTES WITH ARROW
%token TILDE NEG PLUS MINUS MUL DIV MOD AND OR XOR SHL SHR OEQ NEQ LT GT LE GE
%token CAST
%token FOR
%token LPAREN RPAREN COLON COMMA EQ
%token LBRACE RBRACE
%token ARRAY LBRACK RBRACK
%token IO DIVERGENCE READ WRITE ALLOC EMPTYBRACKETS
%token STRUCT
%token AINIT AACEESS
%token HASHEBPF
%token <string> STRING
%token <string> SECTION
%token STAR    
%token EOF

%right  MASSGN            /* := lowest precedence, right-assoc */
%left   OR                /* |  (lowest among bitwise) */
%left   XOR               /* ^ */
%left   AND               /* &  (highest among bitwise) */
%nonassoc OEQ NEQ         /* == != */
%nonassoc LT LE GT GE     /* < <= > >= */
%left   SHL SHR           /* << >> */
%left   PLUS MINUS        /* + - */
%left   MUL DIV MOD       /* * / % */
%nonassoc DEREF REF UMINUS TILDE   /* unary: highest */

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
  | anns = annotations LET id = IDENT COLON t = typ EQ e = expr
    {
      match anns with
      | (false, sec) -> GlobalLet(id, t, e, sec)
      | (true, sec)  -> failwith "Global let cannot be eBPF"
    }
  

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
  | STRUCT IDENT MUL { Ptr (Reftype ("h", (Bstruct $2))) }
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
  | ORSTRUCT IDENT MUL { Ptr (Otype (Reftype ("h", (Bstruct $2)))) }
  | ORABOOL LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tbool, Int32.to_int n))))) }
  | ORAINT8 LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tint8, Int32.to_int n))))) }
  | ORAUINT8 LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tuint8, Int32.to_int n))))) }
  | ORAINT16 LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tint16, Int32.to_int n))))) }
  | ORAUINT16 LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tuint16, Int32.to_int n))))) }
  | ORAINT32 LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tint32, Int32.to_int n))))) }
  | ORAUINT32 LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tuint32, Int32.to_int n))))) }
  | ORALONG LBRACE n = INT32 RBRACE { Ptr (Otype (Reftype ("h", (Barray (Tlong, Int32.to_int n))))) }
  | ORAULONG LBRACE n = INT32 RBRACE { Ptr (Otype ((Reftype ("h", (Barray (Tulong, Int32.to_int n)))))) }
  | STRUCT id = IDENT { Stype id }
  | t = typ LBRACK n = INT32 RBRACK { Atype(t, Int32.to_int n) }
  | FUNTYPE LPAREN args = separated_list(COMMA, typ) RPAREN
    COLON eff = separated_list(COMMA, effect) COMMA ret = typ { Ftype(args, eff, ret) }
  | BYTES { Bytes }

(* --- END OF typ --- *)

dir : 
  | UP   { Up }
  | DOWN { Down }

const:
  | b = BOOL { Cbool b }
  | UNIT     { Cunit }
  | i = INT32 { Cint32 i }
  | l = INT64 { Clong l }
  | s = STRING { Cstring s }

array_elems:
  | LBRACE xs = separated_list(COMMA, expr) RBRACE { xs }

bytes_field:
  | id = IDENT COLON t = typ { (id, t) }

bytes_fields:
  /* empty [] as a single token from the lexer */
  | EMPTYBRACKETS                                  { [] }
  /* empty [] as two tokens */
  | LBRACK RBRACK                                  { [] }
  /* non-empty [ f0, f1, ... ] */
  | LBRACK xs = separated_list(COMMA, bytes_field) RBRACK  { xs }

/* The pattern nonterminal */
pattern:
  | OSOME id = IDENT
      { Psome id }
  | ONONE
      { Pnone }
  | PBYTES id = IDENT COLON t = typ fields=bytes_fields
      { Pbytes (id, t, fields) }

/* A single case:  pattern -> expr 
match_branch:
  | OR p = pattern ARROW e = expr        { (p, e) } */

/* non-empty list of patterns 
match_branches:
  | b=match_branch bs=match_branches { b :: bs }
  | b=match_branch                  { [b] } */

clause:
  | OSOME id=IDENT ARROW e=expr  { (Psome id, e) }
  | ONONE        ARROW e=expr    { (Pnone   , e) }
  | PBYTES id=IDENT COLON t=typ fields=bytes_fields
    ARROW e=expr
    { (Pbytes (id, t, fields), e) }

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
  | LET id = IDENT COLON t = typ EQ elems = array_elems IN e2 = expr
    { 
      match t with
      | Atype (_, _) -> Let(id, t, Ainit(id, elems), e2)
      | _ -> failwith "Array initializer {..} can only initialize an array type"
    }
  | LET id = IDENT COLON t = typ EQ e1 = expr IN e2 = expr
    { Let(id, t, e1, e2) }
  | IF e1 = expr THEN e2 = expr ELSE e3 = expr
    { If(e1, e2, e3) }
  | FOR LPAREN e1 = expr COMMA e2 = expr COMMA d = dir COMMA e3 = expr RPAREN
    { For(e1, e2, d, e3) } 
  | STRUCT id = IDENT LPAREN fields = separated_nonempty_list(COMMA, IDENT) RPAREN
    LPAREN args = separated_nonempty_list(COMMA, expr) RPAREN
    { Sinit(id, fields, args) }
  | e = expr DOT id = IDENT
    { Fget(e, id) }
  | id = IDENT LBRACK n = INT32 RBRACK
    { Aaccess(id, Int32.to_int n) }
  | MATCH e=expr WITH optbar=option(BAR) cs=separated_nonempty_list(BAR, clause)
    { 
      let pats, bodies = List.split cs in
      Match(e, pats, bodies)
    }
  | OSOME e = expr { Esome e }
  | ONONE t = typ     { Enone t}
  
