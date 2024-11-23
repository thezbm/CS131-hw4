%{
open Ast
open Lexing

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token EOF
%token NULL
%token NEW
%token <bool>   BOOL
%token <int64>  INT
%token <string> STRING
%token <string> IDENT

%token TINT     /* int */
%token TBOOL    /* bool */
%token TVOID    /* void */
%token TSTRING  /* string */
%token IF       /* if */
%token ELSE     /* else */
%token FOR      /* for */
%token WHILE    /* while */
%token RETURN   /* return */
%token VAR      /* var */
%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token SHL      /* << */
%token SHR      /* >> */
%token SHRA     /* >>> */
%token EQEQ     /* == */
%token NEQ      /* != */
%token LT       /* < */
%token LTEQ     /* <= */
%token GT       /* > */
%token GTEQ     /* >= */
%token LAND     /* & */
%token LOR      /* | */
%token BAND     /* [&] */
%token BOR      /* [|] */
%token EQ       /* = */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token TILDE    /* ~ */
%token BANG     /* ! */
%token GLOBAL   /* global */


/* Operator precedences */
%left BOR
%left BAND
%left LOR
%left LAND
%left EQEQ NEQ
%left LT LTEQ GT GTEQ
%left SHL SHR SHRA
%left PLUS DASH
%left STAR
%nonassoc BANG
%nonassoc TILDE
%nonassoc LBRACKET
%nonassoc LPAREN

/* ---------------------------------------------------------------------- */

%start prog
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block> block
%type <Ast.ty> ty
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(decl) EOF  { p }

decl:
  | GLOBAL name=IDENT EQ init=gexp SEMI
    { Gvdecl (loc $startpos $endpos { name; init }) }
  | frtyp=ret_ty fname=IDENT LPAREN args=arglist RPAREN body=block
    { Gfdecl (loc $startpos $endpos { frtyp; fname; args; body }) }

arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }

%inline ty:
  | r=btyp { r }
  | r=rtyp { TRef r }

%inline btyp:
  | TINT   { TInt }
  | TBOOL  { TBool }

%inline ret_ty:
  | TVOID  { RetVoid }
  | t=ty   { RetVal t }

rtyp:
  | TSTRING { RString }
  | t=ty LBRACKET RBRACKET { RArray t }

%inline bop:
  | PLUS   { Add }
  | DASH   { Sub }
  | STAR   { Mul }
  | EQEQ   { Eq }
  | NEQ    { Neq }
  | LT     { Lt }
  | LTEQ   { Lte }
  | GT     { Gt }
  | GTEQ   { Gte }
  | LAND   { And }
  | LOR    { Or }
  | BAND   { IAnd }
  | BOR    { IOr }
  | SHL    { Shl }
  | SHR    { Shr }
  | SHRA   { Sar }

%inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

gexp:
  | i=INT       { loc $startpos $endpos @@ CInt i }
  | s=STRING    { loc $startpos $endpos @@ CStr s }
  | t=rtyp NULL { loc $startpos $endpos @@ CNull t }
  | b=BOOL      { loc $startpos $endpos @@ CBool b }
  | NEW t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, gexp) RBRACE
                { loc $startpos $endpos @@ CArr (t, es) }

lhs:
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }


exp:
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | i=INT               { loc $startpos $endpos @@ CInt i }
  | s=STRING            { loc $startpos $endpos @@ CStr s }
  | t=rtyp NULL         { loc $startpos $endpos @@ CNull t }
  | b=BOOL              { loc $startpos $endpos @@ CBool b }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }

  | NEW t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, exp) RBRACE
                        { loc $startpos $endpos @@ CArr (t, es) }

  | NEW t=btyp LBRACKET e=exp RBRACKET
                        { loc $startpos $endpos @@ NewArr (t, e) }


  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  | u=uop e=exp         { loc $startpos $endpos @@ Uop (u, e) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ Call (e,es) }

  | LPAREN e=exp RPAREN { e }

vdecl:
  | VAR id=IDENT EQ init=exp { (id, init) }

vdecls:
  | vs=separated_list(COMMA, vdecl) { vs }

stmt:
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCall(e, es) }
  | ifs=if_stmt         { ifs }
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  | FOR LPAREN vs=vdecls SEMI e=exp SEMI s=stmt RPAREN b=block
                        { loc $startpos $endpos @@ For(vs, Some e, Some s, b) }
  | FOR LPAREN vs=vdecls SEMI SEMI s=stmt RPAREN b=block
                        { loc $startpos $endpos @@ For(vs, None, Some s, b) }
  | FOR LPAREN vs=vdecls SEMI e=exp SEMI RPAREN b=block
                        { loc $startpos $endpos @@ For(vs, Some e, None, b) }
  | FOR LPAREN vs=vdecls SEMI SEMI RPAREN b=block
                        { loc $startpos $endpos @@ For(vs, None, None, b) }
  | WHILE LPAREN e=exp RPAREN b=block
                        { loc $startpos $endpos @@ While(e, b) }

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)       { [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { [ ifs ] }
