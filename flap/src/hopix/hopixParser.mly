%{ (* -*- tuareg -*- *)

  open HopixAST
  open Position

%}

%token <Mint.t> INT
%token <string> ID DATAID TVAR STR
%token <char> CHAR

// Les keywords
%token LET FUN AND IF MATCH THEN ELSE WHILE DO UNTIL FOR FROM TO TYPE EXTERN REF

// Les Symboles
%token LANGLE RANGLE COMMA DOT COLON SEMICOLON EXCLAMATION ANTISLASH PIPE CONJONCTION ARROW
%token LPAREN RPAREN RCURLYB LCURLYB RSQUAREB LSQUAREB UNDERSCORE

// Les opérations
%token AFFECTATION PLUS MINUS TIMES DIV EQUAL LOGAND LOGOR EQUALITY LESS_OR_EQ GREATER_OR_EQ LESS GREATER

%token EOF

%start<HopixAST.t> program

%nonassoc LETSEQ
%right SEMICOLON
%right ARROW
%right AFFECTATION
%left LOGOR
%left LOGAND
%left EQUALITY LESS_OR_EQ GREATER_OR_EQ LESS GREATER
%left PLUS MINUS
%left TIMES DIV
%nonassoc REF EXCLAMATION
%nonassoc CONSTR_NOARG
%right LPAREN

%%


program: defs=located(definition)* EOF { defs }

definition:
  // type type_con [ < type_variable { , type_variable } > ] [ = tdefinition ] 
  | TYPE tcon=located(DATAID) tvars=type_params? td=type_definition? 
    { 
      DefineType (
        Position.map (fun s -> TCon s) tcon ,
        List.map (Position.map (fun s -> TId s)) (Option.value ~default:[] tvars), 
        Option.value ~default:Abstract td)
    }
  // extern var_id : type_scheme
  | EXTERN id=located(ID) COLON ts=located(type_scheme)
    { DeclareExtern (Position.map (fun id -> Id id) id, ts) }
  // vdefinition
  | vd=vdefinition
    {DefineValue vd}

type_params:
  // < type_variable { , type_variable } >
  | LANGLE tvs=separated_list(COMMA, located(TVAR)) RANGLE { tvs }

type_definition:
  | EQUAL td=tdefinition { td }

tdefinition:
  // [ | ] constr_id [ ( type { , type } ) ]  { | constr_id [ ( type { , type } ) ] }
  | PIPE? cases=separated_nonempty_list(PIPE, sum_type_case)
    { DefineSumType cases }
  // { label_id : type { , label_id : type } } 
  | LCURLYB fields=separated_nonempty_list(COMMA, record_field) RCURLYB
    { DefineRecordType fields }

typ:
  // typ -> typ
  | t=located(typ_atom) ARROW t2=located(typ)
    { TyArrow (t, t2) }
  // type * type {* type}
  | t=located(typ_tuple)
    { Position.value t }
  // ceux qu'on coupe pas
  | t=typ_atom
    { t }

typ_in_pattern:
  | tcon=ID typs=loption(delimited(LANGLE, separated_nonempty_list(COMMA, located(typ)), RANGLE))
    { TyCon (TCon tcon, typs) }  
  | tv=TVAR
    { TyVar (TId tv) }  
  | LPAREN t=typ RPAREN { t }  
typ_tuple:
    // au moins 2
  | t1=located(typ_atom) TIMES t2=located(typ_atom) ts=tuple_rest
    { TyTuple (t1 :: t2 :: ts) }

// Modifié pour éviter les conflits shift/reduce avec TIMES
tuple_rest:
  | /* empty */ { [] }
  | TIMES t=located(typ_atom) ts=tuple_rest { t :: ts }

typ_atom:
  // type_con [ < type { , type } > ]
  | tcon=ID typs=loption(delimited(LANGLE, separated_nonempty_list(COMMA, located(typ)), RANGLE))
    { TyCon (TCon tcon, typs) }
  // type_variable
  | tv=TVAR
    { TyVar (TId tv) }
  | LPAREN t=located(typ) RPAREN { Position.value t } 

sum_type_case:
  // constr_id [ ( type { , type } ) ] 
 | constr=located(DATAID) typs=delimited(LPAREN, separated_nonempty_list(COMMA, located(typ)),RPAREN){(Position.map (fun s -> KId s) constr, typs )}

record_field:
  // label_id : type
  | id=located(ID) COLON ty=located(typ)
    { (Position.map (fun s -> LId s ) id, ty) }

vdefinition: 
  // let var_id [ : type_scheme ]= expr 
  | LET id=located(ID) ts=option(preceded(COLON, located(type_scheme))) EQUAL e=located(expr) 
    { SimpleValue (Position.map (fun s -> Id s) id , ts, e) } 
  // fun fundef { and fundef } 
  | FUN fds=separated_nonempty_list(AND, fundef) 
    { RecFunctions fds } 

fundef: 
  // [ : type_scheme ] var_id pattern = expr
  | ts=option(preceded(COLON, located(type_scheme))) id=located(ID) pat=located(pattern) EQUAL e=located(expr)
    { 
      (Position.map (fun s -> Id s ) id, ts, FunctionDefinition (pat, e))
    } %prec LETSEQ




type_scheme: 
  // [ [ type_variable { , type_variable } ] ] type
  | typvars=loption(delimited(LSQUAREB, separated_nonempty_list(COMMA, type_variable), RSQUAREB)) ty=located(typ)
  {
    ForallTy (typvars, ty)
  }

type_variable:
  | tv=located(TVAR) { Position.map (fun s -> TId s) tv}

pattern:
  // division des or et and
  | p=pattern_or { p }

pattern_or:
  | p1=located(pattern_and) PIPE p2=located(pattern_or)
    { 
      match Position.value p2 with
      | POr ps -> POr (p1 :: ps)
      | _ -> POr [p1; p2]
    }
  | p=pattern_and { p }

pattern_and:
  | p1=located(pattern_base) CONJONCTION p2=located(pattern_and)
    {
      match Position.value p2 with
      | PAnd ps -> PAnd (p1 :: ps)
      | _ -> PAnd [p1; p2]
    }
  | p=pattern_base { p }

pattern_base:
  // dans base les patterns "atomiques"
  | var=located(ID) {PVariable (Position.map (fun e -> Id e) var)}
  | UNDERSCORE {PWildcard}
  | LPAREN pats=separated_list(COMMA, located(pattern)) RPAREN {
    match pats with
    | [] -> PTuple []
    | [p] -> Position.value p 
    | _ -> PTuple pats
  }
  | p=located(pattern_base) COLON ty=located(typ_in_pattern) {
    PTypeAnnotation (p,ty)
  }

  |n=located(INT) {PLiteral (Position.map (fun n -> LInt n) n )}

  |c=located(CHAR) {PLiteral (Position.map (fun c -> LChar c) c)}

  | str=located(STR) {PLiteral (Position.map (fun str -> LString str) str)}
  | constr=located(DATAID) types=option(delimited(LANGLE, separated_list(COMMA, located(typ)),RANGLE)) pats=loption(delimited(LPAREN, separated_nonempty_list(COMMA, located(pattern)),RPAREN)) {
    PTaggedValue (Position.map (fun c -> KId c) constr, types, pats)
  }
  | LCURLYB fields=separated_nonempty_list(COMMA, record_field_pattern) RCURLYB tys=option(delimited(LANGLE,separated_nonempty_list(COMMA, located(typ)) ,RANGLE)) { PRecord (fields,tys)}  

record_field_pattern:
  | label=located(ID) EQUAL e=located(pattern) {Position.map (fun s -> LId s) label ,e}

expr:
  | e=simple_expr { e }
  | LET id=located(ID) ts=option(preceded(COLON, located(type_scheme))) EQUAL e1=located(expr) SEMICOLON e2=located(expr)
    { Define (SimpleValue (Position.map (fun s -> Id s) id, ts, e1), e2) } %prec LETSEQ
  | FUN fds=separated_nonempty_list(AND, fundef) SEMICOLON e=located(expr)
    { Define (RecFunctions fds, e) } %prec LETSEQ
  | e1=located(expr) SEMICOLON e2=located(expr)
    {
      match Position.value e2 with
      | Sequence es -> Sequence (e1 :: es)
      | _ -> Sequence [e1; e2]
    }
  | ANTISLASH p=located(pattern) ARROW e=located(expr)
    { Fun (FunctionDefinition (p, e)) }
  | MATCH LPAREN e=located(expr) RPAREN LCURLYB b=branches RCURLYB
    { Case (e, b) }
  | IF LPAREN cond=located(expr) RPAREN THEN LCURLYB trueb=located(expr) RCURLYB falseb=option(preceded(ELSE, delimited(LCURLYB, located(expr), RCURLYB))) {
    match falseb with
    | None -> IfThenElse (cond, trueb, Position.with_pos (Position.position trueb) (Tuple []))
    | Some falseb -> IfThenElse (cond, trueb, falseb)
  }
  | WHILE LPAREN cond=located(expr) RPAREN LCURLYB body=located(expr) RCURLYB
    { While (cond, body) }
  | DO LCURLYB body=located(expr) RCURLYB UNTIL LPAREN cond=located(expr) RPAREN {
    let while_expr = Position.with_pos (Position.position cond) (While (cond, body)) in
    Sequence [body; while_expr]
  }
  | FOR var=located(ID) FROM LPAREN borneinf=located(expr) RPAREN TO LPAREN bornesup=located(expr) RPAREN LCURLYB body=located(expr) RCURLYB
    { For (Position.map (fun s -> Id s) var, borneinf, bornesup, body) }
  | LPAREN e=located(expr) COLON t=located(typ) RPAREN
    { TypeAnnotation (e, t) }
  | lhs=located(simple_expr) AFFECTATION rhs=located(expr)
    { Assign (lhs, rhs) }
  | left=located(expr) op=located(binop) right=located(expr)
    {
    

      let op_var =
        Position.with_pos (Position.position op)
          (Variable (op, None))
      in
      let applied_left =
        Position.with_pos (Position.position left)
          (Apply (op_var, left))
      in
        (Apply (applied_left, right))
    
  }
    
  | REF e=located(expr)
    { Ref e } 

simple_expr:
  | a=atomic_expr { a }
  
  | EXCLAMATION e=located(atomic_expr)
    { Read e }
  | f=located(simple_expr) arg=located(atomic_expr)
    { Apply (f, arg) }
  | f=located(simple_expr) DOT label=located(ID) tys=option(delimited(LANGLE, separated_nonempty_list(COMMA, located(typ)), RANGLE))
    { Field (f, Position.map (fun s -> LId s) label, tys) }

atomic_expr:
  | n=located(INT) { Literal (Position.map (fun n -> LInt n) n) }
  | c=located(CHAR) { Literal (Position.map (fun c -> LChar c) c) }
  | str=located(STR) { Literal (Position.map (fun str -> LString str) str) }
  | varId=located(ID) tys=option(delimited(LANGLE, separated_nonempty_list(COMMA, located(typ)), RANGLE))
    { Variable (Position.map (fun s -> Id s) varId, tys) }
  | constr=located(DATAID) tys=option(delimited(LANGLE, separated_nonempty_list(COMMA, located(typ)), RANGLE)) LPAREN es=separated_list(COMMA, located(expr)) RPAREN
    { Tagged (Position.map (fun s -> KId s) constr, tys, es) }
  | constr=located(DATAID) tys=option(delimited(LANGLE, separated_nonempty_list(COMMA, located(typ)), RANGLE))
    { Tagged (Position.map (fun s -> KId s) constr, tys, []) } %prec CONSTR_NOARG
  | LPAREN RPAREN { Tuple [] }
  | LPAREN e1=located(expr) COMMA e2=located(expr) es=preceded(COMMA, located(expr))* RPAREN
    { Tuple (e1 :: e2 :: es) }
  | LPAREN e=located(expr) RPAREN { Position.value e }
  | LCURLYB fields=separated_nonempty_list(COMMA, record_field_expr) RCURLYB tys=option(delimited(LANGLE, separated_nonempty_list(COMMA, located(typ)), RANGLE))
    { Record (fields, tys) }

%inline binop:
  | PLUS { Id "`+`" }
  | MINUS { Id "`-`" }
  | TIMES { Id "`*`" }
  | DIV { Id "`/`" }
  | LOGAND { Id "`&&`" }
  | LOGOR { Id "`||`" }
  | EQUALITY { Id "`=?`" }
  | LESS_OR_EQ { Id "`<=?`" }
  | GREATER_OR_EQ { Id "`>=?`" }
  | LESS { Id "`<?`" }
  | GREATER { Id "`>?`"  }

branche:
  | p=located(pattern) ARROW e=located(expr)
  {Position.with_pos (Position.position p) (Branch (p,e))}

branches:
  | PIPE? b=branche bs=preceded(PIPE,branche)* { b::bs }

record_field_expr:
  | label=located(ID) EQUAL e=located(expr) {Position.map (fun s -> LId s) label ,e}

%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
