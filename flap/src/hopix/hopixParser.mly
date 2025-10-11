%{ (* -*- tuareg -*- *)

  open HopixAST
  open Position


%}

//  Avec type
%token <int> INT
%token <string> ID DATAID TVAR CHAR STR

// Les keywords
%token LET FUN AND IF MATCH THEN ELSE WHILE DO UNTIL FOR FROM TO TYPE EXTERN REF

// Les Symboles
%token LANGLE RANGLE COMMA DOT COLON SEMICOLON EXCLAMATION ANTISLASH PIPE CONJONCTION ARROW
%token LPAREN RPAREN RCURLYB LCURLYB RSQUAREB LSQUAREB UNDERSCORE

// Les opérations
%token AFFECTATION PLUS MINUS TIMES DIV EQUAL LOGAND LOGOR EQUALITY LESS_OR_EQ GREATER_OR_EQ LESS GREATER

%token EOF

%start<HopixAST.t> program

%%

(*
Une séquence entre crochets est optionnelle, comme `[ ref ]`.
Une séquence entre accolades se répète zéro fois ou plus, comme `( arg { , arg } )`.

p ::= { definition }                          Programme

definition ::= 
             | type type_con [ < type_variable { , type_variable } > ] [ = tdefinition ]   Définition de type
             | extern var_id : type_scheme                                                Valeurs externes
             | vdefinition                                                                Définition de valeur(s)

tdefinition ::= 
              | [ | ] constr_id [ ( type { , type } ) ]  { | constr_id [ ( type { , type } ) ] }         Type somme
              | { label_id : type { , label_id : type } }       Type produit étiqueté

vdefinition ::= 
              | let var_id [ : type_scheme ] = expr              Valeur simple
              | fun fundef { and fundef }                        Fonction(s)

fundef ::= [ : type_scheme ] var_id pattern = expr           

type ::= 
       | type_con [ < type { , type } > ]                        Application d’un constructeur de type
       | type -> type                                            Fonctions
       | type * type { * type }                                  N-uplets (N > 1)
       | type_variable                                           Variables de type
       | ( type )                                                Type entre parenthèses

type_scheme ::= [ [ type_variable { , type_variable } ] ] type

type ::= type_con [ < type { , type } > ]                        Application d’un constructeur de type
       | type -> type                                            Fonctions
       | type * type { * type }                                  N-uplets (N > 1)
       | type_variable                                           Variables de type
       | ( type )                                                Type entre parenthèses

type_scheme ::= [ [ type_variable { , type_variable } ] ] type

expr ::=
       | int                                                Entier positif
       | char                                               Caractère
       | string                                             Chaîne de caractères
       | var_id [ < [ type { , type } ] > ]                 Variable
       | constr_id [ < [ type { , type } ] > ] [ ( expr { , expr } ) ]  Construction d’une donnée
       | ( )                                                Construction d’un 0-uplet
       | ( expr , expr { , expr } )                         Construction d’un n-uplet (n > 1)
       | { label_id = expr { , label_id = expr } } [ < [ type { , type } ] > ]  Enregistrement
       | expr . label_id [ < [ type { , type } ] > ]        Projection d’un champ
       | expr ; expr                                        Séquencement
       | vdefinition ; expr                                 Définition locale
       | \ pattern -> expr                                  Fonction anonyme
       | expr expr                                          Application
       | expr binop expr                                    Application infixe
       | match ( expr ) { branches }                        Analyse de motifs
       | if ( expr ) then { expr } [ else { expr } ]        Conditionnelle
       | ref expr                                           Allocation
       | expr := expr                                       Affectation
       | ! expr                                             Lecture
       | while ( expr ) { expr }                            Boucle non bornée
       | do { expr } until ( expr )                         Boucle non bornée et non vide
       | for var_id from ( expr ) to ( expr ) { expr }      Boucle bornée
       | ( expr )                                           Parenthésage
       | ( expr : type )                                    Annotation de type

binop ::= + | - | * | / | && | || | =? | <=? | >=? | <? | >?      Opérateurs binaires
branches ::= [ | ] branch { | branch }                            Liste de cas
branch ::= pattern -> expr                                        Cas d’analyse

pattern ::=
          | var_id                                                Motif universel liant
          | _                                                     Motif universel non liant
          | ( [ pattern { , pattern } ] )                         N-uplets ou parenthésage
          | pattern : type                                        Annotation de type
          | int                                                   Entier
          | char                                                  Caractère
          | string                                                Chaîne de caractères
          | constr_id [ < [ type { , type } ] > ] [ ( pattern { , pattern } ) ]  Valeurs étiquetées
          | { label_id = pattern { , label_id = pattern } } [ < [ type { , type } ] > ]  Enregistrement
          | pattern | pattern                                     Disjonction
          | pattern & pattern                                     Conjonction

*)

program: defs=definition* EOF { defs }

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
    { DeclareExtern (id, ts) }
  // vdefinition
  | vd=vdefinition
    {DefineValue vd }

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
  // type_con [ < type { , type } > ]  
  | tcon=ID typs=loption(delimited(LANGLE, separated_nonempty_list(COMMA, located(typ)), RANGLE))
    { TyCon (TCon tcon, typs) }
  // type -> type 
  | t1=located(typ) ARROW t2=located(typ)
    { TyArrow (t1, t2) }
  // type * type { * type }
  | t1=located(typ) TIMES t2=located(typ) ts=preceded(TIMES, located(typ))*
    { TyTuple (t1 :: t2 :: ts) }
  // type_variable
  | tv=TVAR
    { TyVar (TId tv) }
  // ( type )
  | LPAREN t=located(typ) RPAREN
    { t }

sum_type_case:
  // constr_id [ ( type { , type } ) ] 
 | constr=located(DATAID) typs=option(delimited(LPAREN, separated_nonempty_list(COMMA, located(typ)),RPAREN)) {(Position.map (fun s -> KId s) constr, typs )}

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
    }




type_scheme: 
  // [ [ type_variable { , type_variable } ] ] type
  | typvars=loption(delimited(LSQUAREB, separated_nonempty_list(COMMA, type_variable), RSQUAREB)) ty=located(typ)
  {
    ForallTy (typvars, ty)
  }

type_variable:
  | tv=located(TVAR) { Position.map (fun s -> TId s) tv}

pattern:{}

expr: 
  | n=located(INT) { Literal (LInt (Mint.of_int n))}
  | c=located(CHAR) { Literal (LChar c)}
  | s=located(STR) { Literal (LString s)}

  | varId=located(ID)     tys=option(delimited(LANGLE,separated_nonempty_list(COMMA, located(typ)) ,RANGLE))     {Variable (Position.map (fun s -> Id s) varId ,tys )}

  |constr=located(DATAID) tys=option(delimited(LANGLE,separated_nonempty_list(COMMA, located(typ)) ,RANGLE)) 
    exps=(delimited(LPAREN,separated_list(COMMA, located(expr)),RPAREN)) 
    { Tagged (Position.map (fun s-> KId s) constr,tys,exps)}

  | LPAREN RPAREN {Tuple []}

  | LPAREN e1=located(expr) COMMA e2=located(expr) es=preceded(COMMA, located(expr))* RPAREN {Tuple (e1 :: e2 :: es)}

  // gère les () (e) (e,e...) en même temps
  | LPAREN exprs=separated_list(COMMA, located(expr)) RPAREN {
    match exprs with 
      | [] -> Tuple []
      | [e] -> Postion.value e
      | _ -> Tupls exprs

  }
  // TODO finir le Record et le reste des expr et les pattern
  |LCURLYB RCURLYB tys=option(delimited(LANGLE,separated_nonempty_list(COMMA, located(typ)) ,RANGLE)) 

%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
