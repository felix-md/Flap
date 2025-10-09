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
  | TYPE tcon=located(DATAID) tvars=type_params? td=type_definition? 
    { 
      let td = match td with 
        | None -> None 
        | Some td -> Some td
      in
      DefineType (tcon, Option.value ~default:[] tvars, td)
    }
  | EXTERN id=located(ID) COLON ts=located(type_scheme)
    { DeclareExtern (id, ts) }
  | vd=vdefinition
    { vd }

type_params:
  | LANGLE tvs=separated_list(COMMA, located(TVAR)) RANGLE { tvs }

type_definition:
  | EQUAL td=tdefinition { td }

tdefinition:
  | PIPE? cases=separated_nonempty_list(PIPE, sum_type_case)
    { DefineSumType cases }
  | LCURLYB fields=separated_nonempty_list(COMMA, record_field) RCURLYB
    { DefineRecordType fields }

sum_type_case:
  | id=located(DATAID) tys=type_params?
    { (id, Option.value ~default:[] tys) }

record_field:
  | id=located(ID) COLON ty=located(typ)
    { (id, ty) }

vdefinition: {}

fundef: {}

typ:
  | tcon=DATAID tys=type_params?
    { TyCon (tcon, Option.value ~default:[] tys) }
  | t1=typ ARROW t2=typ
    { TyArrow (t1, t2) }
  | t1=typ TIMES t2=typ ts=preceded(TIMES, typ)*
    { TyTuple (t1 :: t2 :: ts) }
  | tv=TVAR
    { TyVar tv }
  | LPAREN t=typ RPAREN
    { t }

type_scheme: {}

pattern:{}

expr: {}

%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
