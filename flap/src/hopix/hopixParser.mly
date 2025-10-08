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

program: EOF
{
   []
}

%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
