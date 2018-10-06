/* Use the expression datatype defined in mp8common.ml: */
%{
(* add any extra code here *)
%}

/* Define the tokens of the language: */
%token <string> IDENT INT REAL BOOL ERROR 
%token EOF PLUS MINUS TIMES DIV MOD DPLUS DMINUS DTIMES DDIV LT GT LEQ GEQ EQUALS
       UNDEF LPAREN RPAREN COMMA LEADSTO INFER FUN LET IN IF THEN ELSE PIPE EVAL APP LBRACE RBRACE
       MATCH WITH BY CONST VAR OPRULE FUNRULE LETRULE IFRULE MATCHRULE
       UNARYRULE APPRULE UNDER LBR RBR BLBR BRBR FN BigFun BigIf BigThen BigElse

%left COMMA
%left LT GT LEQ GEQ EQUALS
%left PLUS MINUS DPLUS DMINUS MOD   
%left TIMES DIV DTIMES DDIV


/* Define the "goal" nonterminal of the grammar: */
%start main
%type < string > main

%%

main: 
    expression {"program 'eval('0(.KList), "^$1^", .List)"}
  | expression INFER toplevel {"program 'eval('0(.KList), "^$1^", "^$3^")"}

toplevel:
    expression BY rulename {"ListItem("^$1^", "^$3^")"}
  | UNDEF {"ListItem('undef(.KList), 'undef(.KList))"}
  | expression BY rulename toplevel {"ListCon(ListItem("^$1^", "^$3^"), "^$4^")"}
  | UNDEF toplevel {"ListCon(ListItem('undef(.KList), 'undef(.KList)), "^$2^")"}

rulename:
    CONST {"'const(.KList)"}
  | VAR {"'var(.KList)"}
  | OPRULE {"'oprule(.KList)"}
  | APPRULE {"'apprule(.KList)"}
  | FUNRULE {"'funrule(.KList)"}
  | LETRULE {"'letrule(.KList)"}
  | IFRULE {"'ifrule(.KList)"}
  | MATCHRULE {"'matchrule(.KList)"}
  | UNARYRULE {"'unaryrule(.KList)"}

expression:
   expr {$1}
   | MATCH appexpr WITH pats {"'match("^$2^", "^$4^")"}

expr:
     appexpr {$1}
   | FN var LEADSTO expr {"'fn("^$2^", "^$4^")"}
   | BigFun var var LEADSTO expr {"'bigFun("^$2^", "^$3^", "^$5^")"}
   | FUN var LEADSTO expr {"'fun("^$2^", "^$4^")"}
   | LET var EQUALS expression IN expr {"'let("^$2^", "^$4^", "^$6^")"}
   | IF appexpr THEN expr ELSE expr {"'if("^$2^", "^$4^", "^$6^")"}
   | BigIf appexpr BigThen expr BigElse expr {"'bigIf("^$2^", "^$4^", "^$6^")"}

pats:
    pat {$1}
  | pat PIPE pats {"'patCon("^$1^", "^$3^")"}

pat:
   atomicexpr LEADSTO expr {"'pat("^$1^", "^$3^")"}


appexpr:
   subexpr {$1}
  | appexpr subexpr {"'app("^$1^", "^$2^")"}
   
subexpr:
     unaryexpr {$1}
   | subexpr PLUS subexpr {"'plus("^$1^", "^$3^")"}
   | subexpr MINUS subexpr {"'minus("^$1^", "^$3^")"}
   | subexpr TIMES subexpr {"'times("^$1^", "^$3^")"}
   | subexpr DIV subexpr {"'div("^$1^", "^$3^")"}
   | subexpr MOD subexpr {"'mod("^$1^", "^$3^")"}
   | subexpr DPLUS subexpr {"'dplus("^$1^", "^$3^")"}
   | subexpr DMINUS subexpr {"'dminus("^$1^", "^$3^")"}
   | subexpr DTIMES subexpr {"'dtimes("^$1^", "^$3^")"}
   | subexpr DDIV subexpr {"'ddiv("^$1^", "^$3^")"}
   | subexpr LT subexpr {"'less("^$1^", "^$3^")"}
   | subexpr GT subexpr {"'greater("^$1^", "^$3^")"}
   | subexpr LEQ subexpr {"'leq("^$1^", "^$3^")"}
   | subexpr GEQ subexpr {"'geq("^$1^", "^$3^")"}
   | subexpr EQUALS subexpr {"'equal("^$1^", "^$3^")"}

unaryexpr:
     atomicexpr {$1}

atomicexpr:
     patlist {$1}
   | var {$1}
   | const {$1}
   | BLBR expression BRBR UNDER LBRACE expression RBRACE
              {"'trans("^$2^", "^$6^")"}
   | LPAREN expression RPAREN {$2}

patlist:
  LBR pattuple RBR {$2}

pattuple:
     atomicexpr {"'listCon("^$1^", .Exps)"}
   | atomicexpr COMMA pattuple {"'listCon("^$1^", "^$3^")"}

const:
     INT {"'"^$1^"(.KList)"}
   | REAL {"'"^$1^"(.KList)"}
   | BOOL {"'"^$1^"(.KList)"}

var:
    IDENT {$1^"(.KList)"}


