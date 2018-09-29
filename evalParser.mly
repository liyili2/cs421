/* Use the expression datatype defined in mp8common.ml: */
%{
(* add any extra code here *)
%}

/* Define the tokens of the language: */
%token <string> IDENT INT REAL BOOL ERROR
%token EOF PLUS MINUS TIMES DIV MOD DPLUS DMINUS DTIMES DDIV LT GT LEQ GEQ EQUALS
       UNDEF LPAREN RPAREN COMMA LEADSTO INFER FUN LET IN IF THEN ELSE PIPE EVAL APP LBRACE RBRACE
       MATCH WITH OP BY CONST VAR TUPLE OPRULE APPFIRST FUNRULE LETRULE APPFINAL IFRULE MATCHRULE

%left COMMA
%left LT GT LEQ GEQ EQUALS
%left PLUS MINUS DPLUS DMINUS MOD   
%left TIMES DIV DTIMES DDIV
%nonassoc OP


/* Define the "goal" nonterminal of the grammar: */
%start main
%type < string > main

%%

main: 
    toplevel {"program "^$1}

toplevel:
    expression INFER expression BY rulename {"'infer("^$1^", "^$3^", "^ $5^")"}
  | expression INFER UNDEF {"'infer("^$1^", 'undef(.KList), 'undef(.KList))"}
  | expression INFER expression BY rulename main {"'con('infer("^$1^", "^$3^", "^ $5^"), "^$6^")"}
  | expression INFER UNDEF main {"'con('infer("^$1^", 'undef(.KList), 'undef(.KList)), "^$4^")"}

rulename:
    CONST {"'const(.KList)"}
  | VAR {"'var(.KList)"}
  | TUPLE {"'tuple(.KList)"}
  | OPRULE {"'oprule(.KList)"}
  | APPFIRST {"'appfirst(.KList)"}
  | FUNRULE {"'funrule(.KList)"}
  | LETRULE {"'letrule(.KList)"}
  | APPFINAL {"'appfinal(.KList)"}
  | IFRULE {"'ifrule(.KList)"}
  | MATCHRULE {"'matchrule(.KList)"}

expression:
   expr {$1}
   | MATCH appexpr WITH pats {"'match("^$2^", "^$4^")"}

expr:
     subexpr {$1}
   | FUN var LEADSTO expr {"'fun("^$2^", "^$4^")"}
   | LET vartuple EQUALS expression IN expr {"'let("^$2^", "^$4^", "^$6^")"}
   | IF appexpr THEN expr ELSE expr {"'if("^$2^", "^$4^", "^$6^")"}

vartuple:
    var {$1}
   | LPAREN vartupleaux RPAREN {$2}

vartupleaux:
     var {$1}
   | var COMMA vartupleaux {"'varCon("^$1^")"}

tupleaux:
   LPAREN tupleauxa RPAREN {$2}

tupleauxa:
    expression {$1}
  | expression COMMA tupleauxa {"'tupleCon("^$1^","^$3^")"}

pats:
    pat {$1}
  | pat PIPE pats {"'patCon("^$1^", "^$3^")"}

pat:
   patexpr LEADSTO expr {"'pat("^$1^", "^$3^")"}


appexpr:
   subexpr {$1}
  | appexpr subexpr {"'appop("^$1^", "^$2^")"}
   
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
     tupleaux {$1}
   | var {$1}
   | const {$1}
   | EVAL LPAREN expression COMMA env RPAREN {"'eval("^$3^", "^$5^")"}
   | APP LPAREN expression COMMA expression RPAREN {"'app("^$3^", "^$5^")"}

patexpr:
     var {$1}
   | LPAREN pattuple RPAREN {$2}
   | const {$1}

pattuple:
     patexpr {$1}
   | patexpr COMMA pattuple {"'patCon("^$1^", "^$3^")"}

const:
     INT {"'"^$1^"(.KList)"}
   | REAL {"'"^$1^"(.KList)"}
   | BOOL {"'"^$1^"(.KList)"}

var:
    IDENT {$1^"(.KList)"}

env: 
     LBRACE RBRACE {".Map"}
  | LBRACE envaux RBRACE {$2}

envaux:
   mapitem {$1}
 | mapitem COMMA envaux {"MapCon("^$1^", "^$3^")"}

mapitem:
   var LEADSTO value {"MapItem("^$1^", "^$3^")"}

value:
    const {$1}
  | LPAREN valuetuple RPAREN {$2}
  | closure {$1}

valuetuple:
    value {$1}
  | value COMMA valuetuple {"'valueCon("^$1^", "^$3^")"}

closure:
   LT varexpr COMMA env GT {"'closure("^$2^", "^$4^")"}

varexpr:
   var LEADSTO expression {$1^", "^$3}


