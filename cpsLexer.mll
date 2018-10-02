{
open CpsParser;;

let line_count = ref 1

let linc n = line_count := (!line_count + n)

}

(* You can assign names to commonly-used regular expressions in this part
   of the code, to save the trouble of re-typing them each time they are used *)

let numeric = ['0' - '9']
let lowercase = ['a' - 'z']
let alpha = ['a' - 'z' 'A' - 'Z' ]
let letter =['a' - 'z' 'A' - 'Z' '_']

let id_char = numeric | letter | "'" | "_"

rule ftoken = parse
  | [' ' '\t'] { ftoken lexbuf }
  | ['\n']     { linc 1; ftoken lexbuf }  (* skip over whitespace *)
  | eof        { EOF }
  | numeric+ as s                      { INT s }
  | ((numeric+)'.'(numeric+)) as s      { REAL s }
  | "+"       { PLUS  }
  | "-"       { MINUS  }
  | "*"       { TIMES  }
  | "/"       { DIV  }
  | "mod"     { MOD  }
  | "+."      { DPLUS  }
  | "-."      { DMINUS  }
  | "*."      { DTIMES  }
  | "/."      { DDIV  }
  | "<"       { LT  }
  | ">"       { GT  }
  | "<="      { LEQ  }
  | ">="      { GEQ  }
  | "="       { EQUALS  }
  | "undefined" {UNDEF}
  | "("       { LPAREN  }
  | ")"       { RPAREN  }
  | "{"       {LBRACE}
  | "}"       {RBRACE}
  | ","       { COMMA  }
  | "->"      { LEADSTO}
  | "=>"      {INFER}
  | "fun"     {FUN}
  | "let"     { LET  }
  | "in"      { IN  }
  | "if"      { IF  }
  | "then"    { THEN  }
  | "else"    { ELSE  }
  | "|"       { PIPE  }
  | "match"   {MATCH}
  | "with"    { WITH }
  | "true"    { BOOL "true" }
  | "false"   { BOOL "false" }
  | "[["      {BLBR}
  | "]]"      {BRBR}
  | "["       {LBR}
  | "]"       {RBR}
  | "_"       {UNDER}
  | "by"      {BY}
  | "const"   {CONST}
  | "var"     {VAR}
  | "unaryrule"   {UNARYRULE}
  | "oprule"  {OPRULE}
  | "apprule"     {APPRULE}
  | "funrule"  {FUNRULE}
  | "letrule"  {LETRULE}
  | "ifelse"   {IFRULE}
  | "matchrule" {MATCHRULE}
  | (alpha (id_char*)) as s { IDENT ("$"^s) }
  | _           { ERROR ("mis-spelling allowed symbols or constants in line "^(string_of_int !line_count)^".") }

(* do not modify this function: *)
{
let lextest s = ftoken (Lexing.from_string s)

 }
