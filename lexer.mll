{

open K;;
open K;;
open Parser;;
let rec parseNat n = if n < 0 then raise (Failure "Strict Num cannot be less than zero") 
                        else if n = 0 then Zero_nat else Suc (parseNat (n - 1));;

let rec parseBits n = if n = 1 then One else if n = 2 then Bit0 (One)
            else if n mod 2 = 0 then Bit0 (parseBits (n / 2))
                  else Bit1 (parseBits (n / 2));;

let parseCharNum n = if n = 0 then Zero_char else Char (parseBits n);;

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;


let parseChar c = parseCharNum (int_of_char c);;

let parseString s = List.map (fun c -> parseChar c) (explode s);;

let dealwithSort s = match s with "K" -> K | "Bool" -> Bool | "KItem" -> KItem
         | "KLabel" -> KLabel | "KResult" -> KResult
    | "KList" -> KList | "List" -> List | "Set" -> Set
    | "Map" -> Map | "Bag" -> Bag | "Id" -> Id | "String" -> String
    | "Int" -> Int | "Float" -> Float | _ -> OtherSort (parseString s);;

}

(* You can assign names to commonly-used regular expressions in this part
   of the code, to save the trouble of re-typing them each time they are used *)

let numeric = ['0' - '9']
let lowercase = ['a' - 'z']
let uppercase = ['A' - 'Z']
let alpha = ['a' - 'z' 'A' - 'Z' ]
let letter = numeric | alpha | ['_']
let special = ['`' '~' '!' '@' '#' '%' '^' '&' '*' '-' '=' '+' '[' '{' ']' '}' '|' ';' ':' '\'' ',' '<' '.' '>' '/' '?']

let xmlid = numeric | alpha | "_" | "\'"
let id_char = numeric | letter | "_" | special
let open_comment = "/*"
let close_comment = "*/"
let whitespace = [' ' '\t' '\n']

let escapednum = '0' numeric numeric | '1' numeric numeric | '2' ['0' - '4'] numeric | "25" ['0' -'5']

rule token = parse
  | [' ' '\t'] { token lexbuf }
  | ['\n']     { token lexbuf }  (* skip over whitespace *)
  | eof        { EOF }
  | "rule"       { ARule }
  | "configuration" {AConfiguration}
  | "program"  {AProgram}
  | "syntax" {ASyntax}
  | "requires" {Requires}
  | "\""       {string "" lexbuf}
  | "::="  { Assign }
  | "|"    {Bar}
  | ">"    {Gt}
  | "["    {syntaxattr [] lexbuf}
  | ":"    {TypeCon}
  | "." (uppercase xmlid* as s) {EmptyLabel s}
  | "SetCon" {ASetCon}
  | "SetItem" {ASetItem}
  | "ListCon" {AListCon}
  | "ListItem" {AListItem}
  | "MapCon"  {AMapCon}
  | "MapItem"     {AMapItem}
  | "=>"      {ARewrite}
  | "MapUpdate"      {AMapUpdate}
  | (uppercase xmlid*) as s {dealwithSort s}
  | "Token" whitespace* "{" {dealwithtoken [] lexbuf}
  | "{" {LBig}
  | "}" {RBig}
  | "$" (xmlid* as s) {Variable s}
  | "\'" (id_char+ as s) {LabelId s}
  | "("       { LPAREN  }
  | ")"       { RPAREN  }
  | "," {Dot}
  | ("//"([^'\n']*))   { token lexbuf }
  | "<" (alpha* as s) {dealWithBag s [] lexbuf}
  | "</" (alpha* as s) ">" {BagBack (s,[])}
  | "...</" (alpha* as s) ">" {BagBack (s,[DotDotDot])}
  | open_comment   { multiline_comment lexbuf }
  | _           { raise (Failure "Token Lexical error") }

and multiline_comment = parse
   close_comment   { token lexbuf }
  | eof    { raise (Failure "unterminated comment") }
  | _      { multiline_comment lexbuf }

and dealWithBag name features = parse
    [' ' '\t'] { dealWithBag name features lexbuf }
  | ['\n']     { dealWithBag name features lexbuf }
  | ">..." {BagWrap (name, (DotDotDot)::features)}
  | ">" {BagWrap (name, features)}
  | "multiplicity" whitespace* "=" whitespace* "\"*\""
                   {dealWithBag name ((Multiplicity Star)::features) lexbuf}
  | "multiplicity" whitespace* "=" whitespace* "\"?\""
                   {dealWithBag name ((Multiplicity Question)::features) lexbuf}
  | "stream" whitespace* "=" whitespace* "\"stdout\""
                   {dealWithBag name ((Stream Stdout)::features) lexbuf}
  | "multiplicity" whitespace* "=" whitespace* "\"stdin\""
                   {dealWithBag name ((Stream Stdout)::features) lexbuf}

and dealwithtoken tokens = parse
   "}" {AToken tokens}
  | "\\?" {dealwithtoken (tokens@[AChar (parseChar '?')]) lexbuf}
  | "\\_" {dealwithtoken (tokens@[AChar (parseChar '_')]) lexbuf}
  | "\\\\" {dealwithtoken (tokens@[AChar (parseChar '\\')]) lexbuf}
  | "\\\'" {dealwithtoken (tokens@[AChar (parseChar '\'')]) lexbuf}
  | "\\-"  {dealwithtoken (tokens@[AChar (parseChar '-')]) lexbuf}
  | "\\\"" {dealwithtoken (tokens@[AChar (parseChar '\"')]) lexbuf}
  | "[" {dealwithtoken (tokens@[LBr]) lexbuf}
  | "]" {dealwithtoken (tokens@[RBr]) lexbuf}
  | "-" {dealwithtoken (tokens@[To]) lexbuf}
  | "*" {dealwithtoken (tokens@[TheStar]) lexbuf}
  | "+" {dealwithtoken (tokens@[Plus]) lexbuf}
  | "?" {dealwithtoken (tokens@[OneOrMore]) lexbuf}
  | _ as c {dealwithtoken (tokens@[AChar (parseChar c)]) lexbuf}

and syntaxattr attrs = parse
  | [' ' '\t'] { syntaxattr attrs lexbuf }
  | ['\n']     { syntaxattr attrs lexbuf }  (* skip over whitespace *)
  | eof        { raise (Failure "Bad in syntax attributes.") }
  | "]" {Attr attrs}
  | "left" {syntaxattr (attrs@[Left]) lexbuf}
  | "right" {syntaxattr (attrs@[Right]) lexbuf}
  | "function" {syntaxattr (attrs@[Function]) lexbuf}
  | "seqstrict" {syntaxattr (attrs@[Seqstrict]) lexbuf}
  | "strict"  whitespace* "(" {syntaxattrnum attrs [] lexbuf}
  | "strict" {syntaxattr (attrs@[Strict []]) lexbuf}
  | "non-assoc" {syntaxattr (attrs@[NonAssoc]) lexbuf}
  | "token" {syntaxattr (attrs@[Tokena]) lexbuf}
  | "avoid" {syntaxattr (attrs@[Avoid]) lexbuf}
  | "bracket" {syntaxattr (attrs@[Bracket]) lexbuf}
  | "onlyLabel" {syntaxattr (attrs@[OnlyLabel]) lexbuf}
  | "klabel"  whitespace* "(" "\'" ([^'\"' ')']* as s) ")" {syntaxattr (attrs@[Klabel (parseString s)]) lexbuf}
  | "notInRules" {syntaxattr (attrs@[NotInRules]) lexbuf}
  | "latex" whitespace* "(" ([^',' ' ' '\t' ']' ')']+) ")" as s  {syntaxattr (attrs@[OtherSynAttr (parseString s)]) lexbuf}
  | "hook" whitespace* "(" ([^',' ' ' '\t' ']' ')']+) ")" as s {syntaxattr (attrs@[OtherSynAttr (parseString s)]) lexbuf}
  | "division" {syntaxattr (attrs@[OtherSynAttr (parseString "division")]) lexbuf}
  | "variable" {syntaxattr (attrs@[OtherSynAttr (parseString "variable")]) lexbuf}
  | "autoReject" {syntaxattr (attrs@[OtherSynAttr (parseString "autoReject")]) lexbuf}
  | "arith" {syntaxattr (attrs@[OtherSynAttr (parseString "arith")]) lexbuf}
  | "prefer" {syntaxattr (attrs@[OtherSynAttr (parseString "prefer")]) lexbuf}
  | "owise" {syntaxattr (attrs@[OtherSynAttr (parseString "owise")]) lexbuf}
  | "," {syntaxattr attrs lexbuf}

and syntaxattrnum attrs nums = parse
  (((['1' - '9'])(numeric*)) as s) whitespace* "," { syntaxattrnum attrs (nums@[parseNat (int_of_string s)]) lexbuf}
  | (((['1' - '9'])(numeric*)) as s) whitespace* ")" {syntaxattr (attrs@[Strict (nums@[parseNat (int_of_string s)])]) lexbuf }

and string start_string = parse
   "\""     { Terminal (parseString start_string) }
 | "\\\\"   { string (start_string ^ "\\") lexbuf }
 | "\\\""   { string (start_string ^ "\"") lexbuf }
 | "\\t"    { string (start_string ^ "\t") lexbuf }
 | "\\n"    { string (start_string ^ "\n") lexbuf }
 | "\\r"    { string (start_string ^ "\r") lexbuf }
 | "\\"     { raise (Failure "String Content Lexical error") }
 | _ as c   { string (start_string ^ (String.make 1 c)) lexbuf }

(* do not modify this function: *)
{
let lextest s = token (Lexing.from_string s)

 }
