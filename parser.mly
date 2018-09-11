/* Use the expression datatype defined in mp8common.ml: */
%{
(* add any extra code here *)
open K;;

let rec parNat n = if n < 0 then raise (Failure "Strict Num cannot be less than zero") 
                        else if n = 0 then Zero_nat else Suc (parNat (n - 1));;

let rec parBits n = if n = 1 then One else if n = 2 then Bit0 (One)
            else if n mod 2 = 0 then Bit0 (parBits (n / 2))
                  else Bit1 (parBits (n / 2));;

let parCharNum n = if n = 0 then Zero_char else Char (parBits n);;

let parInt n = if n = 0 then Zero_int else if n < 0 then Neg (parBits (abs n)) else Pos (parBits n);;

let explodep s =
  let rec expp i l =
    if i < 0 then l else expp (i - 1) (s.[i] :: l) in
  expp (String.length s - 1) [];;

let rec getListOfChars a b = if a > b then []
              else if a = b then [parCharNum b]
              else (parCharNum a)::(getListOfChars (a+1) b);;

let rec intExp x n = if n = 0 then 1 else x * (intExp x (n - 1));;

let rec toInt x n = match x with One -> (intExp 2 n)
                       | Bit0 a -> toInt a (n + 1)
                       | Bit1 a -> (intExp 2 n) + (toInt a (n + 1));;

let parseKChar c = match c with Zero_char -> 0
      | Char x -> (toInt x 0);;

let rec getAllChars l = match l with [] -> []
         | x::xl -> (match x with AChar y ->
             (match xl with [] -> (y::(getAllChars xl))
                  | a::al -> (match a with AChar b -> (y::getAllChars xl)
                     | To -> (match al with [] -> raise (Failure "Failed input of a regular expression.")
                  | (c::cl) -> (match c with AChar d
                     -> (getListOfChars (parseKChar y) (parseKChar d))@(getAllChars cl)
                                        | _ -> raise (Failure "Failed input of a regular expression.")))
                                   | _ -> raise (Failure "Failed input of a regular expression.")))
                    | _ -> raise (Failure "Failed input of a regular expression."));;

let rec formAltsFromChars l = match l with [] -> Eps
                 | [x] -> Sym x | (x::xl) -> Alt (Sym x, formAltsFromChars xl);;

let rec findRBr xl yl = match yl with [] -> raise (Failure "Cannot Find Right BR.")
                   | a::al -> (match a with RBr -> (xl,al) | _ -> findRBr (xl@[a]) al);;

let rec toReg l = match l with [] -> Eps
              | x::xl -> match x with AChar y -> toRegAux (Sym y) xl
                       | LBr -> (match findRBr [] xl with (al,bl) -> toRegAux (formAltsFromChars (getAllChars al)) bl)
                       | _ -> raise (Failure "No other possible input char.")
and toRegAux a l = match l with [] -> a
         | (x::xl) -> (match x with AChar y -> (match toReg l with f -> TheSeq (a,f))
                          | TheStar -> (match toReg xl with f -> TheSeq (Rep a,f))
                          | LBr -> (match findRBr [] xl with (al,bl) -> toRegAux (TheSeq (a,(formAltsFromChars (getAllChars al)))) bl)
                          | Plus -> (match toReg xl with f -> TheSeq (TheSeq (a, (Rep a)),f)) 
                          | OneOrMore -> (match toReg xl with f -> TheSeq (Alt (a, Eps),f))
                          | _ ->  raise (Failure "No other possible input Command."));;

let rec sortAdjustAux t l = match l with [] -> []
          | x::xl -> (match x with Syntax (a,b,c) -> Syntax (t,b,c)::(sortAdjustAux t xl)
                           | Subsort (a,b) -> Subsort (a,t)::(sortAdjustAux t xl)
                           | Token (a,b,c) -> Token (t,b,c)::(sortAdjustAux t xl)
                           | ListSyntax (a,b,c,d) -> ListSyntax (t,b,c,d)::(sortAdjustAux t xl));;

let rec sortAdjust t l = match l with [] -> [] | x::xl -> (sortAdjustAux t x)::(sortAdjust t xl);;

let rec dealWithSorts l = match l with [] -> raise (Failure "Cannot have a syntactic sugar construct without fields.")
                               | [a] -> Con (NonTerminal a, Single
                  (Terminal [parCharNum (int_of_char ')')]))
                               | a::al -> Con (NonTerminal a, Con (Terminal [parCharNum (int_of_char ',')], dealWithSorts al));;

let dealWithSugar a l = Con (Terminal a, Con (Terminal [parCharNum (int_of_char '(')], dealWithSorts l));;

let rec dealWithSugarAttr a l = match l with [] -> [Klabel a]
                                    | x::xl -> (match x with Klabel y -> x::xl
                                                      | _ -> x::(dealWithSugarAttr a xl));;
let rec getKlabelChars l = match l with [] -> None
               | (Klabel s)::al -> Some s | a::al -> getKlabelChars al;;

let parChar c = parCharNum (int_of_char c);;

let parString s = List.map (fun c -> parChar c) (explodep s);;

let parseSort s = match s with K.Top -> parString "Top" | K -> parString "K" | Bool -> parString "Bool"
           | KItem -> parString "KItem" | KLabel -> parString "KLabel"
       | KResult -> parString "KResult" | KList -> parString "KList" | List -> parString "List"
     | Set -> parString "Set" | Map -> parString "Map" | Bag -> parString "Bag"
      | Id -> parString "Id" | String -> parString "String"
    | Int -> parString "Int" | Float -> parString "Float" | OtherSort s -> s;;

let toSort s = match s with "K" -> K.K | "Bool" -> K.Bool | "KItem" -> KItem
         | "KLabel" -> KLabel | "KResult" -> KResult
    | "KList" -> KList | "List" -> List | "Set" -> Set
    | "Map" -> Map | "Bag" -> Bag | "Id" -> Id | "String" -> String
    | "Int" -> Int | "Float" -> Float | _ -> OtherSort (parString s);;

let rec toRuleAttr l = match l with [] -> []
                     | (OtherSynAttr s)::sl -> if s = (parString "owise")
                       then Owise::(toRuleAttr sl) else toRuleAttr sl
                     | s::sl -> toRuleAttr sl;;

let rec mergeFeatures l1 l2 = match l2 with [] -> l1
               | x::xl -> if List.exists (fun a -> a = x) l1
                 then mergeFeatures l1 xl else mergeFeatures (x::l1) xl;;

let rec toVarInK x = match x with "k" -> LittleK | _ -> OtherVar (parString x);;

let rec checkAllInts s n = if n >= String.length s then true else
         Char.code (String.get s n) >= (Char.code '0')
        && Char.code (String.get s n) <= (Char.code '9')
        && checkAllInts s (n + 1);;

let rec dealWithLabel x = match x with "getKLabel" -> GetKLabel
           | "isKResult" -> IsKResult | "andBool" -> AndBool
        | "notBool" -> NotBool | "orBool" -> OrBool | "mapUpdate" -> MapUpdate
     | "==K" -> EqualK | "=/=K" -> NotEqualK | "==KLabel" -> EqualKLabel
      | "=/=KLabel" -> NotEqualKLabel | "==Set" -> EqualSet | "==Map" -> EqualMap
     | "+Int" -> PlusInt | "-Int" -> MinusInt
       | "*Int" -> TimesInt | "true" -> ConstToLabel (BoolConst true)
     | "<Int" -> K.LessInt | "<=Int" -> K.LessEqualInt
     | "false" -> ConstToLabel (BoolConst false)
     | "+String" -> StringCon
     | "intToString" -> IntToString
     | _ -> if checkAllInts x 0 then ConstToLabel (IntConst (parInt (int_of_string x)))
                   else OtherLabel (parString x);;
%}

/* Define the tokens of the language: */
%token <K.char list> Terminal OtherSort Klabel OtherSynAttr
%token <K.synAttrib list> Attr
%token <K.nat list> Strict
%token <K.atoken list> AToken
%token <string> EmptyLabel LabelId Variable
%token <string * K.feature list> BagWrap BagBack
%token Bool K KItem KLabel KResult KList List Seta Map Bag Id String Int Float
       Assign Bar Gt EOF Left Right Function Seqstrict
       NonAssoc Tokena Avoid Bracket LBig RBig Dot TheStar Plus LPAREN RPAREN
        TypeCon ASetCon AListCon AConfiguration ARule ASyntax AMapCon ARewrite AMapUpdate Requires
       ASetItem AMapItem AListItem AProgram

/* Define the "goal" nonterminal of the grammar: */
%start main
%type < (K.char list, K.char list, K.char list) K.theoryParsed> main

%%

main: 
    ARule rulebags ARewrite rulebags Requires ruleexpression Attr
             { Parsed (None, [],[($2, ($4, ($6, toRuleAttr $7)))], None) }
  | ARule rulebags ARewrite rulebags Requires ruleexpression
             { Parsed (None,[],[($2, ($4, ($6, [])))], None) }
  | ARule rulebags ARewrite rulebags
             { Parsed (None,[],[($2, ($4, (SimTerm (ConstToLabel (BoolConst true), []), [])))], None) }
  | ARule rulebags ARewrite rulebags Attr
             { Parsed (None,[],[($2, ($4, (SimTerm
                          (ConstToLabel (BoolConst true), []), toRuleAttr $5)))], None) }

  | ARule rulebags ARewrite rulebags Requires ruleexpression Attr main
             {match $8 with Parsed (c,x,y,p) -> Parsed (c, x, ($2,($4,($6, toRuleAttr $7)))::y,p)}
  | ARule rulebags ARewrite rulebags Requires ruleexpression main
             {match $7 with Parsed (c,x,y,p) -> Parsed (c,x, ($2,($4,($6, [])))::y,p)}

  | ARule rulebags ARewrite rulebags main
             {match $5 with Parsed (c,x,y,p) -> Parsed (c, x,
                     ($2, ($4, (SimTerm (ConstToLabel (BoolConst true), []), [])))::y,p)}
  | ARule rulebags ARewrite rulebags Attr main
             {match $6 with Parsed (c, x,y,p) -> Parsed (c, x,
                     ($2, ($4, (SimTerm (ConstToLabel (BoolConst true), []), toRuleAttr $5)))::y,p)}

  | ASyntax sort Assign expressions   {Parsed (None,[($2,sortAdjust $2 $4)], [], None)}
  | ASyntax sort Assign expressions main    {match $5 with Parsed (c,x,y,p)
                                 -> match $4 with u -> Parsed (c,($2,sortAdjust $2 $4)::x, y,p)}
  | AConfiguration rulebags {Parsed (Some $2, [], [], None)}
  | AConfiguration rulebags main {match $3 with Parsed(None, x, y,p) -> Parsed(Some $2, x, y,p)
                                     | _ -> raise (Failure "More than one configuration in a K file.")}
  | AProgram ruleexpression {Parsed (None, [], [], Some $2)}
  | AProgram ruleexpression main {match $3 with Parsed(c, x, y, None) -> Parsed(c, x, y, Some $2)
                                     | _ -> raise (Failure "More than one program in a K file.")}
expressions:
    subexpressions {[$1]}
  | subexpressions Gt expressions {$1::$3}

subexpressions:
    expression  {[$1]}
  | expression Bar subexpressions {$1::$3}

expression:
    List LBig sort Dot Terminal RBig Attr { ListSyntax (Top, $3, $5, $7) }
  | List LBig sort Dot Terminal RBig { ListSyntax (Top, $3, $5, []) }
  | AToken Attr {Token (Top, toReg $1, $2)}
  | AToken {Token (Top, toReg $1, [])}
  | production Attr {match $1 with Single (NonTerminal x) ->
            (match getKlabelChars $2 with None -> Subsort (x, Top)
                  | Some s -> Syntax (Top,
          Con (Terminal s,Con (Terminal [parCharNum (int_of_char '(')], Con (NonTerminal x,
               Single (Terminal [parCharNum (int_of_char ')')])))), $2))
                           | y -> Syntax (Top, y, $2) }
  | production {match $1 with Single (NonTerminal x) -> Subsort (x, Top)
                           | y -> Syntax (Top, y, []) }
  | LabelId LPAREN sorts RPAREN {Syntax (Top,dealWithSugar (parString $1) $3,[Klabel (parString $1)]) }
  | LabelId LPAREN sorts RPAREN Attr {Syntax (Top,dealWithSugar (parString $1) $3, dealWithSugarAttr (parString $1) $5) }

rulebags:
    ruleexpression {$1}
  | BagWrap rulebags BagBack {match $1 with (s,fl) -> match $3 with (s', fl')
                    -> if s = s' then SimBag (toVarInK s,(mergeFeatures fl fl'), $2)
              else raise (Failure "bag name front-end mismatch.")}
  | BagWrap rulebags BagBack rulebags {
               match $1 with (s,fl)
                       -> match $3 with (s', fl')
                    -> if s = s' then SimBagCon (SimBag (toVarInK s,(mergeFeatures fl fl'),$2), $4)
              else raise (Failure "bag name front-end mismatch.")}

ruleexpressions:
    ruleexpression {[$1]}
  | ruleexpression Dot ruleexpressions {$1::$3}

ruleexpression:
  LabelId {SimLabel (dealWithLabel $1)}
  | EmptyLabel {SimEmpty (toSort $1)}
  | sort {SimId (Defined (parseSort $1), Top)}
  | sort TypeCon sort {SimId (Defined (parseSort $1), $3)}
  | LabelId LPAREN ruleexpressions RPAREN {SimTerm (dealWithLabel $1, $3)}
  | Terminal {SimTerm (ConstToLabel (StringConst $1), [])}
  | Variable LPAREN ruleexpressions RPAREN {SimTerm (ConstToLabel (IdConst (parString $1)), $3)}
  | ASetItem LPAREN ruleexpressions RPAREN {SimTerm (SetItemLabel, $3)}
  | ASetCon LPAREN ruleexpressions RPAREN {SimTerm (SetConLabel, $3)}
  | AListItem LPAREN ruleexpressions RPAREN {SimTerm (ListItemLabel, $3)}
  | AListCon LPAREN ruleexpressions RPAREN {SimTerm (ListConLabel, $3)}
  | AMapUpdate LPAREN ruleexpressions RPAREN {SimTerm (MapUpdate, $3)}
  | AMapItem LPAREN ruleexpressions RPAREN {SimTerm (MapItemLabel, $3)}
  | AMapCon LPAREN ruleexpressions RPAREN {SimTerm (MapConLabel, $3)}

production:
   sort {Single (NonTerminal $1)}
  | Terminal {Single (Terminal $1)}
  | sort production {Con (NonTerminal $1, $2)}
  | Terminal production {Con (Terminal $1, $2)}

sorts:
    sort {[$1]}
  | sort Dot sorts {$1::$3}
	
sort:
    Bool   { Bool }
  | K      {K}
  | KItem      {KItem}
  | KLabel      {KLabel}
  | KResult      {KResult}
  | KList      {KList}
  | List      {List}
  | Seta      {Set}
  | Map      {Map}
  | Bag      {Bag}
  | Id      {Id}
  | String      {String}
  | Int      {Int}
  | Float      {Float}
  | OtherSort      {OtherSort $1}
   

