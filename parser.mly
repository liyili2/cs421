/* Use the expression datatype defined in mp8common.ml: */
%{
(* add any extra code here *)

let rec parNat n = if n < 0 then raise (Failure "Strict Num cannot be less than zero") 
                        else if n = 0 then K.K.Zero_nat else K.K.Suc (parNat (n - 1));;

let rec parBits n = if n = 1 then K.K.One else if n = 2 then K.K.Bit0 (K.K.One)
            else if n mod 2 = 0 then K.K.Bit0 (parBits (n / 2))
                  else K.K.Bit1 (parBits (n / 2));;

let parCharNum n = if n = 0 then K.K.Zero_char else K.K.Char (parBits n);;

let parInt n = if n = 0 then K.K.Zero_int else if n < 0 then K.K.Neg (parBits (abs n)) else K.K.Pos (parBits n);;

let explodep s =
  let rec expp i l =
    if i < 0 then l else expp (i - 1) (s.[i] :: l) in
  expp (String.length s - 1) [];;

let rec getListOfChars a b = if a > b then []
              else if a = b then [parCharNum b]
              else (parCharNum a)::(getListOfChars (a+1) b);;

let rec intExp x n = if n = 0 then 1 else x * (intExp x (n - 1));;

let rec toInt x n = match x with K.K.One -> (intExp 2 n)
                       | K.K.Bit0 a -> toInt a (n + 1)
                       | K.K.Bit1 a -> (intExp 2 n) + (toInt a (n + 1));;

let parseKChar c = match c with K.K.Zero_char -> 0
      | K.K.Char x -> (toInt x 0);;

let rec getAllChars l = match l with [] -> []
         | x::xl -> (match x with K.K.AChar y ->
             (match xl with [] -> (y::(getAllChars xl))
                  | a::al -> (match a with K.K.AChar b -> (y::getAllChars xl)
                     | K.K.To -> (match al with [] -> raise (Failure "Failed input of a regular expression.")
                  | (c::cl) -> (match c with K.K.AChar d
                     -> (getListOfChars (parseKChar y) (parseKChar d))@(getAllChars cl)
                                        | _ -> raise (Failure "Failed input of a regular expression.")))
                                   | _ -> raise (Failure "Failed input of a regular expression.")))
                    | _ -> raise (Failure "Failed input of a regular expression."));;

let rec formAltsFromChars l = match l with [] -> K.K.Eps
                 | [x] -> K.K.Sym x | (x::xl) -> K.K.Alt (K.K.Sym x, formAltsFromChars xl);;

let rec findRBr xl yl = match yl with [] -> raise (Failure "Cannot Find Right BR.")
                   | a::al -> (match a with K.K.RBr -> (xl,al) | _ -> findRBr (xl@[a]) al);;

let rec toReg l = match l with [] -> K.K.Eps
              | x::xl -> match x with K.K.AChar y -> toRegAux (K.K.Sym y) xl
                       | K.K.LBr -> (match findRBr [] xl with (al,bl) -> toRegAux (formAltsFromChars (getAllChars al)) bl)
                       | _ -> raise (Failure "No other possible input char.")
and toRegAux a l = match l with [] -> a
         | (x::xl) -> (match x with K.K.AChar y -> (match toReg l with f -> K.K.TheSeq (a,f))
                          | K.K.TheStar -> (match toReg xl with f -> K.K.TheSeq (K.K.Rep a,f))
                          | K.K.LBr -> (match findRBr [] xl with (al,bl) -> toRegAux (K.K.TheSeq (a,(formAltsFromChars (getAllChars al)))) bl)
                          | K.K.Plus -> (match toReg xl with f -> K.K.TheSeq (K.K.TheSeq (a, (K.K.Rep a)),f)) 
                          | K.K.OneOrMore -> (match toReg xl with f -> K.K.TheSeq (K.K.Alt (a, K.K.Eps),f))
                          | _ ->  raise (Failure "No other possible input Command."));;

let rec sortAdjustAux t l = match l with [] -> []
          | x::xl -> (match x with K.K.Syntax (a,b,c) -> K.K.Syntax (t,b,c)::(sortAdjustAux t xl)
                           | K.K.Subsort (a,b) -> K.K.Subsort (a,t)::(sortAdjustAux t xl)
                           | K.K.Token (a,b,c) -> K.K.Token (t,b,c)::(sortAdjustAux t xl)
                           | K.K.ListSyntax (a,b,c,d) -> K.K.ListSyntax (t,b,c,d)::(sortAdjustAux t xl));;

let rec sortAdjust t l = match l with [] -> [] | x::xl -> (sortAdjustAux t x)::(sortAdjust t xl);;

let rec dealWithSorts l = match l with [] -> raise (Failure "Cannot have a syntactic sugar construct without fields.")
                               | [a] -> K.K.Con (K.K.NonTerminal a, K.K.Single
                  (K.K.Terminal [parCharNum (int_of_char ')')]))
                               | a::al -> K.K.Con (K.K.NonTerminal a, K.K.Con (K.K.Terminal [parCharNum (int_of_char ',')], dealWithSorts al));;

let dealWithSugar a l = K.K.Con (K.K.Terminal a, K.K.Con (K.K.Terminal [parCharNum (int_of_char '(')], dealWithSorts l));;

let rec dealWithSugarAttr a l = match l with [] -> [K.K.Klabel a]
                                    | x::xl -> (match x with K.K.Klabel y -> x::xl
                                                      | _ -> x::(dealWithSugarAttr a xl));;
let rec getKlabelChars l = match l with [] -> None
               | (K.K.Klabel s)::al -> Some s | a::al -> getKlabelChars al;;

let parChar c = parCharNum (int_of_char c);;

let parString s = List.map (fun c -> parChar c) (explodep s);;

let parseSort s = match s with K.K.Top -> parString "Top" | K.K.K -> parString "K" | K.K.Bool -> parString "Bool"
           | K.K.KItem -> parString "KItem" | K.K.KLabel -> parString "KLabel"
       | K.K.KResult -> parString "KResult" | K.K.KList -> parString "KList" | K.K.List -> parString "List"
     | K.K.Set -> parString "Set" | K.K.Map -> parString "Map" | K.K.Bag -> parString "Bag"
      | K.K.Id -> parString "Id" | K.K.String -> parString "String"
    | K.K.Int -> parString "Int" | K.K.Float -> parString "Float" | K.K.OtherSort s -> s;;

let toSort s = match s with "K" -> K.K.K | "Bool" -> K.K.Bool | "KItem" -> K.K.KItem
         | "KLabel" -> K.K.KLabel | "KResult" -> K.K.KResult
    | "KList" -> K.K.KList | "List" -> K.K.List | "Set" -> K.K.Set
    | "Map" -> K.K.Map | "Bag" -> K.K.Bag | "Id" -> K.K.Id | "String" -> K.K.String
    | "Int" -> K.K.Int | "Float" -> K.K.Float | _ -> K.K.OtherSort (parString s);;

let rec toRuleAttr l = match l with [] -> []
                     | (K.K.OtherSynAttr s)::sl -> if s = (parString "owise")
                       then K.K.Owise::(toRuleAttr sl) else toRuleAttr sl
                     | s::sl -> toRuleAttr sl;;

let rec mergeFeatures l1 l2 = match l2 with [] -> l1
               | x::xl -> if List.exists (fun a -> a = x) l1
                 then mergeFeatures l1 xl else mergeFeatures (x::l1) xl;;

let rec toVarInK x = match x with "k" -> K.K.LittleK | _ -> K.K.OtherVar (parString x);;

let rec checkAllInts s n = if n >= String.length s then true else
         Char.code (String.get s n) >= (Char.code '0')
        && Char.code (String.get s n) <= (Char.code '9')
        && checkAllInts s (n + 1);;

let rec dealWithLabel x = match x with "getKLabel" -> K.K.GetKLabel
           | "isKResult" -> K.K.IsKResult | "andBool" -> K.K.AndBool
        | "notBool" -> K.K.NotBool | "orBool" -> K.K.OrBool | "mapUpdate" -> K.K.MapUpdate
     | "==K" -> K.K.EqualK | "=/=K" -> K.K.NotEqualK | "==KLabel" -> K.K.EqualKLabel
      | "=/=KLabel" -> K.K.NotEqualKLabel | "==Set" -> K.K.EqualSet | "==Map" -> K.K.EqualMap
     | "+Int" -> K.K.PlusInt | "-Int" -> K.K.MinusInt
       | "*Int" -> K.K.TimesInt | "/Int" -> K.K.DivInt | "%Int" -> K.K.ModInt
      | "+Float" -> K.K.PlusFloat | "-Float" -> K.K.MinusFloat
      | "*Float" -> K.K.TimesFloat | "/Float" -> K.K.DivFloat
      | "<Float" -> K.K.LessFloat | "<=Float" -> K.K.LessEqualFloat
      | ">Float" -> K.K.GtFloat | ">=Float" -> K.K.GeqFloat
     | "true" -> K.K.ConstToLabel (K.K.BoolConst true)
     | "<Int" -> K.K.LessInt | "<=Int" -> K.K.LessEqualInt
     | ">Int" -> K.K.GtInt | ">=Int" -> K.K.GeqInt
     | "false" -> K.K.ConstToLabel (K.K.BoolConst false)
     | "+String" -> K.K.StringCon
     | "intToString" -> K.K.IntToString
     | _ -> if checkAllInts x 0 then K.K.ConstToLabel (K.K.IntConst (parInt (int_of_string x)))
                   else K.K.OtherLabel (parString x);;
%}

/* Define the tokens of the language: */
%token <K.K.char list> Terminal OtherSort Klabel OtherSynAttr
%token <K.K.synAttrib list> Attr
%token <K.K.nat list> Strict
%token <K.K.atoken list> AToken
%token <string> EmptyLabel LabelId Variable
%token <string * K.K.feature list> BagWrap BagBack
%token Bool K KItem KLabel KResult KList List Seta Map Bag Id String Int Float
       Assign Bar Gt EOF Left Right Function Seqstrict
       NonAssoc Tokena Avoid Bracket LBig RBig Dot TheStar Plus LPAREN RPAREN
        TypeCon ASetCon AListCon AConfiguration ARule ASyntax AMapCon ARewrite AMapUpdate Requires
       ASetItem AMapItem AListItem AProgram

/* Define the "goal" nonterminal of the grammar: */
%start main
%type < (K.K.char list, K.K.char list, K.K.char list) K.K.theoryParsed> main

%%

main: 
    ARule rulebags ARewrite rulebags Requires ruleexpression Attr
             { K.K.Parsed (None, [],[($2, ($4, ($6, toRuleAttr $7)))], None) }
  | ARule rulebags ARewrite rulebags Requires ruleexpression
             { K.K.Parsed (None,[],[($2, ($4, ($6, [])))], None) }
  | ARule rulebags ARewrite rulebags
             { K.K.Parsed (None,[],[($2, ($4, (K.K.SimTerm (K.K.ConstToLabel (K.K.BoolConst true), []), [])))], None) }
  | ARule rulebags ARewrite rulebags Attr
             { K.K.Parsed (None,[],[($2, ($4, (K.K.SimTerm
                          (K.K.ConstToLabel (K.K.BoolConst true), []), toRuleAttr $5)))], None) }

  | ARule rulebags ARewrite rulebags Requires ruleexpression Attr main
             {match $8 with K.K.Parsed (c,x,y,p) -> K.K.Parsed (c, x, ($2,($4,($6, toRuleAttr $7)))::y,p)}
  | ARule rulebags ARewrite rulebags Requires ruleexpression main
             {match $7 with K.K.Parsed (c,x,y,p) -> K.K.Parsed (c,x, ($2,($4,($6, [])))::y,p)}

  | ARule rulebags ARewrite rulebags main
             {match $5 with K.K.Parsed (c,x,y,p) -> K.K.Parsed (c, x,
                     ($2, ($4, (K.K.SimTerm (K.K.ConstToLabel (K.K.BoolConst true), []), [])))::y,p)}
  | ARule rulebags ARewrite rulebags Attr main
             {match $6 with K.K.Parsed (c, x,y,p) -> K.K.Parsed (c, x,
                     ($2, ($4, (K.K.SimTerm (K.K.ConstToLabel (K.K.BoolConst true), []), toRuleAttr $5)))::y,p)}

  | ASyntax sort Assign expressions   {K.K.Parsed (None,[($2,sortAdjust $2 $4)], [], None)}
  | ASyntax sort Assign expressions main    {match $5 with K.K.Parsed (c,x,y,p)
                                 -> match $4 with u -> K.K.Parsed (c,($2,sortAdjust $2 $4)::x, y,p)}
  | AConfiguration rulebags {K.K.Parsed (Some $2, [], [], None)}
  | AConfiguration rulebags main {match $3 with K.K.Parsed (None, x, y,p) -> K.K.Parsed(Some $2, x, y,p)
                                     | _ -> raise (Failure "More than one configuration in a K file.")}
  | AProgram ruleexpression {K.K.Parsed (None, [], [], Some $2)}
  | AProgram ruleexpression main {match $3 with K.K.Parsed(c, x, y, None) -> K.K.Parsed(c, x, y, Some $2)
                                     | _ -> raise (Failure "More than one program in a K file.")}
expressions:
    subexpressions {[$1]}
  | subexpressions Gt expressions {$1::$3}

subexpressions:
    expression  {[$1]}
  | expression Bar subexpressions {$1::$3}

expression:
    List LBig sort Dot Terminal RBig Attr { K.K.ListSyntax (K.K.Top, $3, $5, $7) }
  | List LBig sort Dot Terminal RBig { K.K.ListSyntax (K.K.Top, $3, $5, []) }
  | AToken Attr {K.K.Token (K.K.Top, toReg $1, $2)}
  | AToken {K.K.Token (K.K.Top, toReg $1, [])}
  | production Attr {match $1 with K.K.Single (K.K.NonTerminal x) ->
            (match getKlabelChars $2 with None -> K.K.Subsort (x, K.K.Top)
                  | Some s -> K.K.Syntax (K.K.Top,
          K.K.Con (K.K.Terminal s,K.K.Con (K.K.Terminal [parCharNum (int_of_char '(')], K.K.Con (K.K.NonTerminal x,
               K.K.Single (K.K.Terminal [parCharNum (int_of_char ')')])))), $2))
                           | y -> K.K.Syntax (K.K.Top, y, $2) }
  | production {match $1 with K.K.Single (K.K.NonTerminal x) -> K.K.Subsort (x, K.K.Top)
                           | y -> K.K.Syntax (K.K.Top, y, []) }
  | LabelId LPAREN sorts RPAREN {K.K.Syntax (K.K.Top,dealWithSugar (parString $1) $3,[K.K.Klabel (parString $1)]) }
  | LabelId LPAREN sorts RPAREN Attr {K.K.Syntax (K.K.Top,dealWithSugar (parString $1) $3, dealWithSugarAttr (parString $1) $5) }

rulebags:
    ruleexpression {$1}
  | BagWrap rulebags BagBack {match $1 with (s,fl) -> match $3 with (s', fl')
                    -> if s = s' then K.K.SimBag (toVarInK s,(mergeFeatures fl fl'), $2)
              else raise (Failure "bag name front-end mismatch.")}
  | BagWrap rulebags BagBack rulebags {
               match $1 with (s,fl)
                       -> match $3 with (s', fl')
                    -> if s = s' then K.K.SimBagCon (K.K.SimBag (toVarInK s,(mergeFeatures fl fl'),$2), $4)
              else raise (Failure "bag name front-end mismatch.")}

ruleexpressions:
    ruleexpression {[$1]}
  | ruleexpression Dot ruleexpressions {$1::$3}

ruleexpression:
  LabelId {K.K.SimLabel (dealWithLabel $1)}
  | EmptyLabel {K.K.SimEmpty (toSort $1)}
  | sort {K.K.SimId (K.K.Defined (parseSort $1), K.K.Top)}
  | sort TypeCon sort {K.K.SimId (K.K.Defined (parseSort $1), $3)}
  | LabelId LPAREN ruleexpressions RPAREN {K.K.SimTerm (dealWithLabel $1, $3)}
  | Terminal {K.K.SimTerm (K.K.ConstToLabel (K.K.StringConst $1), [])}
  | Variable LPAREN ruleexpressions RPAREN {K.K.SimTerm (K.K.ConstToLabel (K.K.IdConst (parString $1)), $3)}
  | ASetItem LPAREN ruleexpressions RPAREN {K.K.SimTerm (K.K.SetItemLabel, $3)}
  | ASetCon LPAREN ruleexpressions RPAREN {K.K.SimTerm (K.K.SetConLabel, $3)}
  | AListItem LPAREN ruleexpressions RPAREN {K.K.SimTerm (K.K.ListItemLabel, $3)}
  | AListCon LPAREN ruleexpressions RPAREN {K.K.SimTerm (K.K.ListConLabel, $3)}
  | AMapUpdate LPAREN ruleexpressions RPAREN {K.K.SimTerm (K.K.MapUpdate, $3)}
  | AMapItem LPAREN ruleexpressions RPAREN {K.K.SimTerm (K.K.MapItemLabel, $3)}
  | AMapCon LPAREN ruleexpressions RPAREN {K.K.SimTerm (K.K.MapConLabel, $3)}

production:
   sort {K.K.Single (K.K.NonTerminal $1)}
  | Terminal {K.K.Single (K.K.Terminal $1)}
  | sort production {K.K.Con (K.K.NonTerminal $1, $2)}
  | Terminal production {K.K.Con (K.K.Terminal $1, $2)}

sorts:
    sort {[$1]}
  | sort Dot sorts {$1::$3}
	
sort:
    Bool   { K.K.Bool }
  | K      {K.K.K}
  | KItem      {K.K.KItem}
  | KLabel      {K.K.KLabel}
  | KResult      {K.K.KResult}
  | KList      {K.K.KList}
  | List      {K.K.List}
  | Seta      {K.K.Set}
  | Map      {K.K.Map}
  | Bag      {K.K.Bag}
  | Id      {K.K.Id}
  | String      {K.K.String}
  | Int      {K.K.Int}
  | Float      {K.K.Float}
  | OtherSort      {K.K.OtherSort $1}
   

