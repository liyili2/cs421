type result = Good of string | Error of int * string * string option;;

type output = Output of int * result;;

#load "k.cmo";;
#load "lexer.cmo";;
#load "parser.cmo";;
#load "cpsLexer.cmo";;
#load "cpsParser.cmo";;
open K;;
open K;;
open Parser;;
open Lexer;;
open CpsLexer;;
open CpsParser;;

let save file string =
     let channel = open_out_gen [Open_wronly; Open_append; Open_creat; Open_text] 0o666 file in
     output_string channel string;
     close_out channel;;

let read_file filename = 
let lines = ref [] in
let chan = open_in filename in
try
  while true; do
    lines := input_line chan :: !lines
  done; []
with End_of_file ->
  close_in chan;
  List.rev !lines ;;


let rec combineString lst = match lst with [] -> ""
                                     | x::xs -> x^"\n"^combineString xs;;

  let get_all_tokens s =
      let b = Lexing.from_string (s^"\n") in
      let rec g () =
      match token b with EOF -> []
      | t -> t :: g () in
      g ();;

let rec intExp x n = if n = 0 then 1 else x * (intExp x (n - 1));;

let rec toInt x n = match x with One -> (intExp 2 n)
                       | Bit0 a -> toInt a (n + 1)
                       | Bit1 a -> (intExp 2 n) + (toInt a (n + 1));;

let parseKChar c = match c with Zero_char -> 0
      | Char x -> (toInt x 0);;

let rec charListToString c = match c with [] -> ""
            | a::al -> (Char.escaped (Char.chr (parseKChar a))) ^ charListToString al;;

let rec knatToInt a = match a with Zero_nat -> 0
                    | Suc x -> 1 + knatToInt x;;

let printKNat a = string_of_int (knatToInt a);;

let rec intExp x n = if n = 0 then 1 else x * (intExp x (n - 1));;

let rec toInt x n = match x with One -> (intExp 2 n)
                       | Bit0 a -> toInt a (n + 1)
                       | Bit1 a -> (intExp 2 n) + (toInt a (n + 1));;

let parseKChar c = match c with Zero_char -> 0
      | Char x -> (toInt x 0);;

let printKChar a = string_of_int (parseKChar a);;

let printKInt a = match a with Zero_int -> "0"
          | Pos x -> string_of_int (toInt x 0) 
          | Neg x -> string_of_int (- (toInt x 0));;

let printKChar a = string_of_int (parseKChar a);;

let charsToStringInMetaVar a = match a with FunHole -> "FunHole"
      | Generated x -> "Generated " ^ (printKNat x)
      | Defined x -> "Defined " ^ (charListToString x);;

let charsToStringInVar a = match a with LittleK -> "k"
      | OtherVar x -> (charListToString x);;

let featureToString a = match a with Multiplicity x -> 
       (match x with Star -> "multiplicity=*"
                 | Question -> "multiplicity=?")
       | Stream x -> (match x with Stdin -> "stream=stdin"
                 | Stdout -> "stream=stdout")
       | DotDotDot -> "...";;

let rec featureListToString l = match l with [] -> ""
           | a::al -> (featureToString a)^" "^(featureListToString al);;

let charsToStringInSort a = 
    match a with K.OtherSort x -> "Sort "^(charListToString x)
               | Bool -> "Bool" | K -> "K" | KItem -> "KItem"
              | KLabel -> "KLabel" | KResult -> "KResult" | KList -> "KList"
               | List -> "List" | Set -> "Set" | Map -> "Map"
              | Bag -> "Bag" | Top -> "Top" | Int -> "Int" | Float -> "Float"
               | Id -> "Id" | String -> "String";;

let rec charsToStringInSortsAux l = match l with [] -> "]"
            | a::al -> (charsToStringInSort a) ^ ","^ (charsToStringInSortsAux al);;
let charsToStringInSorts l = "["^ charsToStringInSortsAux l;;

let printConst a = match a with IntConst x -> printKInt x
              | FloatConst x -> "Float"
              | StringConst x -> charListToString x
              | BoolConst x -> if x = true then "true" else "false"
              | IdConst x -> "$"^charListToString x;;

let charsToStringInLabel a = 
    match a with UnitLabel x -> "."^(charsToStringInSort x)
       | ConstToLabel x -> "'"^ (printConst x)
    | Sort -> "'Sort" | GetKLabel -> "'GetKLabel"
    | IsKResult -> "'IsKResult" | AndBool -> "'AndBool"
    | NotBool -> "'NotBool" | OrBool -> "'OrBool"
    | SetConLabel -> "'SetConLabel" | SetItemLabel -> "'SetItemLabel"
    | ListConLabel -> "'ListConLabel" | ListItemLabel -> "'ListItemLabel"
    | MapConLabel -> "'MapConLabel" | MapItemLabel -> "'MapItemLabel"
    | MapUpdate -> "'MapUpdate" | EqualK -> "'EqualK"
    | NotEqualK -> "'NotEqualK" | EqualKLabel -> "'EqualKLabel"
    | NotEqualKLabel -> "'NotEqualKLabel"
    | OtherLabel x -> "'"^ (charListToString x)
    | TokenLabel x -> "'"^ (charListToString x)
    | PlusInt -> "'PlusInt" | MinusInt -> "'MinusInt"
    | TimesInt -> "'TimesInt" | EqualSet -> "'EqualSet"
    | EqualMap -> "'EqualMap" | StringCon -> "'StringCon"
    | IntToString -> "'IntToString"
    | LessInt -> "'<Int"
    | LessEqualInt -> "'<=Int"
    | DivInt -> "/Int" | ModInt -> "%Int" | PlusFloat -> "+Float"
    | MinusFloat -> "-Float" | TimesFloat -> "*Float"
    | DivFloat -> "/Float" | GtInt -> ">Int" | GeqInt -> ">=Int"
    | LessFloat -> "<Float" | LessEqualFloat -> "<=Float"
    | GtFloat -> ">Float" | GeqFloat -> ">=Float";;

let rec charsToStringInSUBigKWithBag a =
     match a with SUK al -> "SUK" ^ " [" ^ (charsToStringInSUKFactorList al) ^ "]"
          | SUList al -> "SUList"^ " [" ^ (charsToStringInSUList al)^ "]"
          | SUSet al -> "SUSet"^ " [" ^(charsToStringInSUSet al)^ "]"
          | SUMap al -> "SUMap"^ " [" ^ (charsToStringInSUMap al)^ "]"
          | SUBag al -> "SUBag"^ " [" ^ (charsToStringInSUBag al)^ "]"
and charsToStringInSUKFactorList l =
       match l with [] -> ".K"
           | (a::al) -> (charsToStringInSUKFactor a)^" ~> "^(charsToStringInSUKFactorList al)
and charsToStringInSUList l =
       match l with [] -> ".List"
           | (a::al) -> (charsToStringInSUL a)^" "^(charsToStringInSUList al)
and charsToStringInSUSet l =
       match l with [] -> ".Set"
           | (a::al) -> (charsToStringInSUS a)^" "^(charsToStringInSUSet al)
and charsToStringInSUMap l =
       match l with [] -> ".Map"
           | (a::al) -> (charsToStringInSUM a)^" "^(charsToStringInSUMap al)
and charsToStringInSUBigKWithLabel a =
      match a with SUBigBag al ->  (charsToStringInSUBigKWithBag al)
               | SUBigLabel al -> (charsToStringInSUKLabel al)
and charsToStringInSUKFactor a =
      match a with ItemFactor a -> (charsToStringInSUKItem a)
          | IdFactor a -> "IdFactor "^ (charsToStringInMetaVar a)
          | SUKKItem (x,y,z) -> "SUKKItem ("^(charsToStringInSUKLabel x)^", "
                      ^(charsToStringInSUKList y) ^", "^ (charsToStringInSorts z)^")"
and charsToStringInSUS a =
     match a with ItemS x -> "SetItem("^(charsToStringInSUKFactorList x)^")"
               | IdS x -> "IdS "^(charsToStringInMetaVar x)
               | SUSetKItem (x,y) ->
                     "SUSetKItem ("^charsToStringInSUKLabel x^", "^charsToStringInSUKList y^")"
and charsToStringInSUL a =
     match a with ItemL x -> "ListItem("^(charsToStringInSUKFactorList x)^")"
               | IdL x -> "IdL "^(charsToStringInMetaVar x)
               | SUListKItem (x,y) ->
                     "SUListKItem ("^charsToStringInSUKLabel x^", "^charsToStringInSUKList y^")"
and charsToStringInSUM a =
     match a with ItemM (x,y) -> "("^charsToStringInSUKFactorList x^
                                " |-> "^charsToStringInSUKFactorList y^")"
               | IdM x -> "IdM "^(charsToStringInMetaVar x)
               | SUMapKItem (x,y) ->
                     "SUMapKItem ("^charsToStringInSUKLabel x^", "^charsToStringInSUKList y^")"
and charsToStringInSUBag l = match l with [] -> ".Bag"
            | a::al -> (charsToStringInSUB a)^", "^(charsToStringInSUBag al)
and charsToStringInSUB a = match a with 
          ItemB (x,y,z) -> "<"^charsToStringInVar x^", "
                        ^featureListToString y^"> "^charsToStringInSUBigKWithBag z
                                ^" </"^charsToStringInVar x^">"
         | IdB x -> "IdB "^(charsToStringInMetaVar x)
and charsToStringInSUKList l = match l with [] -> ".KList"
            | a::al -> (charsToStringInSUKL a)^",, "^(charsToStringInSUKList al)
and charsToStringInSUKL a = match a with
        ItemKl x -> ""^(charsToStringInSUBigKWithLabel x)
       | IdKl x -> "IdKl "^(charsToStringInMetaVar x)
and charsToStringInSUKLabel a = match a with
       SUKLabel x -> (charsToStringInLabel x)
     | SUIdKLabel x -> "SUIdKLabel "^(charsToStringInMetaVar x)
     | SUKLabelFun (x,y) -> "SUKLabelFun ("^charsToStringInSUKLabel x^", "^charsToStringInSUKList y^")"
and charsToStringInSUKItem a = match a with
      SUKItem (x,y,z) -> charsToStringInSUKLabel x^"("^ 
                   charsToStringInSUKList y^")::"^charsToStringInSorts z
    | SUIdKItem (x,y) ->  charsToStringInMetaVar x^"::"^charsToStringInSorts y
    | SUHOLE x -> "HOLE "^(charsToStringInSorts x);;

let charsToStringInState a = match a with
     Continue x -> "Continue ("^charsToStringInSUBag x^")"
   | Stop x -> "Stop ("^charsToStringInSUBag x^")"
   | Div x -> "Div ("^charsToStringInSUBag x^")";;

let charsToStringInSubsFactor a = match a with
     KLabelSubs x -> charsToStringInSUKLabel x
   | KItemSubs x -> charsToStringInSUKItem x
   | KListSubs x -> charsToStringInSUKList x
   | KSubs x -> charsToStringInSUKFactorList x
   | ListSubs x -> charsToStringInSUList x
   | MapSubs x -> charsToStringInSUMap x
   | SetSubs x -> charsToStringInSUSet x
   | BagSubs x -> charsToStringInSUBag x;;

let rec charsToStringInSubstList l = match l with [] -> []
    | ((x,y)::al) -> (charsToStringInMetaVar x, charsToStringInSubsFactor y)::(charsToStringInSubstList al);;

let rec charsToStringInSubstListList l = match l with [] -> []
       | (a::al) -> (charsToStringInSubstList a)::(charsToStringInSubstListList al);;

let lexsee () = (get_all_tokens (combineString (read_file "cspapp.k")));;

let interpreta () = (Parser.main Lexer.token (Lexing.from_string (combineString (read_file "cspapp.k"))));;

let allEqual = {equal = (=)};;

let theGraph = subsortGraph {equal = (=)} (interpreta ());;

let typecorrects p = match p with Parsed (c, a,b,d) -> assignSortInRules {equal = (=)} {equal = (=)} b;;

let parsed = interpreta();;

let typedTerm = match typecorrects (interpreta()) with None -> [] | Some a -> a;;

let database = match collectDatabase (interpreta()) with None -> [] | Some a -> a;;

let allRules = match (tupleToRuleInParsed allEqual allEqual allEqual (interpreta())) with None -> []
                    | Some a -> a;;

let parseCPS s =  try Some (CpsParser.main CpsLexer.ftoken (Lexing.from_string s)) with 
            Stdlib.Parsing.Parse_error -> None;;

let readInProgram s = try Some (Parser.main Lexer.token (Lexing.from_string s))
                  with Stdlib.Parsing.Parse_error -> None;;

  let getAllCPSTokens s =
      let b = Lexing.from_string (s^"\n") in
      let rec g () =
      match CpsLexer.ftoken b with EOF -> []
      | t -> t :: g () in
      g ();;

let confi = match parsed with Parsed (Some a,b,c,d) -> a;;

(* let program = match readInProgram "f x" with Parsed (a, b,c, Some d) -> d;; *)

let programState s = match parseCPS s with None -> None
      | Some s' -> (match readInProgram s' with None -> None
      | Some (Parsed (a,b,c,d)) -> 
       (match parsed with Parsed (x,y,u,v) -> 
       genProgramState allEqual allEqual allEqual (Parsed (x,y,u,d)) database theGraph));;

typeCheckRules allEqual allEqual allRules database theGraph;;

let testResult = match genProgramState allEqual allEqual allEqual parsed database theGraph with None -> None
              | Some p -> (match funEvaluation allEqual allEqual allEqual allRules database theGraph p with None -> Some "" | Some a -> Some (charsToStringInSUBag a));;

let printFloat s = match s with Ratreal (Frct (x,y)) -> (printKInt x)^"."^(printKInt y);;

let rec cpsExpToString t = match t with SUKItem ((SUKLabel x),y,z) -> 
       (match x with (OtherLabel l) -> if charListToString l = "if"
                 then (match y with [ItemKl (SUBigBag (SUK [ItemFactor sub1]));
                  ItemKl (SUBigBag (SUK [ItemFactor sub2]));
                   ItemKl (SUBigBag (SUK [ItemFactor sub3]))]
                   -> "if "^(cpsExpToString sub1)^" then "^(cpsExpToString sub2)
                         ^" else "^(cpsExpToString sub3) | _ -> "bad")
                 else if  charListToString l = "bigIf"
                  then (match y with [ItemKl (SUBigBag (SUK [ItemFactor sub1]));
                  ItemKl (SUBigBag (SUK [ItemFactor sub2]));
                   ItemKl (SUBigBag (SUK [ItemFactor sub3]))]
                   -> "IF "^(cpsExpToString sub1)^" THEN "^(cpsExpToString sub2)
                         ^" ELSE "^(cpsExpToString sub3) | _ -> "bad")
                 else if  charListToString l = "app"
                  then (match y with [ItemKl (SUBigBag (SUK [ItemFactor sub1]));
                  ItemKl (SUBigBag (SUK [ItemFactor sub2]))]
                   -> (cpsExpToString sub1)^"("^(cpsExpToString sub2)^")" | _ -> "bad")
                 else if  charListToString l = "bin"
                  then (match y with [ItemKl (SUBigBag (SUK [ItemFactor sub1]));
                  ItemKl (SUBigBag (SUK [ItemFactor sub2]));
                    ItemKl (SUBigBag (SUK [ItemFactor sub3]))]
                   -> "("^(cpsExpToString sub2)^") "^(cpsExpToString sub1)^" ("^(cpsExpToString sub3)^")"
                          | _ -> "bad")
                 else if  charListToString l = "unary"
                  then (match y with [ItemKl (SUBigBag (SUK [ItemFactor sub1]));
                  ItemKl (SUBigBag (SUK [ItemFactor sub2]))]
                   -> (cpsExpToString sub1)^"("^(cpsExpToString sub2)^")"
                          | _ -> "bad")
                 else if  charListToString l = "fun"
                  then (match y with [ItemKl (SUBigBag (SUK [ItemFactor sub1]));
                  ItemKl (SUBigBag (SUK [ItemFactor sub2]))]
                   -> "fun "^(cpsExpToString sub1)^" -> ("^(cpsExpToString sub2)^")"
                          | _ -> "bad")
                 else if  charListToString l = "fn"
                  then (match y with [ItemKl (SUBigBag (SUK [ItemFactor sub1]));
                  ItemKl (SUBigBag (SUK [ItemFactor sub2]))]
                   -> "FN "^(cpsExpToString sub1)^" -> ("^(cpsExpToString sub2)^")"
                          | _ -> "bad")
                 else if  charListToString l = "bigFun"
                  then (match y with [ItemKl (SUBigBag (SUK [ItemFactor sub1]));
                  ItemKl (SUBigBag (SUK [ItemFactor sub2]));
                     ItemKl (SUBigBag (SUK [ItemFactor sub3]))]
                   -> "FUN "^(cpsExpToString sub1)^" "^(cpsExpToString sub2)
                               ^" -> ("^(cpsExpToString sub3)^")"
                          | _ -> "bad")
                 else if  charListToString l = "let"
                  then (match y with [ItemKl (SUBigBag (SUK [ItemFactor sub1]));
                  ItemKl (SUBigBag (SUK [ItemFactor sub2]));
                     ItemKl (SUBigBag (SUK [ItemFactor sub3]))]
                   -> "let "^(cpsExpToString sub1)^" = "^(cpsExpToString sub2)
                               ^" in ("^(cpsExpToString sub3)^")"
                          | _ -> "bad")
                 else if  charListToString l = "trans"
                  then (match y with [ItemKl (SUBigBag (SUK [ItemFactor sub1]));
                  ItemKl (SUBigBag (SUK [ItemFactor sub2]))]
                   -> "[["^(cpsExpToString sub1)^"]]_{"^(cpsExpToString sub2)^"}"
                          | _ -> "bad")
                 else if  charListToString l = "undef" then "undefined"
                 else if  charListToString l = "plus" then "+"
                 else if  charListToString l = "minus" then "-"
                 else if  charListToString l = "times" then "*"
                 else if  charListToString l = "lt" then "<"
                 else if  charListToString l = "leq" then "<="
                 else if  charListToString l = "gt" then ">"
                 else if  charListToString l = "geq" then ">="
                 else "bad"
             | ConstToLabel (IntConst l) ->  printKInt l
              | ConstToLabel (FloatConst l) ->  printFloat l
              |  ConstToLabel (IdConst l) ->  charListToString l
             | _ -> "bad")
                   | _ -> "bad";;

(* error 0 for parsing error, 1 for rule error, 2 for rule name error. *)
let runCPS s = match programState s with None -> Output (0, Error(0, "Student has a parsing error", None))
        | Some x -> (match funEvaluation allEqual allEqual allEqual allRules database theGraph x
         with None -> Output (0, Error (0, "unknown error.", None))
            | Some a -> (match a with [ItemB (u,v, SUK [ItemFactor (SUKItem (la,kl,ty))])]
              -> (match kl with [ItemKl (SUBigBag (SUK
                          [ItemFactor (SUKItem
                  (SUKLabel (ConstToLabel (IntConst laFirst)),klFirst,tyFirst))]));
                  ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel
                         (OtherLabel laSecond),klSecond,tySecond))]))] -> 
                     if (charListToString laSecond) = "success" then
                  (match klSecond with [ItemKl (SUBigBag (SUK
                          [ItemFactor term]));]
                     -> Output (int_of_string (printKInt laFirst), Good (cpsExpToString term))
                   | _ -> Output (0, Error (0, "unknown error.", None)))
                       else (match klSecond with 
                      [ItemKl (SUBigBag (SUK
                          [ItemFactor (SUKItem
                  (SUKLabel (ConstToLabel (IntConst laNext)),klNext,tyNext))]));
                  ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel
                        (ConstToLabel (StringConst laNext2)),klNext2,tyNext2))]));
                  ItemKl (SUBigBag (SUK [ItemFactor term]))]
                      -> Output (int_of_string (printKInt laFirst),
                                Error (int_of_string (printKInt laNext), charListToString laNext2,
                          (if int_of_string (printKInt laNext) = 0
                                     then None else Some (cpsExpToString term))))
                        | _ -> Output (0, Error (0, "unknown error.", None)))
                     | _ -> Output (0, Error (0, "unknown error.", None)))
                   | _ -> Output (0, Error (0, "unknown error.", None))));;





