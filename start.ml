#load "k.cmo";;
#load "lexer.cmo";;
#load "parser.cmo";;
open K;;
open K;;
open Parser;;
open Lexer;;

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

(*
let rec tokenToList s
     = match s with Connect (a,b) -> 
          (tokenToList a) @ (tokenToList b)
          | _ -> [s];;

let get_all_tokens_fun lexbuf = let rec g () =
    match Lexer.token lexbuf with EOF -> []
      | t -> (tokenToList t) @ g () in
      g ();;


let deflate = 
  let q = Queue.create () in
  fun lexbuf -> 
    if not (Queue.is_empty q) then Queue.pop q else   
      match Lexer.token lexbuf with 
        | EOF -> EOF 
        | tok -> (match tokenToList tok with [] -> EOF
              | [a] -> a
              | hd::t ->  List.iter (fun tok -> Queue.add tok q) t ; hd);;
*)


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
    | IntToString -> "'IntToString";;

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

let lexsee () = (get_all_tokens (combineString (read_file "eval.k")));;

let interpreta () = (Parser.main Lexer.token (Lexing.from_string (combineString (read_file "eval.k"))));;

let allEqual = {equal = (=)};;

let theGraph = subsortGraph {equal = (=)} (interpreta ());;

let typecorrects p = match p with Parsed (c, a,b,d) -> assignSortInRules {equal = (=)} {equal = (=)} b;;

let parsed = interpreta();;

let typedTerm = match typecorrects (interpreta()) with None -> [] | Some a -> a;;

let database = match collectDatabase (interpreta()) with None -> [] | Some a -> a;;

let allRules = match (tupleToRuleInParsed allEqual allEqual allEqual (interpreta())) with None -> []
                    | Some a -> a;;

let programState = match genProgramState allEqual allEqual allEqual (interpreta()) database (subsortGraph allEqual (interpreta())) with None -> []
                   | Some a -> a;;

