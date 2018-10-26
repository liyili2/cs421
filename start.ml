type result = Good of {more_steps:bool; last_rhs:string}
              | Error of {error_code:int; err_msg: string; wrong_step: string option};;

type output = Output of int * result;;

#load "k.cmo";;
#load "lexer.cmo";;
#load "parser.cmo";;
#load "cpsLexer.cmo";;
#load "cpsParser.cmo";;
open K;;
(*open K;;*)
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

let rec toInt x n = match x with K.One -> (intExp 2 n)
                       | Bit0 a -> toInt a (n + 1)
                       | Bit1 a -> (intExp 2 n) + (toInt a (n + 1));;

let parseKChar c = match c with K.Zero_char -> 0
      | K.Char x -> (toInt x 0);;

let rec charListToString c = match c with [] -> ""
            | a::al -> (Char.escaped (Char.chr (parseKChar a))) ^ charListToString al;;

let rec knatToInt a = match a with K.Zero_nat -> 0
                    | K.Suc x -> 1 + knatToInt x;;

let printKNat a = string_of_int (knatToInt a);;

let rec intExp x n = if n = 0 then 1 else x * (intExp x (n - 1));;

let rec toInt x n = match x with K.One -> (intExp 2 n)
                       | K.Bit0 a -> toInt a (n + 1)
                       | K.Bit1 a -> (intExp 2 n) + (toInt a (n + 1));;

let parseKChar c = match c with K.Zero_char -> 0
      | Char x -> (toInt x 0);;

let printKChar a = string_of_int (parseKChar a);;

let printKInt a = match a with K.Zero_int -> "0"
          | Pos x -> string_of_int (toInt x 0) 
          | Neg x -> string_of_int (- (toInt x 0));;

let printKChar a = string_of_int (parseKChar a);;

let charsToStringInMetaVar a = match a with K.FunHole -> "FunHole"
      | K.Generated x -> "Generated " ^ (printKNat x)
      | K.Defined x -> "Defined " ^ (charListToString x);;

let charsToStringInVar a = match a with K.LittleK -> "k"
      | K.OtherVar x -> (charListToString x);;

let featureToString a = match a with K.Multiplicity x -> 
       (match x with K.Star -> "multiplicity=*"
                 | K.Question -> "multiplicity=?")
       | K.Stream x -> (match x with K.Stdin -> "stream=stdin"
                 | K.Stdout -> "stream=stdout")
       | K.DotDotDot -> "...";;

let rec featureListToString l = match l with [] -> ""
           | a::al -> (featureToString a)^" "^(featureListToString al);;

let charsToStringInSort a = 
    match a with K.OtherSort x -> "Sort "^(charListToString x)
               | K.Bool -> "Bool" | K.K -> "K" | K.KItem -> "KItem"
              | K.KLabel -> "KLabel" | K.KResult -> "KResult" | K.KList -> "KList"
               | K.List -> "List" | K.Set -> "Set" | K.Map -> "Map"
              | K.Bag -> "Bag" | K.Top -> "Top" | K.Int -> "Int" | K.Float -> "Float"
               | K.Id -> "Id" | K.String -> "String";;

let rec charsToStringInSortsAux l = match l with [] -> "]"
            | a::al -> (charsToStringInSort a) ^ ","^ (charsToStringInSortsAux al);;
let charsToStringInSorts l = "["^ charsToStringInSortsAux l;;

let printConst a = match a with K.IntConst x -> printKInt x
              | K.FloatConst x -> "Float"
              | K.StringConst x -> charListToString x
              | K.BoolConst x -> if x = true then "true" else "false"
              | K.IdConst x -> "$"^charListToString x;;

let charsToStringInLabel a = 
    match a with K.UnitLabel x -> "."^(charsToStringInSort x)
       | K.ConstToLabel x -> "'"^ (printConst x)
    | K.Sort -> "'Sort" | K.GetKLabel -> "'GetKLabel"
    | K.IsKResult -> "'IsKResult" | K.AndBool -> "'AndBool"
    | K.NotBool -> "'NotBool" | K.OrBool -> "'OrBool"
    | K.SetConLabel -> "'SetConLabel" | K.SetItemLabel -> "'SetItemLabel"
    | K.ListConLabel -> "'ListConLabel" | K.ListItemLabel -> "'ListItemLabel"
    | K.MapConLabel -> "'MapConLabel" | K.MapItemLabel -> "'MapItemLabel"
    | K.MapUpdate -> "'MapUpdate" | K.EqualK -> "'EqualK"
    | K.NotEqualK -> "'NotEqualK" | K.EqualKLabel -> "'EqualKLabel"
    | K.NotEqualKLabel -> "'NotEqualKLabel"
    | K.OtherLabel x -> "'"^ (charListToString x)
    | K.TokenLabel x -> "'"^ (charListToString x)
    | K.PlusInt -> "'PlusInt" | K.MinusInt -> "'MinusInt"
    | K.TimesInt -> "'TimesInt" | K.EqualSet -> "'EqualSet"
    | K.EqualMap -> "'EqualMap" | K.StringCon -> "'StringCon"
    | K.IntToString -> "'IntToString"
    | K.LessInt -> "'<Int"
    | K.LessEqualInt -> "'<=Int"
    | K.DivInt -> "/Int" | K.ModInt -> "%Int" | K.PlusFloat -> "+Float"
    | K.MinusFloat -> "-Float" | K.TimesFloat -> "*Float"
    | K.DivFloat -> "/Float" | K.GtInt -> ">Int" | K.GeqInt -> ">=Int"
    | K.LessFloat -> "<Float" | K.LessEqualFloat -> "<=Float"
    | K.GtFloat -> ">Float" | K.GeqFloat -> ">=Float";;

let rec charsToStringInSUBigKWithBag a =
     match a with K.SUK al -> "SUK" ^ " [" ^ (charsToStringInSUKFactorList al) ^ "]"
          | K.SUList al -> "SUList"^ " [" ^ (charsToStringInSUList al)^ "]"
          | K.SUSet al -> "SUSet"^ " [" ^(charsToStringInSUSet al)^ "]"
          | K.SUMap al -> "SUMap"^ " [" ^ (charsToStringInSUMap al)^ "]"
          | K.SUBag al -> "SUBag"^ " [" ^ (charsToStringInSUBag al)^ "]"
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
      match a with K.SUBigBag al ->  (charsToStringInSUBigKWithBag al)
               | K.SUBigLabel al -> (charsToStringInSUKLabel al)
and charsToStringInSUKFactor a =
      match a with K.ItemFactor a -> (charsToStringInSUKItem a)
          | K.IdFactor a -> "IdFactor "^ (charsToStringInMetaVar a)
          | K.SUKKItem (x,y,z) -> "SUKKItem ("^(charsToStringInSUKLabel x)^", "
                      ^(charsToStringInSUKList y) ^", "^ (charsToStringInSorts z)^")"
and charsToStringInSUS a =
     match a with K.ItemS x -> "SetItem("^(charsToStringInSUKFactorList x)^")"
               | K.IdS x -> "IdS "^(charsToStringInMetaVar x)
               | K.SUSetKItem (x,y) ->
                     "SUSetKItem ("^charsToStringInSUKLabel x^", "^charsToStringInSUKList y^")"
and charsToStringInSUL a =
     match a with K.ItemL x -> "ListItem("^(charsToStringInSUKFactorList x)^")"
               | K.IdL x -> "IdL "^(charsToStringInMetaVar x)
               | K.SUListKItem (x,y) ->
                     "SUListKItem ("^charsToStringInSUKLabel x^", "^charsToStringInSUKList y^")"
and charsToStringInSUM a =
     match a with K.ItemM (x,y) -> "("^charsToStringInSUKFactorList x^
                                " |-> "^charsToStringInSUKFactorList y^")"
               | K.IdM x -> "IdM "^(charsToStringInMetaVar x)
               | K.SUMapKItem (x,y) ->
                     "SUMapKItem ("^charsToStringInSUKLabel x^", "^charsToStringInSUKList y^")"
and charsToStringInSUBag l = match l with [] -> ".Bag"
            | a::al -> (charsToStringInSUB a)^", "^(charsToStringInSUBag al)
and charsToStringInSUB a = match a with 
          K.ItemB (x,y,z) -> "<"^charsToStringInVar x^", "
                        ^featureListToString y^"> "^charsToStringInSUBigKWithBag z
                                ^" </"^charsToStringInVar x^">"
         | K.IdB x -> "IdB "^(charsToStringInMetaVar x)
and charsToStringInSUKList l = match l with [] -> ".KList"
            | a::al -> (charsToStringInSUKL a)^",, "^(charsToStringInSUKList al)
and charsToStringInSUKL a = match a with
        K.ItemKl x -> ""^(charsToStringInSUBigKWithLabel x)
       | IdKl x -> "IdKl "^(charsToStringInMetaVar x)
and charsToStringInSUKLabel a = match a with
       K.SUKLabel x -> (charsToStringInLabel x)
     | K.SUIdKLabel x -> "SUIdKLabel "^(charsToStringInMetaVar x)
     | K.SUKLabelFun (x,y) -> "SUKLabelFun ("^charsToStringInSUKLabel x^", "^charsToStringInSUKList y^")"
and charsToStringInSUKItem a = match a with
      K.SUKItem (x,y,z) -> charsToStringInSUKLabel x^"("^ 
                   charsToStringInSUKList y^")::"^charsToStringInSorts z
    | K.SUIdKItem (x,y) ->  charsToStringInMetaVar x^"::"^charsToStringInSorts y
    | K.SUHOLE x -> "HOLE "^(charsToStringInSorts x);;

let charsToStringInState a = match a with
     K.Continue x -> "Continue ("^charsToStringInSUBag x^")"
   | K.Stop x -> "Stop ("^charsToStringInSUBag x^")"
   | K.Div x -> "Div ("^charsToStringInSUBag x^")";;

let charsToStringInSubsFactor a = match a with
     K.KLabelSubs x -> charsToStringInSUKLabel x
   | K.KItemSubs x -> charsToStringInSUKItem x
   | K.KListSubs x -> charsToStringInSUKList x
   | K.KSubs x -> charsToStringInSUKFactorList x
   | K.ListSubs x -> charsToStringInSUList x
   | K.MapSubs x -> charsToStringInSUMap x
   | K.SetSubs x -> charsToStringInSUSet x
   | K.BagSubs x -> charsToStringInSUBag x;;

let rec charsToStringInSubstList l = match l with [] -> []
    | ((x,y)::al) -> (charsToStringInMetaVar x, charsToStringInSubsFactor y)::(charsToStringInSubstList al);;

let rec charsToStringInSubstListList l = match l with [] -> []
       | (a::al) -> (charsToStringInSubstList a)::(charsToStringInSubstListList al);;

let lexsee () = (get_all_tokens (combineString (read_file "cspapp.k")));;

let interpreta () = (Parser.main Lexer.token (Lexing.from_string (combineString (read_file "cspapp.k"))));;

let allEqual = {K.equal = (=)};;

let theGraph = K.subsortGraph {K.equal = (=)} (interpreta ());;

let typecorrects p = match p with K.Parsed (c, a,b,d) -> K.assignSortInRules {K.equal = (=)} {K.equal = (=)} b;;

let parsed = interpreta();;

let typedTerm = match typecorrects (interpreta()) with None -> [] | Some a -> a;;

let database = match K.collectDatabase (interpreta()) with None -> [] | Some a -> a;;

let allRules = match (K.tupleToRuleInParsed allEqual allEqual allEqual (interpreta())) with None -> []
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

let confi = match parsed with K.Parsed (Some a,b,c,d) -> a;;

(* let program = match readInProgram "f x" with K.Parsed (a, b,c, Some d) -> d;; *)

let programState s = match parseCPS s with None -> None
      | Some s' -> (match readInProgram s' with None -> None
      | Some (K.Parsed (a,b,c,d)) -> 
       (match parsed with K.Parsed (x,y,u,v) -> 
       K.genProgramState allEqual allEqual allEqual (K.Parsed (x,y,u,d)) database theGraph));;

let _ = K.typeCheckRules allEqual allEqual allRules database theGraph;;

let testResult = match K.genProgramState allEqual allEqual allEqual parsed database theGraph with None -> None
              | Some p -> (match K.funEvaluation allEqual allEqual allEqual allRules database theGraph p with None -> Some "" | Some a -> Some (charsToStringInSUBag a));;

let printFloat s = match s with K.Ratreal (Frct (x,y)) -> (printKInt x)^"."^(printKInt y);;

let rec cpsExpToString t = match t with K.SUKItem ((K.SUKLabel x),y,z) -> 
       (match x with (K.OtherLabel l) -> if charListToString l = "if"
                 then (match y with [K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub1]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub2]));
                   K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub3]))]
                   -> "if "^(cpsExpToString sub1)^" then "^(cpsExpToString sub2)
                         ^" else "^(cpsExpToString sub3) | _ -> "bad")
                 else if  charListToString l = "bigIf"
                  then (match y with [K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub1]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub2]));
                   K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub3]))]
                   -> "IF "^(cpsExpToString sub1)^" THEN "^(cpsExpToString sub2)
                         ^" ELSE "^(cpsExpToString sub3) | _ -> "bad")
                 else if  charListToString l = "app"
                  then (match y with [K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub1]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub2]))]
                   -> (cpsExpToString sub1)^"("^(cpsExpToString sub2)^")" | _ -> "bad")
                 else if  charListToString l = "bin"
                  then (match y with [K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub1]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub2]));
                    K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub3]))]
                   -> "("^(cpsExpToString sub2)^") "^(cpsExpToString sub1)^" ("^(cpsExpToString sub3)^")"
                          | _ -> "bad")
                 else if  charListToString l = "unary"
                  then (match y with [K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub1]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub2]))]
                   -> (cpsExpToString sub1)^"("^(cpsExpToString sub2)^")"
                          | _ -> "bad")
                 else if  charListToString l = "fun"
                  then (match y with [K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub1]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub2]))]
                   -> "fun "^(cpsExpToString sub1)^" -> ("^(cpsExpToString sub2)^")"
                          | _ -> "bad")
                 else if  charListToString l = "fn"
                  then (match y with [K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub1]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub2]))]
                   -> "FN "^(cpsExpToString sub1)^" -> ("^(cpsExpToString sub2)^")"
                          | _ -> "bad")
                 else if  charListToString l = "bigFun"
                  then (match y with [K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub1]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub2]));
                     K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub3]))]
                   -> "FUN "^(cpsExpToString sub1)^" "^(cpsExpToString sub2)
                               ^" -> ("^(cpsExpToString sub3)^")"
                          | _ -> "bad")
                 else if  charListToString l = "let"
                  then (match y with [K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub1]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub2]));
                     K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub3]))]
                   -> "let "^(cpsExpToString sub1)^" = "^(cpsExpToString sub2)
                               ^" in ("^(cpsExpToString sub3)^")"
                          | _ -> "bad")
                 else if  charListToString l = "trans"
                  then (match y with [K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub1]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor sub2]))]
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
                 else if  charListToString l = "genId" then
                     (match y with [K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor
                    (K.SUKItem (K.SUKLabel (ConstToLabel (IntConst sub1)),kl1,ty1))]))]
                   -> "genId"^(printKInt sub1) | _ -> "bad")
                 else "bad"
             | ConstToLabel (IntConst l) ->  printKInt l
              | ConstToLabel (FloatConst l) ->  printFloat l
              |  ConstToLabel (IdConst l) ->  charListToString l
             | _ -> "bad")
                   | _ -> "bad";;

(* a function to print the next step *)
let getNextStep s = match programState s with None -> None
     | Some x -> (match x with [K.ItemB (u,v, K.SUK
              [K.ItemFactor (K.SUKItem (la,kl,ty))])] ->
            (match kl with [kl1; kl2; kl3] ->
         (match K.funEvaluation allEqual allEqual allEqual allRules database theGraph [K.ItemB (u,v, K.SUK
              [K.ItemFactor (K.SUKItem (K.SUKLabel (K.OtherLabel (parseString "getOneStep")),[kl2],ty))])]
             with None -> None | Some a -> (match a with 
          [K.ItemB (u,v, K.SUK [K.ItemFactor term])] -> Some (cpsExpToString term)
           | _ -> None)) | _ -> None) | _ -> None);;

(* error 0 for parsing error, 1 for rule error, 2 for rule name error. *)
let runCPS s = match programState s with None ->
  Output (0, Error{error_code=0; err_msg="Student has a parsing error"; wrong_step = None})
        | Some x -> (match K.funEvaluation allEqual allEqual allEqual allRules database theGraph x
         with None -> Output (0, Error {error_code = 0; err_msg = "unknown error."; wrong_step = None})
            | Some a -> (match a with [K.ItemB (u,v, K.SUK [K.ItemFactor (K.SUKItem (la,kl,ty))])]
              -> (match kl with [K.ItemKl (K.SUBigBag (K.SUK
                          [K.ItemFactor (K.SUKItem
                  (K.SUKLabel (ConstToLabel (IntConst laFirst)),klFirst,tyFirst))]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor (K.SUKItem (K.SUKLabel
                         (K.OtherLabel laSecond),klSecond,tySecond))]))] -> 
                     if (charListToString laSecond) = "success" then
                  (match klSecond with [K.ItemKl (K.SUBigBag (K.SUK
                          [K.ItemFactor (K.SUKItem
                  (K.SUKLabel (ConstToLabel (BoolConst klSecondLa)),klSecondNe,klSecondTy))]));
                      K.ItemKl (K.SUBigBag (K.SUK
                          [K.ItemFactor term]))]
                      -> Output (int_of_string (printKInt laFirst),
                                 Good {more_steps = klSecondLa;last_rhs = cpsExpToString term})
                   | _ -> Output (0, Error {error_code =0; err_msg = "unknown error."; wrong_step = None}))
                       else (match klSecond with 
                      [K.ItemKl (K.SUBigBag (K.SUK
                          [K.ItemFactor (K.SUKItem
                  (K.SUKLabel (ConstToLabel (IntConst laNext)),klNext,tyNext))]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor (K.SUKItem (K.SUKLabel
                        (ConstToLabel (StringConst laNext2)),klNext2,tyNext2))]));
                  K.ItemKl (K.SUBigBag (K.SUK [K.ItemFactor term]))]
                      -> Output (int_of_string (printKInt laFirst),
                                 Error {error_code = int_of_string (printKInt laNext);
                                        err_msg = charListToString laNext2;
                          wrong_step = (if int_of_string (printKInt laNext) = 0
                                     then None else Some (cpsExpToString term))})
                        | _ -> Output (0, Error {error_code = 0; err_msg = "unknown error."; wrong_step = None}))
                     | _ -> Output (0, Error {error_code = 0; err_msg = "unknown error."; wrong_step = None}))
                   | _ -> Output (0, Error {error_code = 0; err_msg = "unknown error."; wrong_step = None})));;





