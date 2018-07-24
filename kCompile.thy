theory kCompile
imports Main Real List kSort
begin

(* this file defines the k core to k IR translation *)

(* configuration checks *)
fun uniqueCellNameInSUBigKWithBag :: "('upVar, 'var, 'metaVar) suBigKWithBag
       \<Rightarrow> 'var var list \<Rightarrow> 'var var list option"
    and uniqueCellNameInSUBag :: "('upVar, 'var, 'metaVar) suB list 
       \<Rightarrow> 'var var list \<Rightarrow> 'var var list option" where
"uniqueCellNameInSUBag [] A = Some A"
| "uniqueCellNameInSUBag (b#l) A = (case b of ItemB x y z \<Rightarrow>
            if x \<in> set A then None else
          (case uniqueCellNameInSUBigKWithBag z (x#A) of None \<Rightarrow> None
              | Some A' \<Rightarrow> uniqueCellNameInSUBag l A')
        | IdB x \<Rightarrow> uniqueCellNameInSUBag l A)"
| "uniqueCellNameInSUBigKWithBag (SUK a) A = Some A"
| "uniqueCellNameInSUBigKWithBag (SUList a) A = Some A"
| "uniqueCellNameInSUBigKWithBag (SUSet a) A = Some A"
| "uniqueCellNameInSUBigKWithBag (SUMap a) A = Some A"
| "uniqueCellNameInSUBigKWithBag (SUBag a) A = uniqueCellNameInSUBag a A"

fun hasNoBagVarInSUBag :: "('upVar, 'var, 'metaVar) suB list \<Rightarrow> bool"
and hasNoBagVarInSUBigKWithBag :: "('upVar, 'var, 'metaVar)
                              suBigKWithBag \<Rightarrow> bool" where
"hasNoBagVarInSUBag [] = True"
| "hasNoBagVarInSUBag (b#l) = (case b of IdB x \<Rightarrow> False
            | _ \<Rightarrow> hasNoBagVarInSUBag l)"
| "hasNoBagVarInSUBigKWithBag (SUBag a) = hasNoBagVarInSUBag a"
| "hasNoBagVarInSUBigKWithBag a = True"

fun noDotInSUBag :: "('upVar, 'var, 'metaVar) suB list \<Rightarrow> bool"
and noDotInSUBigKWithBag :: "('upVar, 'var, 'metaVar)
                              suBigKWithBag \<Rightarrow> bool" where
"noDotInSUBag [] = True"
| "noDotInSUBag (b#l) = (case b of IdB x \<Rightarrow> noDotInSUBag l
         | ItemB x y z \<Rightarrow> if DotDotDot \<in> set y then False
               else (noDotInSUBigKWithBag z \<and> noDotInSUBag l))"
| "noDotInSUBigKWithBag (SUBag a) = noDotInSUBag a"
| "noDotInSUBigKWithBag a = True"

(* if a context rule has rewrites, then the rewrite must be on rewriting a hole to other items*)
primrec validContextInKLabel :: "('upVar, 'var, 'metaVar) kLabel \<Rightarrow> bool"
    and validContextInKLabelR :: "('upVar, 'var, 'metaVar) kLabel rewrite \<Rightarrow> bool"
    and validContextInKItem :: "('upVar, 'var, 'metaVar) kItem \<Rightarrow> bool"
    and validContextInKItemR :: "('upVar, 'var, 'metaVar) kItem rewrite \<Rightarrow> bool"
    and validContextInKList :: "('upVar, 'var, 'metaVar) kList \<Rightarrow> bool"
    and validContextInKListR :: "('upVar, 'var, 'metaVar) kList rewrite \<Rightarrow> bool"
    and validContextInK :: "('upVar, 'var, 'metaVar) k \<Rightarrow> bool"
    and validContextInKR :: "('upVar, 'var, 'metaVar) k rewrite \<Rightarrow> bool"
    and validContextInList :: "('upVar, 'var, 'metaVar) theList \<Rightarrow> bool"
    and validContextInListR :: "('upVar, 'var, 'metaVar) theList rewrite \<Rightarrow> bool"
    and validContextInSet :: "('upVar, 'var, 'metaVar) theSet \<Rightarrow> bool"
    and validContextInSetR :: "('upVar, 'var, 'metaVar) theSet rewrite \<Rightarrow> bool"
    and validContextInMap :: "('upVar, 'var, 'metaVar) theMap \<Rightarrow> bool"
    and validContextInMapR :: "('upVar, 'var, 'metaVar) theMap rewrite \<Rightarrow> bool"
    and validContextInBigKWithBag :: "('upVar, 'var, 'metaVar) bigKWithBag \<Rightarrow> bool"
    and validContextInBigK :: "('upVar, 'var, 'metaVar) bigK \<Rightarrow> bool"
    and validContextInBag :: "('upVar, 'var, 'metaVar) bag \<Rightarrow> bool"
    and validContextInBagR :: "('upVar, 'var, 'metaVar) bag rewrite \<Rightarrow> bool"
 where
  "validContextInKLabel (KLabelC a) = True"
| "validContextInKLabel (KLabelFun a b) = (validContextInKLabel a \<and> validContextInKListR b)"
| "validContextInKLabel (IdKLabel n) = True"
| "validContextInKLabelR (KTerm n) = validContextInKLabel n"
| "validContextInKLabelR (KRewrite l r) = False"
| "validContextInKItem (KItemC l r ty) = (validContextInKLabelR l \<and> validContextInKListR r)"
| "validContextInKItem (Constant a b) = True"
| "validContextInKItem (IdKItem a b) = True"
| "validContextInKItem (HOLE a) = True"
| "validContextInKItemR (KTerm t) = validContextInKItem t"
| "validContextInKItemR (KRewrite l r) = (case l of HOLE a \<Rightarrow> True
                                                      | _ \<Rightarrow> False)"
| "validContextInKList (KListCon b t) = ((validContextInKListR b) \<and> (validContextInKListR t))"
| "validContextInKList UnitKList = True"
| "validContextInKList (KListItem a) = (validContextInBigKWithBag a)"
| "validContextInKList (IdKList a) = True"
| "validContextInKListR (KTerm t) = validContextInKList t"
| "validContextInKListR (KRewrite l r) = False"
| "validContextInBigKWithBag (TheBigK a) = validContextInBigK a"
| "validContextInBigKWithBag (TheBigBag b) = validContextInBagR b"
| "validContextInBigKWithBag (TheLabel b) = validContextInKLabelR b"
| "validContextInBigK (TheK t) = validContextInKR t"
| "validContextInBigK (TheList t) = validContextInListR t"
| "validContextInBigK (TheSet t) = validContextInSetR t"
| "validContextInBigK (TheMap t) = validContextInMapR t"
| "validContextInK (Tilda a t) = ((validContextInKR a) \<and> (validContextInKR t))"
| "validContextInK UnitK = True"
| "validContextInK (SingleK a) = validContextInKItemR a"
| "validContextInK (IdK a) = True"
| "validContextInK (KFun l r) = (validContextInKLabel l \<and> validContextInKListR r)"
| "validContextInKR (KTerm a) = (validContextInK a)"
| "validContextInKR (KRewrite l r) = False"
| "validContextInList (ListCon l r) = ((validContextInListR l) \<and> (validContextInListR r))"
| "validContextInList UnitList = True"
| "validContextInList (IdList a) = True"
| "validContextInList (ListItem a) = validContextInKR a"
| "validContextInList (ListFun l r) = (validContextInKLabel l \<and> validContextInKListR r)"
| "validContextInListR (KTerm a) = (validContextInList a)"
| "validContextInListR (KRewrite l r) = False"
| "validContextInSet (SetCon l r) = ((validContextInSetR l) \<and> (validContextInSetR r))"
| "validContextInSet UnitSet = True"
| "validContextInSet (IdSet a) = True"
| "validContextInSet (SetItem a) = validContextInKR a"
| "validContextInSet (SetFun l r) = (validContextInKLabel l \<and> validContextInKListR r)"
| "validContextInSetR (KTerm a) = (validContextInSet a)"
| "validContextInSetR (KRewrite l r) = False"
| "validContextInMap (MapCon l r) = ((validContextInMapR l) \<and> (validContextInMapR r))"
| "validContextInMap UnitMap = True"
| "validContextInMap (IdMap a) = True"
| "validContextInMap (MapItem l r) = (validContextInKR l \<and> validContextInKR r)"
| "validContextInMap (MapFun l r) = (validContextInKLabel l \<and> validContextInKListR r)"
| "validContextInMapR (KTerm a) = (validContextInMap a)"
| "validContextInMapR (KRewrite l r) = False"
| "validContextInBag (BagCon l r) =((validContextInBagR l) \<and> (validContextInBagR r))"
| "validContextInBag UnitBag = True"
| "validContextInBag (IdBag a) = True"
| "validContextInBag (Xml a n t) =  validContextInBagR t"
| "validContextInBag (SingleCell a n t) =  validContextInBigK t"
| "validContextInBagR (KTerm a) = (validContextInBag a)"
| "validContextInBagR (KRewrite l r) = False"

fun mapLookup ::
     "'a \<Rightarrow> ('a * 'b) list
            \<Rightarrow> 'b option" where
"mapLookup x [] = None"
| "mapLookup x ((a,b)#l) = (if x = a then Some b else mapLookup x l)"

primrec isElement :: "'c \<Rightarrow> ('a * 'b * 'c KItemSyntax) list \<Rightarrow> bool" where
"isElement a [] = False"
| "isElement a (h#l) = (case h of (x,y, SingleTon z) \<Rightarrow> if a = z then True else
                        isElement a l | (x,y, SetTon s) \<Rightarrow> if s a then True else
                        isElement a l)"


fun hasHoleInIRKItem :: "('upVar, 'var, 'metaVar) irKItem \<Rightarrow> bool"
    and hasHoleInIRKList :: "('upVar, 'var, 'metaVar) irKList \<Rightarrow> bool"
    and hasHoleInIRK :: "('upVar, 'var, 'metaVar) irK \<Rightarrow> bool"
    and hasHoleInIRList :: "('upVar, 'var, 'metaVar) irList \<Rightarrow> bool"
    and hasHoleInIRSet :: "('upVar, 'var, 'metaVar) irSet \<Rightarrow> bool"
    and hasHoleInIRMap :: "('upVar, 'var, 'metaVar) irMap \<Rightarrow> bool"
    and hasHoleInIRBigKWithBag :: "('upVar, 'var, 'metaVar) irBigKWithBag \<Rightarrow> bool"
    and hasHoleInIRBigKWithLabel ::
             "('upVar, 'var, 'metaVar) irBigKWithLabel \<Rightarrow> bool"
    and hasHoleInIRBag :: "('upVar, 'var, 'metaVar) irBag \<Rightarrow> bool"
 where 
 "hasHoleInIRKItem (IRKItem l r ty) = (hasHoleInIRKList r)"
| "hasHoleInIRKItem (IRIdKItem a b) = False"
| "hasHoleInIRKItem (IRHOLE a) = True"
| "hasHoleInIRKList (KListPatNoVar l) =
                    foldl (\<lambda> b t . b \<or> hasHoleInIRBigKWithLabel t) False (l)"
| "hasHoleInIRKList (KListPat l a r) =
                    foldl (\<lambda> b t . b \<or> hasHoleInIRBigKWithLabel t) False (l@r)"
| "hasHoleInIRBigKWithBag (IRK a) = hasHoleInIRK a"
| "hasHoleInIRBigKWithBag (IRList a) = hasHoleInIRList a"
| "hasHoleInIRBigKWithBag (IRSet a) = hasHoleInIRSet a"
| "hasHoleInIRBigKWithBag (IRMap a) = hasHoleInIRMap a"
| "hasHoleInIRBigKWithBag (IRBag a) = hasHoleInIRBag a"
| "hasHoleInIRBigKWithLabel (IRBigBag a) = hasHoleInIRBigKWithBag a"
| "hasHoleInIRBigKWithLabel (IRBigLabel a) = False"
| "hasHoleInIRK (KPat l a) = foldl (\<lambda> b t . b \<or> hasHoleInIRKItem t) False l"
| "hasHoleInIRList (ListPatNoVar l) = foldl (\<lambda> b t . b \<or> hasHoleInIRK t) False (l)"
| "hasHoleInIRList (ListPat l a r) = foldl (\<lambda> b t . b \<or> hasHoleInIRK t) False (l@r)"
| "hasHoleInIRSet (SetPat l a) = foldl (\<lambda> b t . b \<or> hasHoleInIRK t) False l"
| "hasHoleInIRMap (MapPat l a) = foldl (\<lambda> b t . case t of (x,y) \<Rightarrow>
                           b \<or> hasHoleInIRK x \<or> hasHoleInIRK y) False l"
| "hasHoleInIRBag (BagPat l a) = foldl (\<lambda> b t . case t of (x,y,z) \<Rightarrow>
                           b \<or> hasHoleInIRBigKWithBag z) False l"

primrec hasHoleInMatchFactor :: "('upVar, 'var, 'metaVar) matchFactor \<Rightarrow> bool"
where
"hasHoleInMatchFactor (KLabelMatching a) = False"
| "hasHoleInMatchFactor (KItemMatching a) = hasHoleInIRKItem a"
| "hasHoleInMatchFactor (KListMatching a) = hasHoleInIRKList a"
| "hasHoleInMatchFactor (KMatching a) = hasHoleInIRK a"
| "hasHoleInMatchFactor (ListMatching a) = hasHoleInIRList a"
| "hasHoleInMatchFactor (SetMatching a) = hasHoleInIRSet a"
| "hasHoleInMatchFactor (MapMatching a) = hasHoleInIRMap a"
| "hasHoleInMatchFactor (BagMatching a) = hasHoleInIRBag a"

primrec hasHoleInPat :: "('upVar, 'var, 'metaVar) pat \<Rightarrow> bool" where
"hasHoleInPat (KLabelFunPat a b) = hasHoleInIRKList b"
| "hasHoleInPat (KFunPat a b) = hasHoleInIRKList b"
| "hasHoleInPat (KItemFunPat a b) = hasHoleInIRKList b"
| "hasHoleInPat (ListFunPat a b) = hasHoleInIRKList b"
| "hasHoleInPat (SetFunPat a b) = hasHoleInIRKList b"
| "hasHoleInPat (MapFunPat a b) = hasHoleInIRKList b"
| "hasHoleInPat (NormalPat b) = hasHoleInMatchFactor b"


fun hasHoleInSUKLabel :: "('upVar, 'var, 'metaVar) suKLabel \<Rightarrow> bool"
    and hasHoleInSUKItem :: "('upVar, 'var, 'metaVar) suKItem \<Rightarrow> bool"
    and hasHoleInSUKList :: "('upVar, 'var, 'metaVar) suKl list \<Rightarrow> bool"
    and hasHoleInSUK :: "('upVar, 'var, 'metaVar) suKFactor list \<Rightarrow> bool"
    and hasHoleInSUList :: "('upVar, 'var, 'metaVar) suL list \<Rightarrow> bool"
    and hasHoleInSUSet :: "('upVar, 'var, 'metaVar) suS list \<Rightarrow> bool"
    and hasHoleInSUMap :: "('upVar, 'var, 'metaVar) suM list \<Rightarrow> bool"
    and hasHoleInSUBigKWithBag :: "('upVar, 'var, 'metaVar) suBigKWithBag \<Rightarrow> bool"
    and hasHoleInSUBigKWithLabel ::
                     "('upVar, 'var, 'metaVar) suBigKWithLabel \<Rightarrow> bool"
    and hasHoleInSUBag :: "('upVar, 'var, 'metaVar) suB list \<Rightarrow> bool"
 where 
  "hasHoleInSUKLabel (SUKLabel a) = False"
| "hasHoleInSUKLabel (SUKLabelFun a b) = hasHoleInSUKList b"
| "hasHoleInSUKLabel (SUIdKLabel n) = False"
| "hasHoleInSUKItem (SUKItem l r ty) = ((hasHoleInSUKLabel l) \<or> (hasHoleInSUKList r))"
| "hasHoleInSUKItem (SUIdKItem a b) = False"
| "hasHoleInSUKItem (SUHOLE a) = True"
| "hasHoleInSUKList [] = False"
| "hasHoleInSUKList ((ItemKl t)#l) = (hasHoleInSUBigKWithLabel t \<or> hasHoleInSUKList l)"
| "hasHoleInSUKList ((IdKl t)#l) = hasHoleInSUKList l"
| "hasHoleInSUBigKWithBag (SUK a) = hasHoleInSUK a"
| "hasHoleInSUBigKWithBag (SUList a) = hasHoleInSUList a"
| "hasHoleInSUBigKWithBag (SUSet a) = hasHoleInSUSet a"
| "hasHoleInSUBigKWithBag (SUMap a) = hasHoleInSUMap a"
| "hasHoleInSUBigKWithBag (SUBag a) = hasHoleInSUBag a"
| "hasHoleInSUBigKWithLabel (SUBigBag a) = hasHoleInSUBigKWithBag a"
| "hasHoleInSUBigKWithLabel (SUBigLabel a) = hasHoleInSUKLabel a"
| "hasHoleInSUK [] = False"
| "hasHoleInSUK ((IdFactor t)#l) = hasHoleInSUK l"
| "hasHoleInSUK ((ItemFactor t)#l) = (hasHoleInSUKItem t \<or> hasHoleInSUK l)"
| "hasHoleInSUK ((SUKKItem a b ty)#l) = ((hasHoleInSUKLabel a)
                                   \<or> (hasHoleInSUKList b) \<or> hasHoleInSUK l)"
| "hasHoleInSUList [] = False"
| "hasHoleInSUList ((IdL t)#l) = hasHoleInSUList l"
| "hasHoleInSUList ((ItemL t)#l) = (hasHoleInSUK t \<or> hasHoleInSUList l)"
| "hasHoleInSUList ((SUListKItem a b)#l) = ((hasHoleInSUKLabel a)
                                   \<or> (hasHoleInSUKList b) \<or> hasHoleInSUList l)"
| "hasHoleInSUSet [] = False"
| "hasHoleInSUSet ((IdS t)#l) = hasHoleInSUSet l"
| "hasHoleInSUSet ((ItemS t)#l) = (hasHoleInSUK t \<or> hasHoleInSUSet l)"
| "hasHoleInSUSet ((SUSetKItem a b)#l) = ((hasHoleInSUKLabel a)
                                   \<or> (hasHoleInSUKList b) \<or> hasHoleInSUSet l)"
| "hasHoleInSUMap [] = False"
| "hasHoleInSUMap ((IdM t)#l) = hasHoleInSUMap l"
| "hasHoleInSUMap ((ItemM a b)#l) = ((hasHoleInSUK a)
                                   \<or> (hasHoleInSUK b) \<or> hasHoleInSUMap l)"
| "hasHoleInSUMap ((SUMapKItem a b)#l) = ((hasHoleInSUKLabel a)
                                   \<or> (hasHoleInSUKList b) \<or> hasHoleInSUMap l)"
| "hasHoleInSUBag [] = False"
| "hasHoleInSUBag ((IdB t)#l) = hasHoleInSUBag l"
| "hasHoleInSUBag ((ItemB x y z)#l) = (hasHoleInSUBigKWithBag z \<or> hasHoleInSUBag l)"

(* constant to klabels *)
definition isConstInKItem where
"isConstInKItem a = (case a of (IRKItem (IRKLabel s) kl ty) \<Rightarrow> isConst s
                      | _ \<Rightarrow> False)"

definition labelToConstInKItem where
"labelToConstInKItem a = (case a of (IRKItem (IRKLabel s) kl ty) \<Rightarrow> 
                         (labelToConst s) | _ \<Rightarrow> None)"
(*
definition functionKItems :: "('upVar * ('upVar, 'var, 'metaVar metaVar) kItem KItemSyntax) list" where
"functionKItems = syntaxSetToKItemSet (getAllFunctionsInSyntax (getAllSyntaxInKFile Theory))"
*)

(* get the core label by given a term *)
definition getSUKLabelMeaning  where
"getSUKLabelMeaning x = (case x of (SUKLabel a) \<Rightarrow> Some a | _ \<Rightarrow> None)"

definition getKLabelInSUKItem where
"getKLabelInSUKItem A = (case A of (SUKItem a b ty) \<Rightarrow> getSUKLabelMeaning a
                     | _ \<Rightarrow> None)"

definition getKLabelInSUK where
"getKLabelInSUK x = (case x of (SUKKItem a b ty) \<Rightarrow> getSUKLabelMeaning a
                          | _ \<Rightarrow> None)"

definition getKLabelInSUKS where
"getKLabelInSUKS x = (case x of [x'] \<Rightarrow> getKLabelInSUK x'
                          | _ \<Rightarrow> None)"

definition getKLabelInSUList where
"getKLabelInSUList x = (case x of (SUListKItem a b) \<Rightarrow> getSUKLabelMeaning a
                          | _ \<Rightarrow> None)"

definition getKLabelInSUListS where
"getKLabelInSUListS x = (case x of [x'] \<Rightarrow> getKLabelInSUList x'
                          | _ \<Rightarrow> None)"

definition getKLabelInSUSet where
"getKLabelInSUSet x = (case x of (SUSetKItem a b) \<Rightarrow> getSUKLabelMeaning a
                          | _ \<Rightarrow> None)"

definition getKLabelInSUSetS where
"getKLabelInSUSetS x = (case x of [x'] \<Rightarrow> getKLabelInSUSet x'
                          | _ \<Rightarrow> None)"

definition getKLabelInSUMap where
"getKLabelInSUMap x = (case x of (SUMapKItem a b) \<Rightarrow> getSUKLabelMeaning a
                          | _ \<Rightarrow> None)"

definition getKLabelInSUMapS where
"getKLabelInSUMapS x = (case x of [x'] \<Rightarrow> getKLabelInSUMap x'
                          | _ \<Rightarrow> None)"

definition getIRKLabel where
"getIRKLabel x = (case x of (IRKLabel a) \<Rightarrow> Some a | _ \<Rightarrow> None)"

definition getKLabelMeaning where
"getKLabelMeaning x = (case x of (KLabelC a) \<Rightarrow> Some a | _ \<Rightarrow> None)"

definition getKLabelInKLabelR where
"getKLabelInKLabelR x = (case x of (KTerm (KLabelC a))
                              \<Rightarrow> Some a | _ \<Rightarrow> None)"

definition getKLabelInIRKItem where
"getKLabelInIRKItem A = (case A of (IRKItem a b ty) \<Rightarrow> getIRKLabel a
                     | _ \<Rightarrow> None)"

(* giving a function term and check a term has a function label *)
definition FunctionTerms where
"FunctionTerms database =
 foldl (\<lambda> acc (a,b,c,nl,d) . if d then acc@[(a,b,c,nl,d)] else acc) [] (database)"

fun isFunctionItemAux where
"isFunctionItemAux [] s = False"
| "isFunctionItemAux ((a,b, SingleTon t, nl, True)#l) s =
     (if (t = s) then True else isFunctionItemAux l s)"
| "isFunctionItemAux ((a,b, SetTon t, nl, True)#l) s =
     (if (t s) then True else isFunctionItemAux l s)"
| "isFunctionItemAux ((a,b, t, nl, False)#l) s = isFunctionItemAux l s"

definition isFunctionItem where
"isFunctionItem s database = isFunctionItemAux database s"







(* giving a configuration and getting a initial program state of it. *)
primrec composeConfiAndProgInSUKLabel
    and composeConfiAndProgInSUKItem
    and composeConfiAndProgInSUKListElem
    and composeConfiAndProgInSUKList
    and composeConfiAndProgInSUKElem
    and composeConfiAndProgInSUK
    and composeConfiAndProgInSUListElem
    and composeConfiAndProgInSUList
    and composeConfiAndProgInSUSetElem
    and composeConfiAndProgInSUSet
    and composeConfiAndProgInSUMapElem
    and composeConfiAndProgInSUMap
    and composeConfiAndProgInSUBigKWithBag
    and composeConfiAndProgInSUBigKWithLabel
    and composeConfiAndProgInSUBagElem
    and composeConfiAndProgInSUBag where
  "composeConfiAndProgInSUKLabel (SUKLabel a) acc subG = Some (SUKLabel a)"
| "composeConfiAndProgInSUKLabel (SUKLabelFun a b) acc subG =
      (case composeConfiAndProgInSUKLabel a acc subG of None \<Rightarrow> None
         | Some a' \<Rightarrow> 
             (case composeConfiAndProgInSUKList b acc subG of None \<Rightarrow> None
         | Some b' \<Rightarrow> Some (SUKLabelFun a' b')))"
| "composeConfiAndProgInSUKLabel (SUIdKLabel n) acc subG =
       (case getValueTerm n acc of Some (KLabelSubs a) \<Rightarrow> Some a
         | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUKItem (SUKItem l r ty) acc subG =
    (case composeConfiAndProgInSUKLabel l acc subG of None \<Rightarrow> None
          | Some l' \<Rightarrow> (case composeConfiAndProgInSUKList r acc subG of
              None \<Rightarrow> None
             | Some r' \<Rightarrow> Some [ItemFactor (SUKItem l' r' ty)]))"
| "composeConfiAndProgInSUKItem (SUIdKItem a b) acc subG =
     (case getValueTerm a acc of
         Some (KItemSubs (SUKItem l' r' ty')) \<Rightarrow>
       if subsortList ty' b subG then Some [ItemFactor (SUKItem l' r' ty')] else None
        | Some (KItemSubs (SUHOLE ty)) \<Rightarrow> if subsortList ty b subG then
         Some [ItemFactor (SUHOLE ty)] else None
        | Some (KSubs a) \<Rightarrow> if b = [K] then Some a else None
        | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUKItem (SUHOLE a) acc subG = Some [ItemFactor (SUHOLE a)]"
| "composeConfiAndProgInSUKListElem (ItemKl s) acc subG =
     (case composeConfiAndProgInSUBigKWithLabel s acc subG of None \<Rightarrow> None
          | Some s' \<Rightarrow> Some [ItemKl s'])"
| "composeConfiAndProgInSUKListElem (IdKl s) acc subG =
    (case getValueTerm s acc of Some (KListSubs t) \<Rightarrow>
              Some t | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUKList [] acc subG = Some []"
| "composeConfiAndProgInSUKList (b#l) acc subG =
   (case composeConfiAndProgInSUKListElem b acc subG of None \<Rightarrow> None
     | Some a' \<Rightarrow> (case composeConfiAndProgInSUKList l acc subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some (a'@l')))"
| "composeConfiAndProgInSUBigKWithLabel (SUBigBag a) acc subG =
      (case composeConfiAndProgInSUBigKWithBag a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "composeConfiAndProgInSUBigKWithLabel (SUBigLabel a) acc subG =
      (case composeConfiAndProgInSUKLabel a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBigLabel a'))"
| "composeConfiAndProgInSUBigKWithBag (SUK a) acc subG =
      (case composeConfiAndProgInSUK a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUK a'))"
| "composeConfiAndProgInSUBigKWithBag (SUList a) acc subG =
      (case composeConfiAndProgInSUList a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUList a'))"
| "composeConfiAndProgInSUBigKWithBag (SUSet a) acc subG =
      (case composeConfiAndProgInSUSet a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUSet a'))"
| "composeConfiAndProgInSUBigKWithBag (SUMap a) acc subG =
      (case composeConfiAndProgInSUMap a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUMap a'))"
| "composeConfiAndProgInSUBigKWithBag (SUBag a) acc subG =
      (case composeConfiAndProgInSUBag a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBag a'))"
| "composeConfiAndProgInSUKElem (ItemFactor x) acc subG =
    composeConfiAndProgInSUKItem x acc subG"
| "composeConfiAndProgInSUKElem (IdFactor x) acc subG =
    (case getValueTerm x acc of Some (KSubs a) \<Rightarrow> Some a
              | Some (KItemSubs a) \<Rightarrow> Some [(ItemFactor a)] | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUKElem (SUKKItem x y z) acc subG =
    (case composeConfiAndProgInSUKLabel x acc subG of None \<Rightarrow> None
         | Some a' \<Rightarrow> (case composeConfiAndProgInSUKList y acc subG of None \<Rightarrow> None
         | Some b' \<Rightarrow> Some ([SUKKItem a' b' z])))"
| "composeConfiAndProgInSUK [] acc subG = Some []"
| "composeConfiAndProgInSUK (b#l) acc subG =
      (case composeConfiAndProgInSUKElem b acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> (case composeConfiAndProgInSUK l acc subG of None \<Rightarrow> None
    | Some l' \<Rightarrow> Some (b'@l')))"
| "composeConfiAndProgInSUListElem (ItemL x) acc subG =
    (case composeConfiAndProgInSUK x acc subG of None \<Rightarrow> None
        | Some x' \<Rightarrow> Some [ItemL x'])"
| "composeConfiAndProgInSUListElem (IdL x) acc subG =
    (case getValueTerm x acc of Some (ListSubs a) \<Rightarrow> Some a
      | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUListElem (SUListKItem x y) acc subG =
    (case composeConfiAndProgInSUKLabel x acc subG of None \<Rightarrow> None
         | Some a' \<Rightarrow> (case composeConfiAndProgInSUKList y acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> Some [SUListKItem a' b']))"
| "composeConfiAndProgInSUList [] acc subG = Some []"
| "composeConfiAndProgInSUList (b#l) acc subG =
      (case composeConfiAndProgInSUListElem b acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> (case composeConfiAndProgInSUList l acc subG of None \<Rightarrow> None
    | Some l' \<Rightarrow> Some (b'@l')))"
| "composeConfiAndProgInSUSetElem (ItemS x) acc subG =
    (case composeConfiAndProgInSUK x acc subG of None \<Rightarrow> None
        | Some x' \<Rightarrow> Some [ItemS x'])"
| "composeConfiAndProgInSUSetElem (IdS x) acc subG =
    (case getValueTerm x acc of Some (SetSubs a) \<Rightarrow> Some a
      | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUSetElem (SUSetKItem x y) acc subG =
    (case composeConfiAndProgInSUKLabel x acc subG of None \<Rightarrow> None
         | Some a' \<Rightarrow> (case composeConfiAndProgInSUKList y acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> Some [SUSetKItem a' b']))"
| "composeConfiAndProgInSUSet [] acc subG = Some []"
| "composeConfiAndProgInSUSet (b#l) acc subG =
    (case composeConfiAndProgInSUSetElem b acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> (case composeConfiAndProgInSUSet l acc subG of None \<Rightarrow> None
    | Some l' \<Rightarrow> Some (b'@l')))"
| "composeConfiAndProgInSUMapElem (ItemM x y) acc subG =
    (case composeConfiAndProgInSUK x acc subG of None \<Rightarrow> None
        | Some x' \<Rightarrow> (case composeConfiAndProgInSUK x acc subG of None \<Rightarrow> None
     | Some y' \<Rightarrow> Some [ItemM x' y']))"
| "composeConfiAndProgInSUMapElem (IdM x) acc subG =
    (case getValueTerm x acc of Some (MapSubs a) \<Rightarrow> Some a
      | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUMapElem (SUMapKItem x y) acc subG =
    (case composeConfiAndProgInSUKLabel x acc subG of None \<Rightarrow> None
         | Some a' \<Rightarrow> (case composeConfiAndProgInSUKList y acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> Some [SUMapKItem a' b']))"
| "composeConfiAndProgInSUMap [] acc subG = Some []"
| "composeConfiAndProgInSUMap (b#l) acc subG =
    (case composeConfiAndProgInSUMapElem b acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> (case composeConfiAndProgInSUMap l acc subG of None \<Rightarrow> None
    | Some l' \<Rightarrow> Some (b'@l')))"
| "composeConfiAndProgInSUBagElem (ItemB x y z) acc subG =
     (case composeConfiAndProgInSUBigKWithBag z acc subG of None \<Rightarrow> None
          | Some z' \<Rightarrow> Some [ItemB x y z'])"
| "composeConfiAndProgInSUBagElem (IdB s) acc subG =
    (case getValueTerm s acc of Some (BagSubs t) \<Rightarrow>
              Some t | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUBag [] acc subG = Some []"
| "composeConfiAndProgInSUBag (b#l) acc subG =
    (case composeConfiAndProgInSUBagElem b acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> (case composeConfiAndProgInSUBag l acc subG of None \<Rightarrow> None
    | Some l' \<Rightarrow> Some (b'@l')))"



(* normalizing step, checking if two elements are the same in a set or a map*)
primrec isCommonElemInSUSet where
"isCommonElemInSUSet a [] subG = False"
| "isCommonElemInSUSet a (b#l) subG =
        (case a of ItemS v \<Rightarrow> (case b of ItemS v' \<Rightarrow>
           (case syntacticMonoidInSUK v v' subG of None \<Rightarrow> (isCommonElemInSUSet a l subG)
             | Some va \<Rightarrow> True)
             | _ \<Rightarrow> (isCommonElemInSUSet a l subG))
          | IdS x \<Rightarrow> (case b of IdS x' \<Rightarrow>
                  if x = x' then True else (isCommonElemInSUSet a l subG)
                | _ \<Rightarrow> (isCommonElemInSUSet a l subG))
          | SUSetKItem x y \<Rightarrow>
              (case b of SUSetKItem x' y' \<Rightarrow>
               (case (syntacticMonoidInSUKLabel x x' subG, syntacticMonoidInSUKList y y' subG)
                 of (Some xa, Some ya) \<Rightarrow> True
                  | _ \<Rightarrow> (isCommonElemInSUSet a l subG))
                 | _ \<Rightarrow> (isCommonElemInSUSet a l subG)))"

primrec isCommonElemInSUMap where
"isCommonElemInSUMap a [] subG = False"
| "isCommonElemInSUMap a (b#l) subG =
        (case a of ItemM v w \<Rightarrow> (case b of ItemM v' w' \<Rightarrow>
           (case syntacticMonoidInSUK v v' subG of None \<Rightarrow>
             (isCommonElemInSUMap a l subG)
             | Some va \<Rightarrow> (case syntacticMonoidInSUK w w' subG of None \<Rightarrow>
             (isCommonElemInSUMap a l subG) | Some wa \<Rightarrow> True))
             | _ \<Rightarrow> (isCommonElemInSUMap a l subG))
          | IdM x \<Rightarrow> (case b of IdM x' \<Rightarrow>
                  if x = x' then True else (isCommonElemInSUMap a l subG)
                | _ \<Rightarrow> (isCommonElemInSUMap a l subG))
          | SUMapKItem x y \<Rightarrow>
              (case b of SUMapKItem x' y' \<Rightarrow>
               (case (syntacticMonoidInSUKLabel x x' subG, syntacticMonoidInSUKList y y' subG)
                 of (Some xa, Some ya) \<Rightarrow> True
                  | _ \<Rightarrow> (isCommonElemInSUMap a l subG))
                 | _ \<Rightarrow> (isCommonElemInSUMap a l subG)))"

primrec getValueInSUMap where
"getValueInSUMap a [] subG = None"
| "getValueInSUMap a (b#l) subG = (case b of ItemM x y \<Rightarrow>
         (case syntacticMonoidInSUK a x subG of None \<Rightarrow> getValueInSUMap a l subG
            | Some xa \<Rightarrow>  Some y)
              | IdM x \<Rightarrow> getValueInSUMap a l subG
              | SUMapKItem x y \<Rightarrow> getValueInSUMap a l subG)"



(* compiling strict rules and context rules *)
definition genKListByTypeListFactor where
"genKListByTypeListFactor ty newVar subG =
     (if subsortList ty [List] subG then
             (ItemKl (SUBigBag (SUList ([IdL ( newVar)]))))
     else if subsortList ty [Set] subG then
             (ItemKl (SUBigBag (SUSet ([IdS ( newVar)]))))
     else if subsortList ty [Map] subG then
             (ItemKl (SUBigBag (SUMap ([IdM ( newVar)]))))
     else if subsortList ty [Bag] subG then
             (ItemKl (SUBigLabel (SUIdKLabel ( newVar))))
     else if subsortList ty [KLabel] subG then
             (ItemKl (SUBigBag (SUBag ([IdB ( newVar)]))))
     else if ty = [K] then (ItemKl (SUBigBag (SUK ([IdFactor ( newVar)]))))
        else (ItemKl (SUBigBag (SUK ([ItemFactor (SUIdKItem ( newVar) ty)])))))"

primrec genKListByTypeList where
"genKListByTypeList [] vars subG = []"
| "genKListByTypeList (ty#l) vars subG = (case freshVar vars of newVar \<Rightarrow>
      (genKListByTypeListFactor ty newVar subG)#(genKListByTypeList l (newVar#vars) subG))"

definition genKItemByTypeList where
"genKItemByTypeList s sty l vars subG = SUKItem (SUKLabel s) (genKListByTypeList l vars subG) sty"

primrec splitHoleFromKList where
"splitHoleFromKList (c::nat) n [] = None"
| "splitHoleFromKList c n (b#l) = (if c = n then (case b of
      ItemKl (SUBigBag z) \<Rightarrow> (case z of SUK [IdFactor u] \<Rightarrow> 
       Some ((IdFactor u), (ItemKl (SUBigBag (SUK [ItemFactor (SUHOLE [K])])))#l)
          | SUK [ItemFactor (SUIdKItem u ty)] \<Rightarrow> 
        Some (ItemFactor (SUIdKItem u ty), (ItemKl (SUBigBag (SUK [ItemFactor (SUHOLE ty)])))#l)
           | _ \<Rightarrow> None) | _ \<Rightarrow> None)
       else (case splitHoleFromKList (c + 1) n l of None \<Rightarrow> None
                | Some (u, v) \<Rightarrow> Some (u, b#v)))"

primrec getTypeFromKList where
"getTypeFromKList (c::nat) n [] = None"
| "getTypeFromKList c n (b#l) = (if c = n then (case b of
         ItemKl (SUBigLabel a) \<Rightarrow> Some [KLabel]
     | ItemKl (SUBigBag (SUK [IdFactor a])) \<Rightarrow> Some [K]
      | ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem a ty)])) \<Rightarrow> Some ty
    | ItemKl (SUBigBag (SUSet a)) \<Rightarrow> Some [Set]
    | ItemKl (SUBigBag (SUList a)) \<Rightarrow> Some [List]
    | ItemKl (SUBigBag (SUMap a)) \<Rightarrow> Some [Map] 
    | ItemKl (SUBigBag (SUBag a)) \<Rightarrow> Some [Bag]
    | _ \<Rightarrow> None) else getTypeFromKList c n l)"

fun getMetaVar where
"getMetaVar (IdFactor x) = Some x"
| "getMetaVar (ItemFactor x) = (case x of SUIdKItem a b \<Rightarrow> Some a
                       | _ \<Rightarrow> None)"
| "getMetaVar x = None"

primrec genStrictRulesAux where
"genStrictRulesAux s sty [] newKList database subG = Some []"
| "genStrictRulesAux s sty  (n#l) newKList database subG =
  (case getTypeFromKList 1 n newKList of None \<Rightarrow> None
     | Some newTy \<Rightarrow> if subsortList newTy [K] subG then 
    (case splitHoleFromKList 1 n newKList of None \<Rightarrow> None
       | Some (front, kl') \<Rightarrow> (case genStrictRulesAux s sty l newKList database subG
      of None \<Rightarrow> None | Some rl \<Rightarrow>
   (case freshVar (getAllMetaVarsInSUKList newKList) of newVar \<Rightarrow>
   (case suToIRInKList newKList database of Some left \<Rightarrow>
    (case suToIRInKList kl' database of Some left' \<Rightarrow>
    (case getMetaVar front of None \<Rightarrow> None | Some frontVar \<Rightarrow>
        Some ((KRulePat (KPat [IRKItem (IRKLabel s) left sty] (Some ( newVar))) 
           [front, ItemFactor (SUKItem (SUKLabel s) kl' sty), IdFactor (newVar)]
         (SUKItem (SUKLabel NotBool)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
                                 [ItemKl (SUBigBag (SUK [front]))] [Bool])]))] [Bool]) False)#
     (KRulePat (KPat [IRIdKItem frontVar [KResult],
             IRKItem (IRKLabel s) left' sty] (Some (newVar)))
           [ItemFactor (SUKItem (SUKLabel s) newKList sty), IdFactor (newVar)]
         (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#rl))
     | _ \<Rightarrow> None) | _ \<Rightarrow> None)))) else genStrictRulesAux s sty l newKList database subG)"

primrec genKListByTypeListInSeq where
"genKListByTypeListInSeq c n [] vars subG = []"
| "genKListByTypeListInSeq c n (ty#l) vars subG =
   (case freshVar vars of newVar \<Rightarrow>
    (if c < n \<and> subsortList ty [K] subG then
           ((ItemKl (SUBigBag (SUK ([ItemFactor (SUIdKItem ( newVar) [KResult])]))))
               # genKListByTypeListInSeq (c + 1) n l (( newVar)#vars) subG)
  else (genKListByTypeListFactor ty newVar subG)
        # genKListByTypeListInSeq (c + 1) n l (( newVar)#vars) subG))"

primrec genStrictRulesSeq :: "'upVar label \<Rightarrow> 'upVar sort list
         \<Rightarrow> 'upVar sort list list \<Rightarrow> nat \<Rightarrow>
        'upVar sort list list \<Rightarrow> ('upVar sort list * 'upVar sort list list
   * 'upVar label KItemSyntax * synAttrib list * bool) list \<Rightarrow>
     ('upVar kSyntax.sort \<times> 'upVar kSyntax.sort list) list \<Rightarrow>
        ('upVar, 'var, 'metaVar) rulePat list option" where
"genStrictRulesSeq s sty tyl n [] database subG = Some []"
| "genStrictRulesSeq s sty tyl n (b#l) database subG =
 (if subsortList b [K] subG then 
    genStrictRulesSeq s sty tyl (n+1) l database subG else
    (case genKListByTypeListInSeq 1 n tyl [] subG of newKList \<Rightarrow>
    (case splitHoleFromKList 1 n newKList of None \<Rightarrow> None
       | Some (front, kl') \<Rightarrow> (case genStrictRulesSeq s sty tyl (n + 1) l database subG
      of None \<Rightarrow> None | Some rl \<Rightarrow>
   (case freshVar (getAllMetaVarsInSUKList newKList) of newVar \<Rightarrow>
   (case suToIRInKList newKList database of Some left \<Rightarrow>
    (case suToIRInKList kl' database of Some left' \<Rightarrow>
    (case getMetaVar front of None \<Rightarrow> None | Some frontVar \<Rightarrow>
        Some ((KRulePat (KPat [IRKItem (IRKLabel s) left sty] (Some ( newVar))) 
           [front, ItemFactor (SUKItem (SUKLabel s) kl' sty), IdFactor ( newVar)]
         (SUKItem (SUKLabel NotBool)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
                                 [ItemKl (SUBigBag (SUK [front]))] [Bool])]))] [Bool]) False)#
     (KRulePat (KPat [IRIdKItem frontVar [KResult],
             IRKItem (IRKLabel s) left' sty] (Some (newVar)))
           [ItemFactor (SUKItem (SUKLabel s) newKList sty), IdFactor (newVar)]
         (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#rl))
     | _ \<Rightarrow> None) | _ \<Rightarrow> None))))))"

primrec genStrictRules :: "'metaVar metaVar list \<Rightarrow> ('upVar sort list * 'upVar sort list list
   * 'upVar label KItemSyntax * synAttrib list * bool) list \<Rightarrow>
   ('upVar sort list * 'upVar sort list list
   * 'upVar label KItemSyntax * synAttrib list * bool) list
   \<Rightarrow> ('upVar kSyntax.sort \<times> 'upVar kSyntax.sort list) list
      \<Rightarrow> ('upVar, 'var, 'metaVar) rulePat list option" where
"genStrictRules S [] database subG = Some []"
| "genStrictRules S (b#l) database subG =
   (case b of (ty, tyl, SingleTon s, stl, True) \<Rightarrow>
        if Seqstrict \<in> set stl then (if getStrictInAttributes stl = None
        then (case genStrictRulesSeq s ty tyl 1 tyl database subG of None \<Rightarrow> None
          | Some rl \<Rightarrow> (case genStrictRules S l database subG of None \<Rightarrow> None
            | Some rl' \<Rightarrow> Some (rl@rl'))) else None)
     else (case getStrictList stl tyl of [] \<Rightarrow> genStrictRules S l database subG
       | (n#nl) \<Rightarrow> (case genKListByTypeList tyl [] subG of newKList \<Rightarrow>
          (case genStrictRulesAux s ty (n#nl) newKList database subG of None \<Rightarrow> None
           | Some rl \<Rightarrow> (case genStrictRules S l database subG of None \<Rightarrow> None
            | Some rl' \<Rightarrow> Some (rl@rl'))))))"

definition strictRuleTest ::
   "'metaVar metaVar list \<Rightarrow> ('upVar, 'var, 'acapvar, 'metaVar) kFile \<Rightarrow>
      ('upVar sort \<times> 'upVar sort list) list \<Rightarrow> ('upVar, 'var, 'metaVar) rulePat list option" where
"strictRuleTest vars Theory subG = (case syntaxSetToKItemTest Theory of None \<Rightarrow> None
  | Some database \<Rightarrow> (case genStrictRules vars database database subG of None \<Rightarrow> None
                    | Some rl \<Rightarrow> Some rl))"

(* important compilation check *)
definition validSyntaxSort :: "'metaVar metaVar list \<Rightarrow>
    ('upVar, 'var, 'acapvar, 'metaVar) kFile
   \<Rightarrow> ('upVar sort list * 'upVar sort list list *
     'upVar label KItemSyntax * synAttrib list * bool) list
   \<Rightarrow> ('upVar kSyntax.sort \<times> 'upVar kSyntax.sort list) list \<Rightarrow> bool" where
"validSyntaxSort metaVars Theory database subG =
    (validSyntaxs database \<and> validArgSynax database \<and>
       syntaxSetToKItemTest Theory \<noteq> None
              \<and> strictRuleTest metaVars Theory subG \<noteq> None)"

primrec locateHoleInKLabel :: "('upVar, 'var, 'metaVar) kLabel
                                                 \<Rightarrow> ('upVar sort) option"
    and locateHoleInKLabelR :: "('upVar, 'var, 'metaVar) kLabel rewrite
                                                            \<Rightarrow> ('upVar sort) option"
    and locateHoleInKItem :: "('upVar, 'var, 'metaVar) kItem \<Rightarrow> ('upVar sort) option"
    and locateHoleInKItemR :: "('upVar, 'var, 'metaVar) kItem rewrite
                                                            \<Rightarrow> ('upVar sort) option"
    and locateHoleInKList :: "('upVar, 'var, 'metaVar) kList \<Rightarrow> ('upVar sort) option"
    and locateHoleInKListR :: "('upVar, 'var, 'metaVar) kList rewrite
                                                             \<Rightarrow> ('upVar sort) option"
    and locateHoleInK :: "('upVar, 'var, 'metaVar) k \<Rightarrow> ('upVar sort) option"
    and locateHoleInKR :: "('upVar, 'var, 'metaVar)
                   k rewrite \<Rightarrow> ('upVar sort) option"
    and locateHoleInList :: "('upVar, 'var, 'metaVar)
                                theList \<Rightarrow> ('upVar sort) option"
    and locateHoleInListR :: "('upVar, 'var, 'metaVar)
                       theList rewrite \<Rightarrow> ('upVar sort) option"
    and locateHoleInSet :: "('upVar, 'var, 'metaVar) theSet \<Rightarrow> ('upVar sort) option"
    and locateHoleInSetR :: "('upVar, 'var, 'metaVar)
                          theSet rewrite \<Rightarrow> ('upVar sort) option"
    and locateHoleInMap :: "('upVar, 'var, 'metaVar) theMap \<Rightarrow> ('upVar sort) option"
    and locateHoleInMapR :: "('upVar, 'var, 'metaVar)
                              theMap rewrite \<Rightarrow> ('upVar sort) option"
    and locateHoleInBigKWithBag :: "('upVar, 'var, 'metaVar) bigKWithBag
                                                        \<Rightarrow> ('upVar sort) option"
    and locateHoleInBigK :: "('upVar, 'var, 'metaVar) bigK \<Rightarrow> ('upVar sort) option"
    and locateHoleInBag :: "('upVar, 'var, 'metaVar) bag \<Rightarrow> ('upVar sort) option"
    and locateHoleInBagR :: "('upVar, 'var, 'metaVar)
                              bag rewrite \<Rightarrow> ('upVar sort) option"
 where
  "locateHoleInKLabel (KLabelC a) = None"
| "locateHoleInKLabel (KLabelFun a b) =
     (case locateHoleInKLabel a of None \<Rightarrow> locateHoleInKListR b
        | Some ty \<Rightarrow> (case locateHoleInKListR b of None \<Rightarrow> Some ty
        | Some ty' \<Rightarrow> None))"
| "locateHoleInKLabel (IdKLabel n) = None"
| "locateHoleInKLabelR (KTerm n) = locateHoleInKLabel n"
| "locateHoleInKLabelR (KRewrite l r) =
                    (case (locateHoleInKLabel l) of None
                          \<Rightarrow> (case locateHoleInKLabel r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                 | Some a \<Rightarrow> (case locateHoleInKLabel r of None \<Rightarrow> Some a
                 | Some a' \<Rightarrow> None))"
| "locateHoleInKItem (KItemC l r ty) = (case (locateHoleInKLabelR l) of None
                          \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                 | Some a \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> Some a
                 | Some a' \<Rightarrow> None))"
| "locateHoleInKItem (Constant a b) = None"
| "locateHoleInKItem (IdKItem a b) = None"
| "locateHoleInKItem (HOLE a) = Some a"
| "locateHoleInKItemR (KTerm t) = locateHoleInKItem t"
| "locateHoleInKItemR (KRewrite l r) = (case (locateHoleInKItem l) of None
                          \<Rightarrow> (case locateHoleInKItem r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKItem r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInKList (KListCon l r) = (case (locateHoleInKListR l) of None
                          \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInKList UnitKList = None"
| "locateHoleInKList (IdKList a) = None"
| "locateHoleInKList (KListItem a) = (locateHoleInBigKWithBag a)"
| "locateHoleInKListR (KTerm t) = locateHoleInKList t"
| "locateHoleInKListR (KRewrite l r) = (case (locateHoleInKList l) of None
                          \<Rightarrow> (case locateHoleInKList r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKList r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInBigKWithBag (TheBigK a) = locateHoleInBigK a"
| "locateHoleInBigKWithBag (TheLabel a) = locateHoleInKLabelR a"
| "locateHoleInBigKWithBag (TheBigBag b) = locateHoleInBagR b"
| "locateHoleInBigK (TheK t) = locateHoleInKR t"
| "locateHoleInBigK (TheList t) = locateHoleInListR t"
| "locateHoleInBigK (TheSet t) = locateHoleInSetR t"
| "locateHoleInBigK (TheMap t) = locateHoleInMapR t"
| "locateHoleInK (Tilda l r) = (case (locateHoleInKR l) of None
                          \<Rightarrow> (case locateHoleInKR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInK UnitK = None"
| "locateHoleInK (IdK a) = None"
| "locateHoleInK (SingleK a) = (locateHoleInKItemR a)"
| "locateHoleInK (KFun l r) = (case (locateHoleInKLabel l) of None
                          \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInKR (KTerm a) = (locateHoleInK a)"
| "locateHoleInKR (KRewrite l r) = (case (locateHoleInK l) of None
                          \<Rightarrow> (case locateHoleInK r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInK r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInList (ListCon l r) = (case (locateHoleInListR l) of None
                          \<Rightarrow> (case locateHoleInListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInListR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInList UnitList = None"
| "locateHoleInList (IdList a) = None"
| "locateHoleInList (ListItem a) = locateHoleInKR a"
| "locateHoleInList (ListFun l r) = (case (locateHoleInKLabel l) of None
                          \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInListR (KTerm a) = (locateHoleInList a)"
| "locateHoleInListR (KRewrite l r) = (case (locateHoleInList l) of None
                          \<Rightarrow> (case locateHoleInList r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInList r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInSet (SetCon l r) = (case (locateHoleInSetR l) of None
                          \<Rightarrow> (case locateHoleInSetR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInSetR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInSet UnitSet = None"
| "locateHoleInSet (IdSet a) = None"
| "locateHoleInSet (SetItem a) = locateHoleInKR a"
| "locateHoleInSet (SetFun l r) = (case (locateHoleInKLabel l) of None
                          \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInSetR (KTerm a) = (locateHoleInSet a)"
| "locateHoleInSetR (KRewrite l r) = (case (locateHoleInSet l) of None
                          \<Rightarrow> (case locateHoleInSet r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInSet r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInMap (MapCon l r) = (case (locateHoleInMapR l) of None
                          \<Rightarrow> (case locateHoleInMapR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInMapR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInMap UnitMap = None"
| "locateHoleInMap (IdMap a) = None"
| "locateHoleInMap (MapItem l r) = (case (locateHoleInKR l) of None
                          \<Rightarrow> (case locateHoleInKR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInMap (MapFun l r) = (case (locateHoleInKLabel l) of None
                          \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInMapR (KTerm a) = (locateHoleInMap a)"
| "locateHoleInMapR (KRewrite l r) = (case (locateHoleInMap l) of None
                          \<Rightarrow> (case locateHoleInMap r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInMap r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInBag (BagCon l r) = (case (locateHoleInBagR l) of None
                          \<Rightarrow> (case locateHoleInBagR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInBagR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInBag UnitBag = None"
| "locateHoleInBag (IdBag a) = None"
| "locateHoleInBag (Xml a n t) =  locateHoleInBagR t"
| "locateHoleInBag (SingleCell a n t) =  locateHoleInBigK t"
| "locateHoleInBagR (KTerm a) = (locateHoleInBag a)"
| "locateHoleInBagR (KRewrite l r) = (case (locateHoleInBag l) of None
                          \<Rightarrow> (case locateHoleInBag r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInBag r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"


function fillHoleInKLabel :: "('upVar, 'var, 'metaVar) kLabel \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) kLabel"
    and fillHoleInKLabelR ::
         "('upVar, 'var, 'metaVar) kLabel rewrite \<Rightarrow> 'metaVar metaVar
              \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) kLabel rewrite"
    and fillHoleInKItem :: "('upVar, 'var, 'metaVar) kItem \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) kItem"
    and fillHoleInKItemR :: "('upVar, 'var, 'metaVar) kItem rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) kItem rewrite"
    and fillHoleInKList :: "('upVar, 'var, 'metaVar) kList \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) kList"
    and fillHoleInKListR :: "('upVar, 'var, 'metaVar) kList rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) kList rewrite"
    and fillHoleInK :: "('upVar, 'var, 'metaVar) k \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) k"
    and fillHoleInKR :: "('upVar, 'var, 'metaVar) k rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) k rewrite"
    and fillHoleInList :: "('upVar, 'var, 'metaVar) theList \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) theList"
    and fillHoleInListR :: "('upVar, 'var, 'metaVar) theList rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) theList rewrite"
    and fillHoleInSet :: "('upVar, 'var, 'metaVar) theSet \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) theSet"
    and fillHoleInSetR :: "('upVar, 'var, 'metaVar) theSet rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) theSet rewrite"
    and fillHoleInMap :: "('upVar, 'var, 'metaVar) theMap \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) theMap"
    and fillHoleInMapR :: "('upVar, 'var, 'metaVar) theMap rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) theMap rewrite"
    and fillHoleInBigKWithBag :: "('upVar, 'var, 'metaVar) bigKWithBag \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) bigKWithBag"
    and fillHoleInBigK :: "('upVar, 'var, 'metaVar) bigK \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) bigK"
    and fillHoleInBag :: "('upVar, 'var, 'metaVar) bag \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) bag"
    and fillHoleInBagR :: "('upVar, 'var, 'metaVar) bag rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) bag rewrite"
 where
  "fillHoleInKLabel (KLabelC a) x ty = KLabelC a"
| "fillHoleInKLabel (KLabelFun a b) x ty =
              (KLabelFun (fillHoleInKLabel a x ty) (fillHoleInKListR b x ty))"
| "fillHoleInKLabel (IdKLabel n) x ty = (IdKLabel n)"
| "fillHoleInKLabelR (KTerm n) x ty = KTerm (fillHoleInKLabel n x ty)"
| "fillHoleInKLabelR (KRewrite l r) x ty =
                     KRewrite (fillHoleInKLabel l x ty) (fillHoleInKLabel r x ty)"
| "fillHoleInKItem (KItemC l r ty) x tya =
                  KItemC (fillHoleInKLabelR l x tya) (fillHoleInKListR r x tya) ty"
| "fillHoleInKItem (Constant a b) x ty = (Constant a b)"
| "fillHoleInKItem (IdKItem a b) x ty = (IdKItem a b)"
| "fillHoleInKItem (HOLE a) x ty = IdKItem x ty"
| "fillHoleInKItemR (KTerm t) x ty = KTerm (fillHoleInKItem t  x ty)"
| "fillHoleInKItemR (KRewrite l r) x ty =
          KRewrite (fillHoleInKItem l x ty) (fillHoleInKItem r x ty)"
| "fillHoleInKList (KListCon l r) x ty =
               KListCon (fillHoleInKListR l x ty) (fillHoleInKListR r x ty)"
| "fillHoleInKList UnitKList x ty = UnitKList"
| "fillHoleInKList (IdKList a) x ty = (IdKList a)"
| "fillHoleInKList (KListItem a) x ty = KListItem (fillHoleInBigKWithBag a x ty)"
| "fillHoleInKListR (KTerm t) x ty = KTerm (fillHoleInKList t x ty)"
| "fillHoleInKListR (KRewrite l r) x ty =
                 KRewrite (fillHoleInKList l x ty) (fillHoleInKList r x ty)"
| "fillHoleInBigKWithBag (TheBigK a) x ty = TheBigK (fillHoleInBigK a x ty)"
| "fillHoleInBigKWithBag (TheBigBag b) x ty = TheBigBag (fillHoleInBagR b x ty)"
| "fillHoleInBigKWithBag (TheLabel b) x ty = TheLabel (fillHoleInKLabelR b x ty)"
| "fillHoleInBigK (TheK t) x ty = TheK (fillHoleInKR t x ty)"
| "fillHoleInBigK (TheList t) x ty = TheList (fillHoleInListR t x ty)"
| "fillHoleInBigK (TheSet t) x ty = TheSet (fillHoleInSetR t x ty)"
| "fillHoleInBigK (TheMap t) x ty = TheMap (fillHoleInMapR t x ty)"
| "fillHoleInK (Tilda l r) x ty =
                   Tilda (fillHoleInKR l x ty) (fillHoleInKR r x ty)"
| "fillHoleInK UnitK x ty = UnitK"
| "fillHoleInK (IdK a) x ty = (IdK a)"
| "fillHoleInK (SingleK a) x ty = SingleK (fillHoleInKItemR a x ty)"
| "fillHoleInK (KFun l r) x ty =
                  KFun (fillHoleInKLabel l x ty) (fillHoleInKListR r x ty)"
| "fillHoleInKR (KTerm a) x ty = KTerm (fillHoleInK a x ty)"
| "fillHoleInKR (KRewrite l r) x ty = KRewrite (fillHoleInK l x ty) (fillHoleInK r x ty)"
| "fillHoleInList (ListCon l r) x ty = ListCon (fillHoleInListR l x ty) (fillHoleInListR r x ty)"
| "fillHoleInList UnitList x ty = UnitList"
| "fillHoleInList (IdList a) x ty = (IdList a)"
| "fillHoleInList (ListItem a) x ty = ListItem (fillHoleInKR a x ty)"
| "fillHoleInList (ListFun l r) x ty = ListFun (fillHoleInKLabel l x ty) (fillHoleInKListR r x ty)"
| "fillHoleInListR (KTerm a) x ty = KTerm (fillHoleInList a x ty)"
| "fillHoleInListR (KRewrite l r) x ty =
                     KRewrite (fillHoleInList l x ty) (fillHoleInList r x ty)"
| "fillHoleInSet (SetCon l r) x ty = SetCon (fillHoleInSetR l x ty) (fillHoleInSetR r x ty)"
| "fillHoleInSet UnitSet x ty = UnitSet"
| "fillHoleInSet (IdSet a) x ty = (IdSet a)"
| "fillHoleInSet (SetItem a) x ty = SetItem (fillHoleInKR a x ty)"
| "fillHoleInSet (SetFun l r) x ty =  SetFun (fillHoleInKLabel l x ty) (fillHoleInKListR r x ty)"
| "fillHoleInSetR (KTerm a) x ty = KTerm (fillHoleInSet a x ty)"
| "fillHoleInSetR (KRewrite l r) x ty = KRewrite (fillHoleInSet l x ty) (fillHoleInSet r x ty)"
| "fillHoleInMap (MapCon l r) x ty = MapCon (fillHoleInMapR l x ty) (fillHoleInMapR r x ty)"
| "fillHoleInMap UnitMap x ty = UnitMap"
| "fillHoleInMap (IdMap a) x ty = (IdMap a)"
| "fillHoleInMap (MapItem l r) x ty = MapItem (fillHoleInKR l x ty) (fillHoleInKR r x ty)"
| "fillHoleInMap (MapFun l r) x ty = MapFun (fillHoleInKLabel l x ty) (fillHoleInKListR r x ty)"
| "fillHoleInMapR (KTerm a) x ty = KTerm (fillHoleInMap a x ty)"
| "fillHoleInMapR (KRewrite l r) x ty =
                    KRewrite (fillHoleInMap l x ty) (fillHoleInMap r x ty)"
| "fillHoleInBag (BagCon l r) x ty = BagCon (fillHoleInBagR l x ty) (fillHoleInBagR r x ty)"
| "fillHoleInBag UnitBag x ty = UnitBag"
| "fillHoleInBag (IdBag a) x ty = (IdBag a)"
| "fillHoleInBag (Xml a n t) x ty =  Xml a n (fillHoleInBagR t x ty)"
| "fillHoleInBag (SingleCell a n t) x ty =  SingleCell a n (fillHoleInBigK t x ty)"
| "fillHoleInBagR (KTerm a) x ty = KTerm (fillHoleInBag a x ty)"
| "fillHoleInBagR (KRewrite l r) x ty = KRewrite (fillHoleInBag l x ty) (fillHoleInBag r x ty)"
by pat_completeness auto

termination sorry

(* defining type checking algorithm for K and type adjustment *)
primrec updateMap where
"updateMap a b [] subG = Some [(a,b)]"
| "updateMap a b (x#l) subG = (case x of (a',b') \<Rightarrow> 
   (if a = a' then (case meet b b' subG of [] \<Rightarrow> None
     | (ty#tyl) \<Rightarrow> Some ((a,(ty#tyl))#l)) else
   (case (updateMap a b l subG) of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some (x#l'))))"

primrec updateBeta where
"updateBeta a b [] subG = Some []"
| "updateBeta a b (x#l) subG = (case x of (a',b') \<Rightarrow> 
   (if a = a' then (case meet b b' subG of [] \<Rightarrow> None
     | (ty#tyl) \<Rightarrow> Some ((a,(ty#tyl))#l)) else
   (case (updateBeta a b l subG) of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some (x#l'))))"

(*
primrec isMinInList where
"isMinInList a [] subG = True"
| "isMinInList a (b#l) subG = (if subsortList a b subG then isMinInList a l subG else False)"

primrec pickMinInListAux where
"pickMinInListAux l [] subG = None"
| "pickMinInListAux l (a#al) subG =
     (if isMinInList a (l@al) subG then Some a else pickMinInListAux (l@[a]) al subG)"

definition pickMinInList where
"pickMinInList l subG = pickMinInListAux [] l subG"


primrec makeSortMap where
"makeSortMap [] subG = Some []"
| "makeSortMap (a#l) subG = (case a of (x,y) \<Rightarrow> 
          (case pickMinInList y subG of None \<Rightarrow> None
             | Some v \<Rightarrow> (case makeSortMap l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some ((x,v)#l'))))"
*)



(*
definition pickMinSortInTwo where
"pickMinSortInTwo a b subG = (if subsortList a b subG then Some a 
              else if subsortList b a subG then Some b
                else None)"

definition pickMinSortInThree where
"pickMinSortInThree a b c subG =
        (if subsortList a b subG \<and> subsortList a c subG then Some a 
     else if subsortList b a subG \<and> subsortList b c subG then Some b
     else if subsortList c a subG \<and> subsortList c b subG then Some c
                else None)"
*)

fun getDomainInIRKItem
  and getDomainInIRBigKWithBag
  and getDomainInIRBigKWithLabel
  and getDomainInIRK
  and getDomainInIRKList
  and getDomainInIRList
  and getDomainInIRSet
  and getDomainInIRMap
  and getDomainInIRBag where
"getDomainInIRKItem (IRKItem a b ty) = (case a of (IRIdKLabel x) \<Rightarrow> x#(getDomainInIRKList b)
          | _ \<Rightarrow> getDomainInIRKList b)"
| "getDomainInIRKItem (IRIdKItem a ty) = []"
| "getDomainInIRKItem (IRHOLE ty) = []"
| "getDomainInIRBigKWithBag (IRK a) = getDomainInIRK a"
| "getDomainInIRBigKWithBag (IRList a) = getDomainInIRList a"
| "getDomainInIRBigKWithBag (IRSet a) = getDomainInIRSet a"
| "getDomainInIRBigKWithBag (IRMap a) = getDomainInIRMap a"
| "getDomainInIRBigKWithBag (IRBag a) = getDomainInIRBag a"
| "getDomainInIRBigKWithLabel (IRBigBag a) = getDomainInIRBigKWithBag a"
| "getDomainInIRBigKWithLabel (IRBigLabel a) = []"
| "getDomainInIRK (KPat [] b) = []"
| "getDomainInIRK (KPat (x#l) b) = (getDomainInIRKItem x)@(getDomainInIRK (KPat l b))"
| "getDomainInIRKList (KListPatNoVar []) = []"
| "getDomainInIRKList (KListPatNoVar (x#l)) = (getDomainInIRBigKWithLabel x)@
                                   (getDomainInIRKList (KListPatNoVar l))"
| "getDomainInIRKList (KListPat [] b []) = []"
| "getDomainInIRKList (KListPat [] b (x#l)) = (getDomainInIRBigKWithLabel x)@
                                   (getDomainInIRKList (KListPat [] b l))"
| "getDomainInIRKList (KListPat (x#l) b S) = (getDomainInIRBigKWithLabel x)@
                                   (getDomainInIRKList (KListPat l b S))"
| "getDomainInIRList (ListPatNoVar []) = []"
| "getDomainInIRList (ListPatNoVar (x#l)) = (getDomainInIRK x)@
                                   (getDomainInIRList (ListPatNoVar l))"
| "getDomainInIRList (ListPat [] b []) = []"
| "getDomainInIRList (ListPat [] b (x#l)) = (getDomainInIRK x)@
                                   (getDomainInIRList (ListPat [] b l))"
| "getDomainInIRList (ListPat (x#l) b S) = (getDomainInIRK x)@
                                   (getDomainInIRList (ListPat l b S))"
| "getDomainInIRSet (SetPat [] b) = []"
| "getDomainInIRSet (SetPat (x#l) b) = (getDomainInIRK x)@
                                   (getDomainInIRSet (SetPat l b))"
| "getDomainInIRMap (MapPat [] b) = []"
| "getDomainInIRMap (MapPat ((x,y)#l) b) = (getDomainInIRK x)@(getDomainInIRK y)@
                                   (getDomainInIRMap (MapPat l b))"
| "getDomainInIRBag (BagPat [] b) = []"
| "getDomainInIRBag (BagPat ((x,y,z)#l) b) = (getDomainInIRBigKWithBag z)@
                                   (getDomainInIRBag (BagPat l b))"

primrec getDomainInMatchFactor where
"getDomainInMatchFactor (KLabelMatching a) = []"
| "getDomainInMatchFactor (KItemMatching a) = getDomainInIRKItem a"
| "getDomainInMatchFactor (KListMatching a) = getDomainInIRKList a"
| "getDomainInMatchFactor (KMatching a) = getDomainInIRK a"
| "getDomainInMatchFactor (ListMatching a) = getDomainInIRList a"
| "getDomainInMatchFactor (SetMatching a) = getDomainInIRSet a"
| "getDomainInMatchFactor (MapMatching a) = getDomainInIRMap a"
| "getDomainInMatchFactor (BagMatching a) = getDomainInIRBag a"

primrec getDomainInPat where
"getDomainInPat (KLabelFunPat a b) = getDomainInIRKList b"
| "getDomainInPat (KFunPat a b) = getDomainInIRKList b"
| "getDomainInPat (KItemFunPat a b) = getDomainInIRKList b"
| "getDomainInPat (ListFunPat a b) = getDomainInIRKList b"
| "getDomainInPat (SetFunPat a b) = getDomainInIRKList b"
| "getDomainInPat (MapFunPat a b) = getDomainInIRKList b"
| "getDomainInPat (NormalPat a) = getDomainInMatchFactor a"

primrec constructSortMap where
"constructSortMap [] = []"
| "constructSortMap (a#l) = (a,[Top])#(constructSortMap l)"

fun hasNoTop where
"hasNoTop [] = True"
| "hasNoTop ((a,b)#l) = (if Top \<in> set b then False else hasNoTop l)"

fun getIdInSUKLabel where
"getIdInSUKLabel (SUIdKLabel a) = Some a"
| "getIdInSUKLabel a = None"

(* get domain of beta for configuration *)
fun getDomainInSUKLabel
  and getDomainInSUKItem
  and getDomainInSUBigKWithBag
  and getDomainInSUBigKWithLabel
  and getDomainInSUK
  and getDomainInSUKList
  and getDomainInSUList
  and getDomainInSUSet
  and getDomainInSUMap
  and getDomainInSUBag where
"getDomainInSUKLabel (SUKLabel a) = []"
| "getDomainInSUKLabel (SUIdKLabel x) = []"
| "getDomainInSUKLabel (SUKLabelFun x y) = (case x of (SUIdKLabel x') \<Rightarrow> x'#(getDomainInSUKList y)
           | _ \<Rightarrow> getDomainInSUKList y)"
| "getDomainInSUKItem (SUKItem a b ty) = (case a of (SUIdKLabel x) \<Rightarrow> x#(getDomainInSUKList b)
          | _ \<Rightarrow> getDomainInSUKList b)"
| "getDomainInSUKItem (SUIdKItem a ty) = []"
| "getDomainInSUKItem (SUHOLE ty) = []"
| "getDomainInSUBigKWithBag (SUK a) = getDomainInSUK a"
| "getDomainInSUBigKWithBag (SUList a) = getDomainInSUList a"
| "getDomainInSUBigKWithBag (SUSet a) = getDomainInSUSet a"
| "getDomainInSUBigKWithBag (SUMap a) = getDomainInSUMap a"
| "getDomainInSUBigKWithBag (SUBag a) = getDomainInSUBag a"
| "getDomainInSUBigKWithLabel (SUBigBag a) = getDomainInSUBigKWithBag a"
| "getDomainInSUBigKWithLabel (SUBigLabel a) = []"
| "getDomainInSUK [] = []"
| "getDomainInSUK (x#l) = (case x of (ItemFactor x') \<Rightarrow> (getDomainInSUKItem x')@(getDomainInSUK l)
          | IdFactor x' \<Rightarrow> getDomainInSUK l
         | SUKKItem a b c \<Rightarrow> (case a of (SUIdKLabel x') \<Rightarrow> x'#(getDomainInSUK l)
           | _ \<Rightarrow> getDomainInSUK l))"
| "getDomainInSUKList [] = []"
| "getDomainInSUKList (x#l) =
      (case x of (ItemKl x') \<Rightarrow> (getDomainInSUBigKWithLabel x')@(getDomainInSUKList l)
          | IdKl x' \<Rightarrow> getDomainInSUKList l)"
| "getDomainInSUList [] = []"
| "getDomainInSUList (x#l) = (case x of (ItemL x') \<Rightarrow> (getDomainInSUK x')@(getDomainInSUList l)
          | IdL x' \<Rightarrow> getDomainInSUList l
         | SUListKItem a b \<Rightarrow> (case a of (SUIdKLabel x') \<Rightarrow> x'#(getDomainInSUList l)
           | _ \<Rightarrow> getDomainInSUList l))"
| "getDomainInSUSet [] = []"
| "getDomainInSUSet (x#l) = (case x of (ItemS x') \<Rightarrow> (getDomainInSUK x')@(getDomainInSUSet l)
          | IdS x' \<Rightarrow> getDomainInSUSet l
         | SUSetKItem a b \<Rightarrow> (case a of (SUIdKLabel x') \<Rightarrow> x'#(getDomainInSUSet l)
           | _ \<Rightarrow> getDomainInSUSet l))"
| "getDomainInSUMap [] = []"
| "getDomainInSUMap (x#l) = (case x of (ItemM x' y')
      \<Rightarrow> (getDomainInSUK x')@((getDomainInSUK y')@(getDomainInSUMap l))
          | IdM x' \<Rightarrow> getDomainInSUMap l
         | SUMapKItem a b \<Rightarrow> (case a of (SUIdKLabel x') \<Rightarrow> x'#(getDomainInSUMap l)
           | _ \<Rightarrow> getDomainInSUMap l))"
| "getDomainInSUBag [] = []"
| "getDomainInSUBag (x#l) =
    (case x of (ItemB x' y' z') \<Rightarrow> (getDomainInSUBigKWithBag z')@(getDomainInSUBag l)
          | IdB x' \<Rightarrow> getDomainInSUBag l)"


    
primrec checkTermsInSubsFactor where
"checkTermsInSubsFactor (KLabelSubs a) beta database subG =
    (case checkTermsInSUKLabel a [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', KLabelSubs a'))"
| "checkTermsInSubsFactor (KItemSubs a) beta database subG =
      (case checkTermsInSUKItem a [KItem] [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', KItemSubs a'))"
| "checkTermsInSubsFactor (KListSubs a) beta database subG =
      (case checkTermsInNoneSUKList a [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', KListSubs a'))"
| "checkTermsInSubsFactor (KSubs a) beta database subG =
      (case checkTermsInSUK a [K] [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', KSubs a'))"
| "checkTermsInSubsFactor (ListSubs a) beta database subG =
      (case checkTermsInSUList a [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', ListSubs a'))"
| "checkTermsInSubsFactor (SetSubs a) beta database subG =
      (case checkTermsInSUSet a [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', SetSubs a'))" 
| "checkTermsInSubsFactor (MapSubs a) beta database subG =
      (case checkTermsInSUMap a [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', MapSubs a'))" 
| "checkTermsInSubsFactor (BagSubs a) beta database subG =
      (case checkTermsInSUBag a [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', BagSubs a'))"

primrec replaceVarSortInSUKLabel
    and replaceVarSortInSUKItem
    and replaceVarSortInSUKListElem
    and replaceVarSortInSUKList
    and replaceVarSortInSUKElem
    and replaceVarSortInSUK
    and replaceVarSortInSUListElem
    and replaceVarSortInSUList
    and replaceVarSortInSUSetElem
    and replaceVarSortInSUSet
    and replaceVarSortInSUMapElem
    and replaceVarSortInSUMap
    and replaceVarSortInSUBigKWithBag
    and replaceVarSortInSUBigKWithLabel
    and replaceVarSortInSUBagElem
    and replaceVarSortInSUBag where 
  "replaceVarSortInSUKLabel (SUKLabel a) acc beta subG = Some (SUKLabel a)"
| "replaceVarSortInSUKLabel (SUKLabelFun a b) acc beta subG =
      (case replaceVarSortInSUKLabel a acc beta subG of None \<Rightarrow> None
         | Some a' \<Rightarrow> 
             (case replaceVarSortInSUKList b acc beta subG of None \<Rightarrow> None
         | Some b' \<Rightarrow> Some (SUKLabelFun a' b')))"
| "replaceVarSortInSUKLabel (SUIdKLabel n) acc beta subG = Some (SUIdKLabel n)"
| "replaceVarSortInSUKItem (SUKItem l r ty) acc beta subG =
    (case getIdInSUKLabel l of Some lx \<Rightarrow>
     (case getValueTerm lx beta of None \<Rightarrow> None
        | Some ty' \<Rightarrow>
       (case replaceVarSortInSUKList r acc beta subG of None \<Rightarrow> None
             | Some r' \<Rightarrow> Some (SUKItem l r' ty')))
         | None \<Rightarrow> (case replaceVarSortInSUKLabel l acc beta subG of None \<Rightarrow> None
    | Some l' \<Rightarrow>  (case replaceVarSortInSUKList r acc beta subG of None \<Rightarrow> None
             | Some r' \<Rightarrow> Some (SUKItem l' r' ty))))"
| "replaceVarSortInSUKItem (SUIdKItem a b) acc beta subG =
        (case getValueTerm a acc of None \<Rightarrow> None
             | Some b' \<Rightarrow> Some (SUIdKItem a b'))"
| "replaceVarSortInSUKItem (SUHOLE a) acc beta subG = Some (SUHOLE a)"
| "replaceVarSortInSUKListElem (IdKl x) acc beta subG = Some (IdKl x)"
| "replaceVarSortInSUKListElem (ItemKl x) acc beta subG = 
    (case replaceVarSortInSUBigKWithLabel x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> Some (ItemKl x'))"
| "replaceVarSortInSUKList [] acc beta subG = Some []"
| "replaceVarSortInSUKList (b#l) acc beta subG = 
    (case replaceVarSortInSUKListElem b acc beta subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case replaceVarSortInSUKList l acc beta subG of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some (b'#l')))"
| "replaceVarSortInSUBigKWithLabel (SUBigBag a) acc beta subG =
      (case replaceVarSortInSUBigKWithBag a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "replaceVarSortInSUBigKWithLabel (SUBigLabel a) acc beta subG =
      (case replaceVarSortInSUKLabel a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBigLabel a'))"
| "replaceVarSortInSUBigKWithBag (SUK a) acc beta subG =
      (case replaceVarSortInSUK a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUK a'))"
| "replaceVarSortInSUBigKWithBag (SUList a) acc beta subG =
      (case replaceVarSortInSUList a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUList a'))"
| "replaceVarSortInSUBigKWithBag (SUSet a) acc beta subG =
      (case replaceVarSortInSUSet a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUSet a'))"
| "replaceVarSortInSUBigKWithBag (SUMap a) acc beta subG =
      (case replaceVarSortInSUMap a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUMap a'))"
| "replaceVarSortInSUBigKWithBag (SUBag a) acc beta subG =
      (case replaceVarSortInSUBag a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBag a'))"
| "replaceVarSortInSUKElem (IdFactor x) acc beta subG =
   (case getValueTerm x acc of None \<Rightarrow> None
       | Some ty \<Rightarrow> if ty = [K] then Some (IdFactor x)
            else if subsortList ty [KItem] subG then Some (ItemFactor (SUIdKItem x ty)) else None)"
| "replaceVarSortInSUKElem (ItemFactor x) acc beta subG = 
    (case replaceVarSortInSUKItem x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> Some (ItemFactor x'))"
| "replaceVarSortInSUKElem (SUKKItem x y ty) acc beta subG = 
    (case getIdInSUKLabel x of Some xx \<Rightarrow>
      (case getValueTerm xx beta of None \<Rightarrow> None
       | Some ty' \<Rightarrow> 
    (case replaceVarSortInSUKList y acc beta subG of None \<Rightarrow> None
         | Some y' \<Rightarrow> Some ((SUKKItem x y' ty'))))
        | _ \<Rightarrow> (case replaceVarSortInSUKLabel x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow>
    (case replaceVarSortInSUKList y acc beta subG of None \<Rightarrow> None
         | Some y' \<Rightarrow>  Some ((SUKKItem x' y' ty)))))"
| "replaceVarSortInSUK [] acc beta subG = Some []"
| "replaceVarSortInSUK (b#l) acc beta subG =
    (case replaceVarSortInSUKElem b acc beta subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case replaceVarSortInSUK l acc beta subG of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some (b'#l')))"
| "replaceVarSortInSUListElem (IdL x) acc beta subG = Some (IdL x)"
| "replaceVarSortInSUListElem (ItemL x) acc beta subG = 
    (case replaceVarSortInSUK x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> Some (ItemL x'))"
| "replaceVarSortInSUListElem (SUListKItem x y) acc beta subG = 
   (case replaceVarSortInSUKLabel x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case replaceVarSortInSUKList y acc beta subG of None \<Rightarrow> None
         | Some y' \<Rightarrow> Some ((SUListKItem x' y'))))"
| "replaceVarSortInSUList [] acc beta subG = Some []"
| "replaceVarSortInSUList (b#l) acc beta subG =
    (case replaceVarSortInSUListElem b acc beta subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case replaceVarSortInSUList l acc beta subG of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some (b'#l')))"
| "replaceVarSortInSUSetElem (IdS x) acc beta subG = Some (IdS x)"
| "replaceVarSortInSUSetElem (ItemS x) acc beta subG = 
    (case replaceVarSortInSUK x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> Some (ItemS x'))"
| "replaceVarSortInSUSetElem (SUSetKItem x y) acc beta subG = 
   (case replaceVarSortInSUKLabel x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case replaceVarSortInSUKList y acc beta subG of None \<Rightarrow> None
         | Some y' \<Rightarrow> Some ((SUSetKItem x' y'))))"
| "replaceVarSortInSUSet [] acc beta subG = Some []"
| "replaceVarSortInSUSet (b#l) acc beta subG =
    (case replaceVarSortInSUSetElem b acc beta subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case replaceVarSortInSUSet l acc beta subG of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some (b'#l')))"
| "replaceVarSortInSUMapElem (IdM x) acc beta subG = Some (IdM x)"
| "replaceVarSortInSUMapElem (ItemM x y) acc beta subG = 
    (case replaceVarSortInSUK x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case replaceVarSortInSUK y acc beta subG of None
          \<Rightarrow> None | Some y' \<Rightarrow> Some (ItemM x' y')))"
| "replaceVarSortInSUMapElem (SUMapKItem x y) acc beta subG = 
   (case replaceVarSortInSUKLabel x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case replaceVarSortInSUKList y acc beta subG of None \<Rightarrow> None
         | Some y' \<Rightarrow> Some ((SUMapKItem x' y'))))"
| "replaceVarSortInSUMap [] acc beta subG = Some []"
| "replaceVarSortInSUMap (b#l) acc beta subG =
    (case replaceVarSortInSUMapElem b acc beta subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case replaceVarSortInSUMap l acc beta subG of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some (b'#l')))"
| "replaceVarSortInSUBagElem (IdB x) acc beta subG = Some (IdB x)"
| "replaceVarSortInSUBagElem (ItemB x y z) acc beta subG = 
    (case replaceVarSortInSUBigKWithBag z acc beta subG of None \<Rightarrow> None
       | Some z' \<Rightarrow> Some (ItemB x y z'))"
| "replaceVarSortInSUBag [] acc beta subG = Some []"
| "replaceVarSortInSUBag (b#l) acc beta subG =
      (case replaceVarSortInSUBagElem b acc beta subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case replaceVarSortInSUBag l acc beta subG of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some (b'#l')))"

primrec replaceVarSortInSubsFactor where
"replaceVarSortInSubsFactor (KLabelSubs a) acc beta subG =
       (case replaceVarSortInSUKLabel a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (KLabelSubs a'))"
| "replaceVarSortInSubsFactor (KItemSubs a) acc beta subG =
       (case replaceVarSortInSUKItem a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (KItemSubs a'))"
| "replaceVarSortInSubsFactor (KListSubs a) acc beta subG =
       (case replaceVarSortInSUKList a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (KListSubs a'))"
| "replaceVarSortInSubsFactor (KSubs a) acc beta subG =
       (case replaceVarSortInSUK a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (KSubs a'))"
| "replaceVarSortInSubsFactor (ListSubs a) acc beta subG =
       (case replaceVarSortInSUList a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (ListSubs a'))"
| "replaceVarSortInSubsFactor (SetSubs a) acc beta subG =
       (case replaceVarSortInSUSet a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (SetSubs a'))"
| "replaceVarSortInSubsFactor (MapSubs a) acc beta subG =
       (case replaceVarSortInSUMap a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (MapSubs a'))"
| "replaceVarSortInSubsFactor (BagSubs a) acc beta subG =
       (case replaceVarSortInSUBag a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (BagSubs a'))"

primrec hasIdInSUBag :: "('upVar, 'var, 'metaVar) suB list \<Rightarrow> bool" where
"hasIdInSUBag [] = False"
| "hasIdInSUBag (b#l) = (case b of IdB x \<Rightarrow> True
                | _ \<Rightarrow> hasIdInSUBag l)"

primrec onlyIdInSUBag :: "('upVar, 'var, 'metaVar) suB list \<Rightarrow> bool" where
"onlyIdInSUBag [] = True"
| "onlyIdInSUBag (b#l) = (case b of IdB x \<Rightarrow> onlyIdInSUBag l
                | _ \<Rightarrow> False)"

primrec searchBagWithName :: "'var var \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
            \<Rightarrow> (('upVar, 'var, 'metaVar) suB list
                                * ('upVar, 'var, 'metaVar) suB list)" where
"searchBagWithName x [] = ([], [])"
| "searchBagWithName a (b#l) = (case b of IdB x \<Rightarrow>
      (case searchBagWithName a l of  (u,v) \<Rightarrow> (u, b#l))
      | ItemB u v w \<Rightarrow> (case searchBagWithName a l of (q,t)
      \<Rightarrow> (if a = u then ((ItemB u v w)#q,t)
                              else (q, (ItemB u v w)#t))))"

fun checkTermsWithConfi
 and checkTermsWithConfiList
 and checkTermsWithConfiAux where
"checkTermsWithConfi [] A subG = (if onlyIdInSUBag A then True else False)"
| "checkTermsWithConfi (b#l) A subG = (case b of IdB x \<Rightarrow> False
        | ItemB x y z \<Rightarrow> (case searchBagWithName x A of (al, ar) \<Rightarrow>
        (case al of [] \<Rightarrow>
           (if hasIdInSUBag A \<or> Multiplicity Question \<in> set y 
                then checkTermsWithConfi l A subG else False)
           | [a] \<Rightarrow> checkTermsWithConfiList z al subG \<and> checkTermsWithConfi l ar subG
           | al' \<Rightarrow> if Multiplicity Star \<in> set y then
          checkTermsWithConfiList z al subG \<and> checkTermsWithConfi l ar subG
           else False)))"
| "checkTermsWithConfiList P [] subG = True"
| "checkTermsWithConfiList P (b#l) subG = (case b of IdB x \<Rightarrow> False
         | ItemB x y z \<Rightarrow>
            (checkTermsWithConfiAux P z subG \<and> checkTermsWithConfiList P l subG))"
| "checkTermsWithConfiAux (SUBag x) y subG = (case y of SUBag y'
      \<Rightarrow> checkTermsWithConfi x y' subG | _ \<Rightarrow> False)"
| "checkTermsWithConfiAux (SUK x) y subG = (case y of SUK y' \<Rightarrow>
      (case x of [a] \<Rightarrow> (case a of ItemFactor u \<Rightarrow> 
       (case y' of [ItemFactor u'] \<Rightarrow>
         if subsortList (getType u') (getType u) subG then True else False
            | [SUKKItem l kl ty] \<Rightarrow> 
           if subsortList ty (getType u) subG then True else False
            | _ \<Rightarrow> if getType u = [K] then True else False)
          | SUKKItem xl xkl xty \<Rightarrow> (case y' of [ItemFactor u'] \<Rightarrow>
         if subsortList (getType u') xty subG then True else False
            | [SUKKItem l kl ty] \<Rightarrow> 
           if subsortList ty xty subG then True else False
            | _ \<Rightarrow> if xty = [K] then True else False)
           | _ \<Rightarrow> (case y' of [ItemFactor u'] \<Rightarrow>
         if getType u' = [K] then True else False
            | [SUKKItem l kl ty] \<Rightarrow> 
           if ty = [K] then True else False
            | _ \<Rightarrow> True)) | _ \<Rightarrow> True) | _ \<Rightarrow> False)"
| "checkTermsWithConfiAux (SUList x) y subG = (case y of SUList y' \<Rightarrow> True
           | _ \<Rightarrow> False)"
| "checkTermsWithConfiAux (SUSet x) y subG = (case y of SUSet y' \<Rightarrow> True
           | _ \<Rightarrow> False)"
| "checkTermsWithConfiAux (SUMap x) y subG = (case y of SUMap y' \<Rightarrow> True
           | _ \<Rightarrow> False)"

fun wellFormRules :: "('upVar, 'var, 'metaVar) rulePat list \<Rightarrow> bool" where
"wellFormRules [] = True"
| "wellFormRules ((FunPat s rl a)#l) = ((foldl (\<lambda> b (x,y,z) . b \<and>
       (set (getAllMetaVarsInSubsFactor y @ getAllMetaVarsInSUKItem z)
           \<subseteq> set (getAllMetaVarsInPat x))) True
                (case a of None \<Rightarrow> rl | Some a' \<Rightarrow> (a'#rl)))
             \<and> wellFormRules l)"
| "wellFormRules ((MacroPat s a b)#l) =
  ((set (getAllMetaVarsInSUK b) \<subseteq> set (getAllMetaVarsInIRKList a))
          \<and> wellFormRules l)"
| "wellFormRules ((AnywherePat ss a b c)#l) =
         ((set (getAllMetaVarsInSUK b @ getAllMetaVarsInSUKItem c)
                    \<subseteq> set (getAllMetaVarsInIRKList a)) \<and> wellFormRules l)"
| "wellFormRules ((KRulePat a b c tb)#l) =
         ((set (getAllMetaVarsInSUK b @ getAllMetaVarsInSUKItem c)
                \<subseteq> set (getAllMetaVarsInIRK a)) \<and> wellFormRules l)"
| "wellFormRules ((BagRulePat a b c tb)#l) =
      ((set (getAllMetaVarsInSUBag b @ getAllMetaVarsInSUKItem c)
             \<subseteq> set (getAllMetaVarsInIRBag a)) \<and> wellFormRules l)"

(* type adjustment each rule *)
primrec inferTypesInFunPat where
"inferTypesInFunPat s [] database subG = Some []"
| "inferTypesInFunPat s (b#l) database subG = (case b of (x,y,z) \<Rightarrow>
    (case x of KLabelFunPat ss kl \<Rightarrow> if ss = s then
     (case y of (KLabelSubs sl) \<Rightarrow> (case (getSort s database, getArgSort s database)
       of (Some ty, Some tyl) \<Rightarrow> if ty = [KLabel] then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
                      (constructSortMap (getDomainInIRKList kl)) database subG)
      of None \<Rightarrow> None | Some (acckl, betakl, kl') \<Rightarrow>
     (case checkTermsInSUKLabel sl acckl betakl database subG of None \<Rightarrow> None
        | Some (accsl, betasl, sl') \<Rightarrow>
      (case checkTermsInSUKItem z [KItem] accsl betasl database subG of None \<Rightarrow> None
       | Some (accz, betaz, z') \<Rightarrow> if hasNoTop accz \<and> hasNoTop betaz then
    (case (replaceVarSortInSUKList kl' accz betaz subG, replaceVarSortInSUKLabel sl' accz betaz subG,
      replaceVarSortInSUKItem z' accz betaz subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUKLabel sla subG,
         regularizeInSUKItem za subG) of (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInFunPat s l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((KLabelFunPat s klb', KLabelSubs slb, zb)#l')))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))) else None | _ \<Rightarrow> None)
            | _ \<Rightarrow> None) else None
    | KFunPat ss kl \<Rightarrow> if ss = s then
     (case y of (KSubs sl) \<Rightarrow> (case (getSort s database, getArgSort s database)
       of (Some ty, Some tyl) \<Rightarrow> if subsortList ty [K] subG then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
                      (constructSortMap (getDomainInIRKList kl)) database subG)
      of None \<Rightarrow> None | Some (acckl, betakl, kl') \<Rightarrow>
     (case checkTermsInSUK sl ty acckl betakl database subG of None \<Rightarrow> None
        | Some (accsl, betasl, sl') \<Rightarrow>
      (case checkTermsInSUKItem z [KItem] accsl betasl database subG of None \<Rightarrow> None
       | Some (accz, betaz, z') \<Rightarrow> if hasNoTop accz \<and> hasNoTop betaz then
    (case (replaceVarSortInSUKList kl' accz betaz subG, replaceVarSortInSUK sl' accz betaz subG,
      replaceVarSortInSUKItem z' accz betaz subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUK sla subG,
         regularizeInSUKItem za subG) of (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInFunPat s l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((KFunPat s klb', KSubs slb, zb)#l')))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))) else None | _ \<Rightarrow> None)
            | _ \<Rightarrow> None) else None
    | KItemFunPat ss kl \<Rightarrow> if ss = s then
     (case y of (KItemSubs sl) \<Rightarrow> (case (getSort s database, getArgSort s database)
       of (Some ty, Some tyl) \<Rightarrow> if subsortList ty [KItem] subG then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
                      (constructSortMap (getDomainInIRKList kl)) database subG)
      of None \<Rightarrow> None | Some (acckl, betakl, kl') \<Rightarrow>
     (case checkTermsInSUKItem sl ty acckl betakl database subG of None \<Rightarrow> None
        | Some (accsl, betasl, sl') \<Rightarrow>
      (case checkTermsInSUKItem z [KItem] accsl betasl database subG of None \<Rightarrow> None
       | Some (accz, betaz, z') \<Rightarrow> if hasNoTop accz \<and> hasNoTop betaz then
    (case (replaceVarSortInSUKList kl' accz betaz subG, replaceVarSortInSUKItem sl' accz betaz subG,
      replaceVarSortInSUKItem z' accz betaz subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUKItem sla subG,
         regularizeInSUKItem za subG) of (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInFunPat s l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((KItemFunPat s klb', KItemSubs slb, zb)#l')))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))) else None | _ \<Rightarrow> None)
            | _ \<Rightarrow> None) else None
    | ListFunPat ss kl \<Rightarrow> if ss = s then
     (case y of (ListSubs sl) \<Rightarrow> (case (getSort s database, getArgSort s database)
       of (Some ty, Some tyl) \<Rightarrow> if subsortList ty [List] subG then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
                      (constructSortMap (getDomainInIRKList kl)) database subG)
      of None \<Rightarrow> None | Some (acckl, betakl, kl') \<Rightarrow>
     (case checkTermsInSUList sl acckl betakl database subG of None \<Rightarrow> None
        | Some (accsl, betasl, sl') \<Rightarrow>
      (case checkTermsInSUKItem z [KItem] accsl betasl database subG of None \<Rightarrow> None
       | Some (accz, betaz, z') \<Rightarrow> if hasNoTop accz \<and> hasNoTop betaz then
    (case (replaceVarSortInSUKList kl' accz betaz subG, replaceVarSortInSUList sl' accz betaz subG,
      replaceVarSortInSUKItem z' accz betaz subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUList sla subG,
         regularizeInSUKItem za subG) of (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInFunPat s l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((ListFunPat s klb', ListSubs slb, zb)#l')))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))) else None | _ \<Rightarrow> None)
            | _ \<Rightarrow> None) else None
    | SetFunPat ss kl \<Rightarrow> if ss = s then
     (case y of (SetSubs sl) \<Rightarrow> (case (getSort s database, getArgSort s database)
       of (Some ty, Some tyl) \<Rightarrow> if subsortList ty [Set] subG then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
                      (constructSortMap (getDomainInIRKList kl)) database subG)
      of None \<Rightarrow> None | Some (acckl, betakl, kl') \<Rightarrow>
     (case checkTermsInSUSet sl acckl betakl database subG of None \<Rightarrow> None
        | Some (accsl, betasl, sl') \<Rightarrow>
      (case checkTermsInSUKItem z [KItem] accsl betasl database subG of None \<Rightarrow> None
       | Some (accz, betaz, z') \<Rightarrow> if hasNoTop accz \<and> hasNoTop betaz then
    (case (replaceVarSortInSUKList kl' accz betaz subG, replaceVarSortInSUSet sl' accz betaz subG,
      replaceVarSortInSUKItem z' accz betaz subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUSet sla subG,
         regularizeInSUKItem za subG) of (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInFunPat s l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((SetFunPat s klb', SetSubs slb, zb)#l')))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))) else None | _ \<Rightarrow> None)
            | _ \<Rightarrow> None) else None
    | MapFunPat ss kl \<Rightarrow> if ss = s then
     (case y of (MapSubs sl) \<Rightarrow> (case (getSort s database, getArgSort s database)
       of (Some ty, Some tyl) \<Rightarrow> if subsortList ty [Map] subG then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
                      (constructSortMap (getDomainInIRKList kl)) database subG)
      of None \<Rightarrow> None | Some (acckl, betakl, kl') \<Rightarrow>
     (case checkTermsInSUMap sl acckl betakl database subG of None \<Rightarrow> None
        | Some (accsl, betasl, sl') \<Rightarrow>
      (case checkTermsInSUKItem z [KItem] accsl betasl database subG of None \<Rightarrow> None
       | Some (accz, betaz, z') \<Rightarrow> if hasNoTop accz \<and> hasNoTop betaz then
    (case (replaceVarSortInSUKList kl' accz betaz subG, replaceVarSortInSUMap sl' accz betaz subG,
      replaceVarSortInSUKItem z' accz betaz subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUMap sla subG,
         regularizeInSUKItem za subG) of (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInFunPat s l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((MapFunPat s klb', MapSubs slb, zb)#l')))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))) else None | _ \<Rightarrow> None)
            | _ \<Rightarrow> None) else None
     | _ \<Rightarrow> None))"

fun inferTypesInRules where
"inferTypesInRules [] Theory database subG = Some []"
| "inferTypesInRules ((FunPat s kl ow)#l) Theory database subG = (case ow of None \<Rightarrow>
     (case inferTypesInFunPat s kl database subG of None \<Rightarrow> None
        | Some kl' \<Rightarrow> (case inferTypesInRules l Theory database subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((FunPat s kl' None)#l')))
  | Some (x,y,z) \<Rightarrow>
       (case inferTypesInFunPat s [(x,y,z)] database subG of Some [(x',y',z')] \<Rightarrow>
        (case inferTypesInFunPat s kl database subG of None \<Rightarrow> None
        | Some kl' \<Rightarrow> (case inferTypesInRules l Theory database subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((FunPat s kl' (Some (x',y',z')))#l'))) | _ \<Rightarrow> None))"
| "inferTypesInRules ((MacroPat s kl sl)#l) Theory database subG =
    (case (getSort s database, getArgSort s database) of (Some ty, Some tyl) \<Rightarrow>
      if subsortList ty [KItem] subG \<and> \<not> isFunctionItem s database then
         (case (checkTermsInSUKList (irToSUInKList kl) tyl []
             (constructSortMap (getDomainInIRKList kl)) database subG) of None \<Rightarrow> None
      | Some (acckl,betakl,kl') \<Rightarrow> (case 
      checkTermsInSUK sl [K] acckl betakl database subG of None \<Rightarrow> None
       | Some (accsl,betasl, sl') \<Rightarrow> if hasNoTop accsl \<and> hasNoTop betasl then
      (case (replaceVarSortInSUKList kl' accsl betasl subG, replaceVarSortInSUK sl' accsl betasl subG)
         of (Some kla, Some sla) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUK sla subG) of (Some klb, Some slb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow> (case inferTypesInRules l Theory database subG of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((MacroPat s klb' slb)#l'))) | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))
      else None | _ \<Rightarrow> None)"
| "inferTypesInRules ((AnywherePat ss kl r c)#l) Theory database subG =
   (case (getSort ss database, getArgSort ss database) of (Some ty, Some tyl) \<Rightarrow>
      if subsortList ty [KItem] subG \<and> \<not> isFunctionItem ss database then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
              (constructSortMap (getDomainInIRKList kl)) database subG) of None \<Rightarrow> None
     | Some (acckl, betakl, kl') \<Rightarrow> 
     (case (checkTermsInSUK r [K] acckl betakl database subG) of None \<Rightarrow> None
      | Some (accr, betar, r') \<Rightarrow>
     (case checkTermsInSUKItem c [KItem] accr betar database subG of None \<Rightarrow> None
       | Some (accc, betac, c') \<Rightarrow> if hasNoTop accc \<and> hasNoTop betac then
       (case (replaceVarSortInSUKList kl' accc betac subG, replaceVarSortInSUK r' accc betac subG,
      replaceVarSortInSUKItem c' accc betac subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUK sla subG, regularizeInSUKItem za subG) of
          (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInRules l Theory database subG of None \<Rightarrow> None
      | Some l' \<Rightarrow> Some ((AnywherePat ss klb' slb zb)#l'))) | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)))
     else None | _ \<Rightarrow> None)"
| "inferTypesInRules ((KRulePat kl r c tb)#l) Theory database subG =
   (case (checkTermsInSUK (irToSUInK kl) [K] []
                    (constructSortMap (getDomainInIRK kl)) database subG) of None \<Rightarrow> None
       | Some (acckl, betakl, kl') \<Rightarrow>
        (case checkTermsInSUK r [K] acckl betakl database subG of None \<Rightarrow> None
         | Some (accr, betar, r') \<Rightarrow>
        (case checkTermsInSUKItem c [KItem] accr betar database subG of None \<Rightarrow> None
         | Some (accc, betac, c') \<Rightarrow> if hasNoTop accc \<and> hasNoTop betac then
        (case (replaceVarSortInSUK kl' accc betac subG, replaceVarSortInSUK r' accc betac subG,
      replaceVarSortInSUKItem c' accc betac subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUK kla subG, regularizeInSUK sla subG, regularizeInSUKItem za subG) of
          (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInK klb database of None \<Rightarrow> None
             | Some (NormalPat (KMatching klb')) \<Rightarrow>
          (case inferTypesInRules l Theory database subG of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some ((KRulePat klb' slb zb tb)#l'))) | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)))"
| "inferTypesInRules ((BagRulePat kl r c tb)#l) Theory database subG =
   (case getConfiguration Theory of [confi] \<Rightarrow>
    (case toSUInBag confi of None \<Rightarrow> None | Some confi' \<Rightarrow>
      if (checkTermsWithConfi confi' (irToSUInBag kl) subG \<and> checkTermsWithConfi confi' r subG)
           then (case (checkTermsInSUBag (irToSUInBag kl) []
         (constructSortMap (getDomainInIRBag kl)) database subG) of None \<Rightarrow> None
        | Some (acckl, betakl,kl') \<Rightarrow>
         (case checkTermsInSUBag r acckl betakl database subG of None \<Rightarrow> None
          | Some (accr,betar,r') \<Rightarrow>
         (case checkTermsInSUKItem c [KItem] accr betar database subG of None \<Rightarrow> None
         | Some (accc,betac,c') \<Rightarrow> if hasNoTop accc \<and> hasNoTop betac then
      (case (replaceVarSortInSUBag kl' accc betac subG, replaceVarSortInSUBag r' accc betac subG,
      replaceVarSortInSUKItem c' accc betac subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUBag kla subG, regularizeInSUBag sla subG, regularizeInSUKItem za subG) of
          (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInBag klb database of None \<Rightarrow> None
       | Some klb' \<Rightarrow> (case inferTypesInRules l Theory database subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((BagRulePat klb' slb zb tb)#l'))) | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)))
         else None) | _ \<Rightarrow> None)"


(* given a bag term in K core, compile it to a K IR version that is compared with the
    configuration of a language spec and fulfilled missing cells *)
primrec removeDotInFeatureList :: "feature list \<Rightarrow> feature list" where
"removeDotInFeatureList [] = []"
| "removeDotInFeatureList (b#l) = (case b of DotDotDot \<Rightarrow> removeDotInFeatureList l
          | _ \<Rightarrow> b#(removeDotInFeatureList l))"

function completeBagHasDotInSUBag :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
      \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
       \<Rightarrow> (('upVar, 'var, 'metaVar) suB list *
                            ('upVar, 'var, 'metaVar) suB list) option"
   and completeBagNoDotInSUBag :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list option"
   and completeSameBagsInSUBag :: "feature list \<Rightarrow>
           ('upVar, 'var, 'metaVar) suBigKWithBag
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
       \<Rightarrow> ('upVar, 'var, 'metaVar) suB list option"
   and completeNextBagsInSUBag :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
      \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
       \<Rightarrow> (('upVar, 'var, 'metaVar) suB list * 
                    ('upVar, 'var, 'metaVar) suB list) option"
      and completeBagInSUBigKWithBag :: "feature list \<Rightarrow>
      ('upVar, 'var, 'metaVar) suBigKWithBag
      \<Rightarrow> ('upVar, 'var, 'metaVar) suBigKWithBag
       \<Rightarrow> ('upVar, 'var, 'metaVar) suBigKWithBag option" where
 "completeBagNoDotInSUBag [] A postp = (if postp = [] then
        (if onlyIdInSUBag A then Some A else None)
         else (if onlyIdInSUBag A \<and> hasIdInSUBag A then Some A else None))"
| "completeBagNoDotInSUBag (b#l) A postp = (case b of IdB x \<Rightarrow> None
               | ItemB x y z \<Rightarrow>
         (case searchBagWithName x A of (al, as) \<Rightarrow>
    if al = [] then completeBagNoDotInSUBag l A (postp@[b]) else
     (if Multiplicity Star \<in> set y then
          (case completeSameBagsInSUBag y z al of None \<Rightarrow> None
              | Some al' \<Rightarrow>
           (case completeBagNoDotInSUBag l as postp of None \<Rightarrow> None
              | Some l' \<Rightarrow> Some (al'@l')))
      else ( if length al > 1 then None
             else  (case completeSameBagsInSUBag y z al of None \<Rightarrow> None
    | Some al' \<Rightarrow> (case completeBagNoDotInSUBag l as postp of None \<Rightarrow> None
                 | Some l' \<Rightarrow> Some (al'@l')))))))"
| "completeSameBagsInSUBag f p [] = Some []"
| "completeSameBagsInSUBag f p (b#l) = (case b of IdB x \<Rightarrow> None
             | ItemB x y z \<Rightarrow>
       (case completeBagInSUBigKWithBag f p z of None \<Rightarrow> None
              | Some z' \<Rightarrow>
          (case completeSameBagsInSUBag f p l of None \<Rightarrow> None
              | Some l' \<Rightarrow> Some ((ItemB x (removeDotInFeatureList y) z')#l'))))"
| "completeBagHasDotInSUBag [] A postp acc = completeNextBagsInSUBag postp A acc"
| "completeBagHasDotInSUBag (b#l) A postp acc = (case b of IdB x \<Rightarrow> None
               | ItemB x y z \<Rightarrow>
      (case searchBagWithName x A of (al,as) \<Rightarrow>
     if al = [] then
            completeBagHasDotInSUBag l A (postp@[ItemB x (removeDotInFeatureList y) z]) acc
      else
       (if Multiplicity Star \<in> set y then
          (case completeSameBagsInSUBag y z al of None \<Rightarrow> None
              | Some al' \<Rightarrow> completeBagHasDotInSUBag l as postp (acc@al'))
      else (if length al > 1 then None
             else  (case completeSameBagsInSUBag y z al of None \<Rightarrow> None
              | Some al' \<Rightarrow> completeBagHasDotInSUBag l as postp (acc@al'))))))"
| "completeNextBagsInSUBag [] A acc = Some (acc, A)"
| "completeNextBagsInSUBag (b#l) A acc = (if A = [] then Some (acc@(b#l), [])
     else (case b of IdB x \<Rightarrow> None
            | ItemB x y z \<Rightarrow>
           (case z of SUBag al \<Rightarrow>
    (case completeBagHasDotInSUBag al A [] [] of None \<Rightarrow> None
        | Some (acc', A') \<Rightarrow> 
       completeNextBagsInSUBag l A' (acc@[ItemB x (removeDotInFeatureList y) (SUBag acc')]))
            | _ \<Rightarrow>
                completeNextBagsInSUBag l A (acc@[ItemB x (removeDotInFeatureList y) z]))))"
| "completeBagInSUBigKWithBag f (SUBag a) S = (case S of (SUBag b) \<Rightarrow>
      (if DotDotDot \<in> set f then
        (case completeBagHasDotInSUBag a b [] [] of None \<Rightarrow> None
            | Some (a', still) \<Rightarrow> if still = [] then Some (SUBag a') else None)
       else (case completeBagNoDotInSUBag a b [] of None \<Rightarrow> None
            | Some a' \<Rightarrow>  Some (SUBag a')))
          | _ \<Rightarrow> None)"
| "completeBagInSUBigKWithBag f (SUK a) S =
                    (case S of (SUK b) \<Rightarrow> Some (SUK b) | _ \<Rightarrow> None)"
| "completeBagInSUBigKWithBag f (SUList a) S =
                 (case S of (SUList b) \<Rightarrow> Some (SUList b) | _ \<Rightarrow> None)"
| "completeBagInSUBigKWithBag f (SUSet a) S =
                 (case S of (SUSet b) \<Rightarrow> Some (SUSet b) | _ \<Rightarrow> None)"
| "completeBagInSUBigKWithBag f (SUMap a) S =
                (case S of (SUMap b) \<Rightarrow> Some (SUMap b) | _ \<Rightarrow> None)"
by pat_completeness auto

termination sorry

fun completeBagBySearchBags :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
 \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
       \<Rightarrow> (('upVar, 'var, 'metaVar) suB list *
                         ('upVar, 'var, 'metaVar) suB list) option"
    and completeBagBySearchBigKWithBag :: "('upVar, 'var, 'metaVar) suBigKWithBag
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
 \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
      \<Rightarrow> (('upVar, 'var, 'metaVar) suB list *
                         ('upVar, 'var, 'metaVar) suB list) option" where
"completeBagBySearchBags [] P acc = Some (acc, P)"
| "completeBagBySearchBags (b#l) P acc = (case b of IdB x \<Rightarrow> None
        | ItemB x y z \<Rightarrow> (case searchBagWithName x P of (al, ar)
           \<Rightarrow> if al = [] then
            (case completeBagBySearchBigKWithBag z P acc of None \<Rightarrow> None
        | Some (acc', remain) \<Rightarrow> completeBagBySearchBags l remain acc')
   else (case completeSameBagsInSUBag y z al of None \<Rightarrow> None
            | Some al' \<Rightarrow>
       (case completeBagBySearchBigKWithBag z ar (acc@al') of None \<Rightarrow> None
      | Some (acc', remain) \<Rightarrow> completeBagBySearchBags l remain acc'))))"
| "completeBagBySearchBigKWithBag (SUBag x) P acc = completeBagBySearchBags x P acc"
| "completeBagBySearchBigKWithBag X P acc = Some (acc, P)"

primrec getListInIRBag :: "('upVar, 'var, 'metaVar) irBag
     \<Rightarrow> ('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list" where
"getListInIRBag (BagPat x y) = x"

primrec getVarInIRBag :: "('upVar, 'var, 'metaVar) irBag
     \<Rightarrow> 'metaVar metaVar option" where
"getVarInIRBag (BagPat x y) = y"

primrec mergeListToIRBag :: "('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list
           \<Rightarrow> ('upVar, 'var, 'metaVar) irBag \<Rightarrow>
                  ('upVar, 'var, 'metaVar) irBag" where
"mergeListToIRBag l (BagPat x y) = BagPat (l@x) y"

primrec searchBagWithNameInIRBag
        :: "'var var \<Rightarrow> ('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list
            \<Rightarrow> (('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list
                                * ('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list)" where
"searchBagWithNameInIRBag x [] = ([], [])"
| "searchBagWithNameInIRBag a (b#l) = (case b of (x,y,z) \<Rightarrow>
      (case searchBagWithNameInIRBag a l of (q,t) \<Rightarrow>
        (if a = x then ((x,y,z)#q,t) else (q, (x,y,z)#t))))"

function fillVarsBagHasDotInIRBag :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) irBag
      \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
 \<Rightarrow> ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
       \<Rightarrow> 'metaVar metaVar list
       \<Rightarrow> (('upVar, 'var, 'metaVar) irBag *
         ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
                        * 'metaVar metaVar list) option"
   and fillVarsBagNoDotInIRBag :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) irBag
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
       \<Rightarrow> 'metaVar metaVar list
   \<Rightarrow> (('upVar, 'var, 'metaVar) irBag * 'metaVar metaVar list) option"
   and fillVarsSameBagsInIRBag :: "feature list \<Rightarrow>
           ('upVar, 'var, 'metaVar) suBigKWithBag
   \<Rightarrow> ('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list
       \<Rightarrow> 'metaVar metaVar list \<Rightarrow> (('var var * feature list *
     ('upVar, 'var, 'metaVar) irBigKWithBag) list * 'metaVar metaVar list) option"
   and fillVarsNextBagsInIRBag :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('var var * feature list *
            ('upVar, 'var, 'metaVar) irBigKWithBag) list
       \<Rightarrow> 'metaVar metaVar list \<Rightarrow> (('var var * feature list *
            ('upVar, 'var, 'metaVar) irBigKWithBag) list *
         ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
                        * 'metaVar metaVar list) option"
      and fillVarsInIRBigKWithBag :: "feature list \<Rightarrow>
      ('upVar, 'var, 'metaVar) suBigKWithBag
      \<Rightarrow> ('upVar, 'var, 'metaVar) irBigKWithBag
       \<Rightarrow> 'metaVar metaVar list
       \<Rightarrow> (('upVar, 'var, 'metaVar) irBigKWithBag * 
                        'metaVar metaVar list)  option" where
 "fillVarsBagHasDotInIRBag [] A postp acc vars = (case A of (BagPat [] None)
        \<Rightarrow> (case freshVar vars of newVar \<Rightarrow>
              Some (BagPat acc (Some ( newVar)), [], ( newVar)#vars))
       | BagPat [] (Some v) \<Rightarrow> None
       | BagPat (b#l) None \<Rightarrow> (case fillVarsNextBagsInIRBag postp (b#l) vars
         of None \<Rightarrow> None
      | Some (acc', remains, vars') \<Rightarrow>
          (case freshVar vars' of newVar \<Rightarrow> Some (BagPat (acc@acc')
            (Some (newVar)), remains, (newVar)#vars')))
      | _ \<Rightarrow> None)"
| "fillVarsBagHasDotInIRBag (b#l) A postp acc vars = (case b of IdB x \<Rightarrow> None
               | ItemB x y z \<Rightarrow>
          (case searchBagWithNameInIRBag x (getListInIRBag A) of (al,as) \<Rightarrow>
               if al = [] then
            fillVarsBagHasDotInIRBag l A (postp@[ItemB x y z]) acc vars
     else (if Multiplicity Star \<in> set y then
          (case fillVarsSameBagsInIRBag y z al vars of None \<Rightarrow> None
              | Some (al', vars') \<Rightarrow>
               fillVarsBagHasDotInIRBag l (BagPat as (getVarInIRBag A)) postp (acc@al') vars')
      else (if length al > 1 then None
             else  (case fillVarsSameBagsInIRBag y z al vars of None \<Rightarrow> None
       | Some (al', vars') \<Rightarrow>
          fillVarsBagHasDotInIRBag l (BagPat as (getVarInIRBag A)) postp (acc@al') vars')))))"
| "fillVarsBagNoDotInIRBag [] A postp vars = (case A of (BagPat [] None)
   \<Rightarrow> if postp = [] then Some (BagPat [] None, vars) else None
     | (BagPat [] (Some x)) \<Rightarrow> Some (BagPat [] (Some x), vars)
      | _ \<Rightarrow> None)"
| "fillVarsBagNoDotInIRBag (b#l) A postp vars = (case b of IdB x \<Rightarrow> None
               | ItemB x y z \<Rightarrow>
         (case searchBagWithNameInIRBag x (getListInIRBag A) of (al, as)
          \<Rightarrow> if al = [] then fillVarsBagNoDotInIRBag l A (postp@[b]) vars
         else (if Multiplicity Star \<in> set y then
          (case fillVarsSameBagsInIRBag y z al vars of None \<Rightarrow> None
              | Some (al', vars') \<Rightarrow>
           (case fillVarsBagNoDotInIRBag l (BagPat as (getVarInIRBag A)) postp vars'
             of None \<Rightarrow> None
              | Some (l', varsa) \<Rightarrow> Some (mergeListToIRBag al' l', varsa)))
      else ( if length al > 1 then None
             else  (case fillVarsSameBagsInIRBag y z al vars of None \<Rightarrow> None
         | Some (al', vars') \<Rightarrow>
           (case fillVarsBagNoDotInIRBag l (BagPat as (getVarInIRBag A)) postp vars'
              of None \<Rightarrow> None
                 | Some (l', varsa) \<Rightarrow> Some (mergeListToIRBag al' l', varsa)))))))"
| "fillVarsNextBagsInIRBag [] A vars = Some ([], A, vars)"
| "fillVarsNextBagsInIRBag (b#l) A vars = (if A = [] then Some ([], [], vars)
     else (case b of IdB x \<Rightarrow> None
            | ItemB x y z \<Rightarrow>
           (case z of SUBag al \<Rightarrow>
    (case fillVarsBagHasDotInIRBag al (BagPat A None) [] [] vars of None \<Rightarrow> None
        | Some (acc', A', vars') \<Rightarrow> 
      (case fillVarsNextBagsInIRBag l A' vars' of None \<Rightarrow> None
          | Some (acca, Aa, varsa) \<Rightarrow>
                Some ((x,removeDotInFeatureList y,IRBag acc')#acca, Aa, varsa)))
            | _ \<Rightarrow> fillVarsNextBagsInIRBag l A vars)))"
| "fillVarsSameBagsInIRBag f p [] vars = Some ([], vars)"
| "fillVarsSameBagsInIRBag f p (b#l) vars = (case b of (x,y,z) \<Rightarrow>
       (case fillVarsInIRBigKWithBag f p z vars of None \<Rightarrow> None
              | Some (z', vars') \<Rightarrow>
          (case fillVarsSameBagsInIRBag f p l vars' of None \<Rightarrow> None
              | Some (l', varsa) \<Rightarrow>
                    Some ((x,(removeDotInFeatureList y),z')#l', varsa))))"
| "fillVarsInIRBigKWithBag f (SUBag a) S vars = (case S of (IRBag b) \<Rightarrow>
      (if DotDotDot \<in> set f then
        (case fillVarsBagHasDotInIRBag a b [] [] vars of None \<Rightarrow> None
            | Some (a', still, vars')
          \<Rightarrow> if still = [] then Some (IRBag a', vars') else None)
       else (case fillVarsBagNoDotInIRBag a b [] vars of None \<Rightarrow> None
            | Some (a', vars') \<Rightarrow>  Some (IRBag a', vars')))
          | _ \<Rightarrow> None)"
| "fillVarsInIRBigKWithBag f (SUK a) S vars =
     (case S of (IRK b) \<Rightarrow> Some (IRK b, vars) | _ \<Rightarrow> None)"
| "fillVarsInIRBigKWithBag f (SUList a) S vars =
      (case S of (IRList b) \<Rightarrow> Some (IRList b, vars) | _ \<Rightarrow> None)"
| "fillVarsInIRBigKWithBag f (SUSet a) S vars =
      (case S of (IRSet b) \<Rightarrow> Some (IRSet b, vars) | _ \<Rightarrow> None)"
| "fillVarsInIRBigKWithBag f (SUMap a) S vars =
     (case S of (IRMap b) \<Rightarrow> Some (IRMap b, vars) | _ \<Rightarrow> None)"
by pat_completeness auto

termination sorry

fun fillVarsBySearchBags :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
 \<Rightarrow> ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
       \<Rightarrow> 'metaVar metaVar list
       \<Rightarrow> (('var var * feature list *
                  ('upVar, 'var, 'metaVar) irBigKWithBag) list *
         ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
                        * 'metaVar metaVar list) option"
    and fillVarsBySearchBigKWithBag :: "('upVar, 'var, 'metaVar) suBigKWithBag
   \<Rightarrow> ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
 \<Rightarrow> ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
       \<Rightarrow> 'metaVar metaVar list
       \<Rightarrow> (('var var * feature list *
                  ('upVar, 'var, 'metaVar) irBigKWithBag) list *
         ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
                        * 'metaVar metaVar list) option" where
"fillVarsBySearchBags [] P acc vars = Some (acc, P, vars)"
| "fillVarsBySearchBags (b#l) P acc vars = (case b of IdB x \<Rightarrow> None
        | ItemB x y z \<Rightarrow> (case searchBagWithNameInIRBag x P of (al, ar)
           \<Rightarrow> if al = [] then
            (case fillVarsBySearchBigKWithBag z P acc vars of None \<Rightarrow> None
           | Some (acc', remain, varsa) \<Rightarrow> fillVarsBySearchBags l remain acc' varsa)
   else (case fillVarsSameBagsInIRBag y z al vars of None \<Rightarrow> None
            | Some (al', vars') \<Rightarrow>
       (case fillVarsBySearchBigKWithBag z ar (acc@al') vars' of None \<Rightarrow> None
           | Some (acc', remain, varsa) \<Rightarrow> fillVarsBySearchBags l remain acc' varsa))))"
| "fillVarsBySearchBigKWithBag (SUBag x) P acc vars = fillVarsBySearchBags x P acc vars"
| "fillVarsBySearchBigKWithBag X P acc vars = Some (acc, P, vars)"

definition notIdOfKLabel :: "('svar, 'metaVar) irKLabel \<Rightarrow> bool" where
"notIdOfKLabel a = (case a of (IRIdKLabel x) \<Rightarrow> False | _ \<Rightarrow> True)"

primrec mergeTwoIRBag :: "('upVar, 'var, 'metaVar) irBag
               \<Rightarrow> ('upVar, 'var, 'metaVar) irBag
              \<Rightarrow> ('upVar, 'var, 'metaVar) irBag option" where
"mergeTwoIRBag (BagPat a b) P = (case P of BagPat a' b' \<Rightarrow> 
        (case (b,b') of (None, None) \<Rightarrow> Some (BagPat (a@a') None)
             | (Some x, None) \<Rightarrow> Some (BagPat (a@a') (Some x))
             | (None, Some x) \<Rightarrow> Some (BagPat (a@a') (Some x))
             | _ \<Rightarrow> None))"

definition mergeBagTuple :: "('upVar, 'var, 'metaVar) irBag
     \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
        \<Rightarrow> (('upVar, 'var, 'metaVar) irBag *
           ('upVar, 'var, 'metaVar) suB list)
           \<Rightarrow> (('upVar, 'var, 'metaVar) irBag *
           ('upVar, 'var, 'metaVar) suB list) option" where
"mergeBagTuple a b t = (case t of (BagPat l v, y) \<Rightarrow>
       (case a of BagPat l' v' \<Rightarrow> (case (v,v') of (None, None) \<Rightarrow>
          Some (BagPat (l@l') None, y@b)
         | (Some u, None) \<Rightarrow> Some (BagPat (l@l') (Some u), y@b)
         | (None, Some u) \<Rightarrow> Some (BagPat (l@l') (Some u), y@b)
         | (Some u, Some w) \<Rightarrow> None)))"

fun getSubPattern :: "'var var \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> (feature list *
           ('upVar, 'var, 'metaVar) suBigKWithBag) option"
    and getSubPatternAux :: "'var var \<Rightarrow>
       ('upVar, 'var, 'metaVar) suBigKWithBag \<Rightarrow> (feature list *
           ('upVar, 'var, 'metaVar) suBigKWithBag) option" where
"getSubPattern x [] = None"
| "getSubPattern x (b#l) = (case b of IdB x \<Rightarrow> None
              | ItemB u v w \<Rightarrow> if u = x then Some (v,w) else
       (case getSubPatternAux x w of None \<Rightarrow> getSubPattern x l
             | Some tu \<Rightarrow> Some tu))"
| "getSubPatternAux x (SUBag y) = getSubPattern x y"
| "getSubPatternAux x y = None"

primrec ditachBag :: "('upVar, 'var, 'metaVar) bag
          \<Rightarrow> ((('upVar, 'var, 'metaVar) bag *
            ('upVar, 'var, 'metaVar) bag) list
         * ('upVar, 'var, 'metaVar) bag list
         * ('upVar, 'var, 'metaVar) bag list) option"
    and ditachBagR :: "('upVar, 'var, 'metaVar) bag rewrite
          \<Rightarrow> ((('upVar, 'var, 'metaVar) bag *
            ('upVar, 'var, 'metaVar) bag) list
         * ('upVar, 'var, 'metaVar) bag list
         * ('upVar, 'var, 'metaVar) bag list) option" where
"ditachBag UnitBag = Some ([],[],[])"
| "ditachBag (IdBag x) = None"
| "ditachBag (Xml x y z) = (if hasRewriteInBagR z then Some ([], [(Xml x y z)],[])
                          else Some ([], [], [(Xml x y z)]))"
| "ditachBag (SingleCell x y z) = (if hasRewriteInBigK z then Some ([], [(SingleCell x y z)],[])
                          else Some ([], [], [(SingleCell x y z)]))"
| "ditachBag (BagCon l r) = (case (ditachBagR l, ditachBagR r) of (Some (x,y,z), Some (u,v,w))
              \<Rightarrow> Some (x@u,y@v,z@w) | _ \<Rightarrow> None)"
| "ditachBagR (KTerm a) = ditachBag a"
| "ditachBagR (KRewrite a b) = (if (\<not> hasRewriteInBag a) \<and> (\<not> hasRewriteInBag b)
                then Some ([(a,b)],[],[]) else None)"

primrec ditachBagWithVars :: "('upVar, 'var, 'metaVar) bag
          \<Rightarrow> ((('upVar, 'var, 'metaVar) bag *
            ('upVar, 'var, 'metaVar) bag) list
         * ('upVar, 'var, 'metaVar) bag list
         * ('upVar, 'var, 'metaVar) bag list) option"
    and ditachBagRWithVars :: "('upVar, 'var, 'metaVar) bag rewrite
          \<Rightarrow> ((('upVar, 'var, 'metaVar) bag *
            ('upVar, 'var, 'metaVar) bag) list
         * ('upVar, 'var, 'metaVar) bag list
         * ('upVar, 'var, 'metaVar) bag list) option" where
"ditachBagWithVars UnitBag = Some ([],[],[])"
| "ditachBagWithVars (IdBag x) = None"
| "ditachBagWithVars (Xml x y z) = (if hasRewriteInBagR z then Some ([], [(Xml x y z)],[])
                          else Some ([], [], [(Xml x y z)]))"
| "ditachBagWithVars (SingleCell x y z) =
                (if hasRewriteInBigK z then Some ([], [(SingleCell x y z)],[])
                          else Some ([], [], [(SingleCell x y z)]))"
| "ditachBagWithVars (BagCon l r) =
         (case (ditachBagRWithVars l, ditachBagRWithVars r) of (Some (x,y,z), Some (u,v,w))
              \<Rightarrow> Some (x@u,y@v,z@w) | _ \<Rightarrow> None)"
| "ditachBagRWithVars (KTerm a) = ditachBagWithVars a"
| "ditachBagRWithVars (KRewrite a b) =
              (if (\<not> hasRewriteInBag a) \<and> (\<not> hasRewriteInBag b)
                then Some ([(a,b)],[],[]) else None)"

primrec searchBagWithNameInList ::
  "'var var \<Rightarrow>
       (('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list *
           ('upVar, 'var, 'metaVar) suB list) list
      \<Rightarrow> (('var var * feature list *
     ('upVar, 'var, 'metaVar) irBigKWithBag) list *
         ('upVar, 'var, 'metaVar) suB list * (('var var * feature list *
          ('upVar, 'var, 'metaVar) irBigKWithBag) list *
           ('upVar, 'var, 'metaVar) suB list) list
     * (('var var * feature list *
          ('upVar, 'var, 'metaVar) irBigKWithBag) list *
           ('upVar, 'var, 'metaVar) suB list) list)" where
"searchBagWithNameInList v [] = ([],[],[], [])"
| "searchBagWithNameInList v (b#l) = (case b of (x,y) \<Rightarrow>
       (case (searchBagWithNameInIRBag v x, searchBagWithName v y) of ((xl, xr),(yl, yr))
       \<Rightarrow> (case searchBagWithNameInList v l of
        (left, right, acc, changeAcc) \<Rightarrow>
          if xl = [] \<and> yl = [] then (left, right, b#acc, changeAcc) else
         if xr = [] \<and> yr = [] then
           (xl@left, yl@right, acc, changeAcc)
         else (xl@left, yl@right, acc, (xr, yr)#changeAcc))))"

function prepareBagTripleList
    and normalizeBagTripleList
    and prepareBagNoDot
    and normalizeBagNoDot
    and normalizeNextBag
    and normalizeInSUBigKWithBag where
 "prepareBagTripleList P [] [] [] vars acc database = 
       (case normalizeBagTripleList P acc vars database of None \<Rightarrow> None
         | Some (l, r, lrr, vars') \<Rightarrow> 
           if lrr = [] \<and> hasNoBagVarInSUBag r then
          (case freshVar vars' of newVar \<Rightarrow>
            Some (BagPat l (Some (newVar)), r@[IdB (newVar)],
                   (newVar)#vars')) else None)"
| "prepareBagTripleList P [] [] (b#l) vars acc database = (case toIRInBag b database of
         Some (BagPat x None) \<Rightarrow>
          (case fillVarsBySearchBags P x [] vars of None \<Rightarrow> None
            | Some (x', xr, vars') \<Rightarrow> if xr = [] then
             prepareBagTripleList P [] [] l vars' (acc@[(x',(irToSUInIRBagList x'))]) database
             else None) | _ \<Rightarrow> None)"
| "prepareBagTripleList P [] (b#l) L vars acc database = (case b of SingleCell x y z \<Rightarrow>
      (case (getLeftInBigK z, getRightInBigK z) of (Some zl, Some zr) \<Rightarrow>
         (case (toIRInBigK zl database, toSUInBigK zr) of (Some zl', Some zr') \<Rightarrow>
       prepareBagTripleList P [] l L vars (acc@[([(x,removeDotInFeatureList y,zl')],
                 [(ItemB x (removeDotInFeatureList y) zr')])]) database
        | _ \<Rightarrow> None) | _ \<Rightarrow> None)
       | Xml x y z \<Rightarrow> (case getSubPattern x P of None \<Rightarrow> None
            | Some (fl,P') \<Rightarrow>
         (case normalizeInSUBigKWithBag x y P' z vars database of None \<Rightarrow> None
          | Some (left, right, vars') \<Rightarrow>
           prepareBagTripleList P [] l L vars' (acc@[([left],[right])]) database))
         | _ \<Rightarrow> None)"
| "prepareBagTripleList P (b#l) R L vars acc database = (case b of (x,y) \<Rightarrow>
      (case (toIRInBag x database, toSUInBag y) of (Some (BagPat x' None), Some y') \<Rightarrow>
      (case fillVarsBySearchBags P x' [] vars of None \<Rightarrow> None
       | Some (xa, xr, varsa) \<Rightarrow>
          (case completeBagBySearchBags y' P [] of None \<Rightarrow> None
      | Some (ya, yr) \<Rightarrow> if xr = [] \<and> yr = [] then
       prepareBagTripleList P l R L varsa (acc@[(xa, ya)]) database else None))
        | _ \<Rightarrow> None))"
| "normalizeBagTripleList [] acc vars database = Some ([], [], acc, vars)"
| "normalizeBagTripleList (b#l) acc vars database = (case b of IdB x \<Rightarrow> None
            | ItemB x y z \<Rightarrow>
    (case searchBagWithNameInList x acc of (left, right, acc', accChange) \<Rightarrow>
     if acc' = [] then
             (case normalizeBagTripleList l accChange vars database of None \<Rightarrow> None
          | Some (lefta, righta, acca, varsa) \<Rightarrow> 
            Some (left@lefta, right@righta, acca, varsa))
   else (case normalizeNextBag z acc' vars database of None \<Rightarrow> None
       | Some (left', right', acca, vars') \<Rightarrow>
           (case normalizeBagTripleList l acca vars' database of None \<Rightarrow> None
          | Some (lefta, righta, accb, varsa) \<Rightarrow> 
         if left' = [] \<and> right' = [] then
            Some (left@lefta, right@righta, accb, varsa)
         else (case freshVar varsa of newVar \<Rightarrow>
  Some (left@[(x,removeDotInFeatureList y, IRBag (BagPat left' (Some (newVar))))]@lefta,
           right@[(ItemB x y (SUBag (right'@[IdB (newVar)])))]@righta, accb, varsa))))))"
| "normalizeNextBag a acc vars database = (case a of SUBag x \<Rightarrow>
    normalizeBagTripleList x acc vars database | _ \<Rightarrow> Some ([], [], acc, vars))"
| "normalizeInSUBigKWithBag x y S B vars database = (case S of SUBag T \<Rightarrow>
      (if DotDotDot \<in> set y then
       (case ditachBagR B of None \<Rightarrow> None
              | Some (u, v, w) \<Rightarrow>
    (case prepareBagTripleList T u v w vars [] database of None \<Rightarrow> None
       | Some (left, right, vars') \<Rightarrow> Some ((x, removeDotInFeatureList y, IRBag left),
              ItemB x (removeDotInFeatureList y) (SUBag right), vars')))
   else (case ditachBagRWithVars B of None \<Rightarrow> None
              | Some (u, v, w) \<Rightarrow>
       (case prepareBagNoDot T u v w vars (BagPat [] None, []) database of None \<Rightarrow> None
       | Some (left, right, vars') \<Rightarrow>
                  Some ((x, y, IRBag left), ItemB x y (SUBag right), vars'))))
       | _ \<Rightarrow> None)"
|  "prepareBagNoDot P [] [] [] vars acc database = (case normalizeBagNoDot P acc database 
      of None \<Rightarrow> None
      | Some (x,y) \<Rightarrow> Some (x,y,vars))"
| "prepareBagNoDot P [] [] (b#l) vars acc database = (case toIRInBag b database of
         Some (BagPat x y) \<Rightarrow>
          (case fillVarsBySearchBags P x [] vars of None \<Rightarrow> None
            | Some (x', xr, vars') \<Rightarrow> if xr = [] then
        (case mergeBagTuple (BagPat x' y) (irToSUInIRBagList x') acc of None \<Rightarrow> None
          | Some acc' \<Rightarrow> prepareBagNoDot P [] [] l vars' acc' database)
             else None) | _ \<Rightarrow> None)"
| "prepareBagNoDot P [] (b#l) L vars acc database = (case b of SingleCell x y z \<Rightarrow>
      (case (getLeftInBigK z, getRightInBigK z) of (Some zl, Some zr) \<Rightarrow>
         (case (toIRInBigK zl database, toSUInBigK zr) of (Some zl', Some zr') \<Rightarrow>
         (case mergeBagTuple (BagPat [(x,removeDotInFeatureList y,zl')] None)
                    [(ItemB x (removeDotInFeatureList y) zr')] acc of None \<Rightarrow> None
           | Some acc' \<Rightarrow> prepareBagNoDot P [] l L vars acc' database)
        | _ \<Rightarrow> None) | _ \<Rightarrow> None)
       | Xml x y z \<Rightarrow> (case getSubPattern x P of None \<Rightarrow> None
            | Some (fl,P') \<Rightarrow>
         (case normalizeInSUBigKWithBag x y P' z vars database of None \<Rightarrow> None
          | Some (left, right, vars') \<Rightarrow>
           (case mergeBagTuple (BagPat [left] None) [right] acc of None \<Rightarrow> None
              | Some acc' \<Rightarrow> prepareBagNoDot P [] l L vars' acc' database)))
         | _ \<Rightarrow> None)"
| "prepareBagNoDot P (b#l) R L vars acc database = (case b of (x,y) \<Rightarrow>
      (case (toIRInBag x database, toSUInBag y) of (Some (BagPat x' v), Some y') \<Rightarrow>
      (case fillVarsBySearchBags P x' [] vars of None \<Rightarrow> None
       | Some (xa, xr, varsa) \<Rightarrow>
          (case completeBagBySearchBags y' P [] of None \<Rightarrow> None
      | Some (ya, yr) \<Rightarrow> if xr = [] \<and> yr = [] then
       (case mergeBagTuple (BagPat xa v) ya acc of None \<Rightarrow> None
          | Some acc' \<Rightarrow>
       prepareBagNoDot P l R L varsa acc' database) else None))
        | _ \<Rightarrow> None))"
| "normalizeBagNoDot [] T database = (case T of (BagPat u v, y) \<Rightarrow> 
         if u = [] \<and> onlyIdInSUBag y then Some (BagPat [] v, y) else None)"
| "normalizeBagNoDot (b#l) T database = (case b of IdB x \<Rightarrow> None
         | ItemB x y z \<Rightarrow> (case T of (BagPat u v, y) \<Rightarrow>
        (case (searchBagWithNameInIRBag x u, searchBagWithName x y)
          of ((ul, ur), (yl, yr)) \<Rightarrow>
           (case normalizeBagNoDot l (BagPat ur v, yr) database of None \<Rightarrow> None
              | Some (BagPat u' v', y') \<Rightarrow> Some (BagPat (ul@u') v', yl@y')))))"
by pat_completeness auto

termination sorry

(* final k compile step *)
primrec updateFunInRules where
"updateFunInRules a [] = (case a of (s, x, y, z, rs) \<Rightarrow>
         if Owise \<in> set rs then Some [(FunPat s [] (Some (x,y,z)))]
          else Some [(FunPat s [(x,y,z)] None)])"
| "updateFunInRules a (b#l) = (case b of (FunPat s rl None) \<Rightarrow>
             (case a of (s', x, y, z, rs) \<Rightarrow>
     if s = s' then (if Owise \<in> set rs then Some ((FunPat s rl (Some (x,y,z)))#l)
                            else Some ((FunPat s (rl@[(x,y,z)]) None)#l))
          else (case updateFunInRules a l of None \<Rightarrow> None
                      | Some l' \<Rightarrow> Some (b#l')))
      | (FunPat s rl (Some r)) \<Rightarrow> (case a of (s', x, y, z, rs) \<Rightarrow>
      if s = s' then (if Owise \<in> set rs then None
                  else Some ((FunPat s (rl@[(x,y,z)]) (Some r))#l)) else
         (case updateFunInRules a l of None \<Rightarrow> None
                      | Some l' \<Rightarrow> Some (b#l')))
          | _ \<Rightarrow> None)"

(* a funtion to transfer rules in IR format to SUIR format with type check
   and does a lot of checks on valid rules
   Representing the core of compilation step *)
fun normalizeRules where
"normalizeRules [] Theory database subG = Some []"
| "normalizeRules ((KRule a b)#l) Theory database subG = (if hasRewriteInKR a then
     (case (getLeftInKR a, getRightInKR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInKR al database, toSUInKR ar) of (Some al', Some ar') \<Rightarrow>
           (if (hasHoleInPat al' \<or> hasHoleInSUK ar') then None else
         (if Macro \<in> set b then (case al' of
             (NormalPat (KMatching (KPat [IRKItem ala alb alty] None))) \<Rightarrow>
                 (case normalizeRules l Theory database subG of None \<Rightarrow> None 
              | Some l' \<Rightarrow> (case getIRKLabel ala of None \<Rightarrow> None
                    | Some ss \<Rightarrow>
                  if isFunctionItem ss database then None else Some ((MacroPat ss alb ar')#l')))
            (* not a necessary check isFunctionItem here. Adding only because of easy proof *)
             | _ \<Rightarrow> None)
          else if Anywhere \<in> set b then
  (case al' of (NormalPat (KMatching (KPat [IRKItem (IRKLabel ss) alb alty] None))) \<Rightarrow>
                 (case normalizeRules l Theory database subG of None \<Rightarrow> None 
    | Some l' \<Rightarrow> Some ((AnywherePat ss alb ar'
                   (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]))#l'))
       | _ \<Rightarrow> None)
          else (case al' of (KFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then 
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, (KFunPat ss alb), KSubs ar',
             (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]), b) l') else None
               | _ \<Rightarrow> (case al' of (NormalPat (KMatching ala))
                \<Rightarrow> (case normalizeRules l Theory database subG of None \<Rightarrow> None
                | Some l' \<Rightarrow> if Transition \<in> set b then
               Some ((KRulePat ala ar' (SUKItem (SUKLabel 
                         (ConstToLabel (BoolConst True))) [] [Bool]) True)#l')
             else Some ((KRulePat ala ar' (SUKItem (SUKLabel 
                         (ConstToLabel (BoolConst True))) [] [Bool]) False)#l'))
                 | _ \<Rightarrow> None))))
             | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((KRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInKR a then
     (case (getLeftInKR a, getRightInKR a) of (Some al, Some ar) \<Rightarrow>
   (case (toIRInKR al database, toSUInKR ar, toSUInKItem c) of
        (Some al', Some ar', Some c') \<Rightarrow>
       (if (hasHoleInPat al' \<or> hasHoleInSUK ar' \<or> hasHoleInSUKItem c') then None else
         (if Macro \<in> set b then None
          else if Anywhere \<in> set b then
              (case al' of (NormalPat (KMatching (KPat [IRKItem (IRKLabel ss) alb alty] None)))
                \<Rightarrow>
                 (case normalizeRules l Theory database subG of None \<Rightarrow> None 
    | Some l' \<Rightarrow> Some ((AnywherePat  ss alb ar' c')#l'))
       | _ \<Rightarrow> None)
          else (case al' of (KFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', KSubs ar', c', b) l') else None
               | _ \<Rightarrow> (case al' of (NormalPat (KMatching ala)) \<Rightarrow>
                (case normalizeRules l Theory database subG of None \<Rightarrow> None
                | Some l' \<Rightarrow> if Transition \<in> set b then Some ((KRulePat ala ar' c' True)#l')
                          else Some ((KRulePat ala ar' c' False)#l'))
                | _ \<Rightarrow> None))))
             | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((KItemRule a b)#l) Theory database subG = (if hasRewriteInKItemR a then
     (case (getLeftInKItemR a, getRightInKItemR a) of (Some al, Some ar) \<Rightarrow>
   (case (toIRInKItemR al database, toSUInKItemR ar) of (Some al', Some ar') \<Rightarrow>
           (if (hasHoleInPat al' \<or> hasHoleInSUKItem ar') then None else
         (if Macro \<in> set b then (case al' of
             (NormalPat (KItemMatching (IRKItem ala alb alty))) \<Rightarrow>
                 (case normalizeRules l Theory database subG of None \<Rightarrow> None 
              | Some l' \<Rightarrow> (case getIRKLabel ala of None \<Rightarrow> None
           | Some ss \<Rightarrow>
           if isFunctionItem ss database then None else Some ((MacroPat ss alb [ItemFactor ar'])#l')))
             (* not a necessary check isFunctionItem here. Adding only because of easy proof *)
             | _ \<Rightarrow> None)
          else if Anywhere \<in> set b then
         (case al' of (NormalPat (KItemMatching (IRKItem (IRKLabel ss) alb alty))) \<Rightarrow>
                 (case normalizeRules l Theory database subG of None \<Rightarrow> None 
    | Some l' \<Rightarrow> Some ((AnywherePat ss alb [ItemFactor ar']
                       (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]))#l'))
               | _ \<Rightarrow> None)
          else (case al' of (KItemFunPat ss alb) \<Rightarrow>
            (if isFunctionItem ss database then
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', KItemSubs ar',
                 (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]), b) l')
               else None)
               | _ \<Rightarrow> (case al' of (NormalPat (KItemMatching ala))
            \<Rightarrow> (case normalizeRules l Theory database subG of None \<Rightarrow> None
                | Some l' \<Rightarrow> if Transition \<in> set b then
                Some ((KRulePat (KPat [ala] None) [ItemFactor ar']
               (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) True)#l')
              else Some ((KRulePat (KPat [ala] None) [ItemFactor ar']
               (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#l'))))))
             | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((KItemRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInKItemR a then
     (case (getLeftInKItemR a, getRightInKItemR a) of (Some al, Some ar) \<Rightarrow>
   (case (toIRInKItemR al database, toSUInKItemR ar, toSUInKItem c) of
                      (Some al', Some ar', Some c') \<Rightarrow>
     (if (hasHoleInPat al' \<or> hasHoleInSUKItem ar' \<or> hasHoleInSUKItem c') then None else
         (if Macro \<in> set b then None
          else if Anywhere \<in> set b then
              (case al' of (NormalPat (KItemMatching (IRKItem (IRKLabel ss) alb alty)))
           \<Rightarrow> (case normalizeRules l Theory database subG of None \<Rightarrow> None 
    | Some l' \<Rightarrow>  Some ((AnywherePat ss alb
                               [ItemFactor ar'] c')#l'))  | _ \<Rightarrow> None)
          else (case al' of (KItemFunPat ss alb) \<Rightarrow>
            (if isFunctionItem ss database then
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow>
                    updateFunInRules (ss, al', KItemSubs ar', c', b) l') else None)
               | _ \<Rightarrow> (case al' of (NormalPat (KItemMatching ala))
             \<Rightarrow> (case normalizeRules l Theory database subG of None \<Rightarrow> None
                | Some l' \<Rightarrow> if Transition \<in> set b then
                    Some ((KRulePat (KPat [ala] None) [ItemFactor ar'] c' True)#l')
             else Some ((KRulePat (KPat [ala] None) [ItemFactor ar'] c' False)#l'))))))
             | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((KLabelRule a b)#l) Theory database subG = (if hasRewriteInKLabelR a then
     (case (getLeftInKLabelR a, getRightInKLabelR a) of (Some al, Some ar) \<Rightarrow>
   (case (toIRInKLabelR al database, toSUInKLabelR ar) of (Some al', Some ar') \<Rightarrow>
           (if (hasHoleInPat al' \<or> hasHoleInSUKLabel ar') then None else
         (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (KLabelFunPat ss alb) \<Rightarrow>
           if isFunctionItem ss database then
              (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', KLabelSubs ar',
                        (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]), b) l')
                  else None | _ \<Rightarrow> None)))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((KLabelRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInKLabelR a then
     (case (getLeftInKLabelR a, getRightInKLabelR a) of (Some al, Some ar) \<Rightarrow>
   (case (toIRInKLabelR al database, toSUInKLabelR ar, toSUInKItem c)
      of (Some al', Some ar', Some c') \<Rightarrow>
           (if (hasHoleInPat al' \<or> hasHoleInSUKLabel ar' \<or> hasHoleInSUKItem c') 
            then None else (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (KLabelFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', KLabelSubs ar', c', b) l')
        else None | _ \<Rightarrow> None)))
        | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((BagRule a b)#l) Theory database subG = (if hasRewriteInBagR a then
   (case ditachBagR a of None \<Rightarrow> None 
     | Some (u,v,w) \<Rightarrow> (case getConfiguration Theory of [P] \<Rightarrow>
     (case toSUInBag P of None \<Rightarrow> None | Some P' \<Rightarrow>
      (case prepareBagTripleList P' u v w (getAllMetaVarsInBagR a) [] database 
              of None \<Rightarrow> None
         | Some (al, ar, vars) \<Rightarrow>
      (if (hasHoleInIRBag al \<or> hasHoleInSUBag ar) then None else
         (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case normalizeRules l Theory database subG of None \<Rightarrow> None 
            | Some l' \<Rightarrow> if Transition \<in> set b then
             Some ((BagRulePat al ar
              (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) True)#l')
          else Some ((BagRulePat al ar
              (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#l'))))))
           | _ \<Rightarrow> None)) else None)"
| "normalizeRules ((BagRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInBagR a then
   (case ditachBagR a of None \<Rightarrow> None 
     | Some (u,v,w) \<Rightarrow> (case getConfiguration Theory of [P] \<Rightarrow>
     (case (toSUInBag P, toSUInKItem c) of (Some P', Some c') \<Rightarrow>
      (case prepareBagTripleList P' u v w (getAllMetaVarsInBagR a) [] database
         of None \<Rightarrow> None | Some (al, ar, vars) \<Rightarrow>
      (if (hasHoleInIRBag al \<or> hasHoleInSUBag ar) then None else
         (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case normalizeRules l Theory database subG of None \<Rightarrow> None 
            | Some l' \<Rightarrow> if Transition \<in> set b then
             Some ((BagRulePat al ar c' True)#l') else  Some ((BagRulePat al ar c' False)#l')))))
             | _ \<Rightarrow> None)
           | _ \<Rightarrow> None)) else None)"
| "normalizeRules ((ListRule a b)#l) Theory database subG = (if hasRewriteInListR a then
     (case (getLeftInListR a, getRightInListR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInListR al database, toSUInListR ar) of (Some al', Some ar') \<Rightarrow>
     (if (hasHoleInPat al' \<or> hasHoleInSUList ar') then None else
       (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (ListFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
              (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', ListSubs ar',
                  SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool], b) l')
                   else None | _ \<Rightarrow> None)))
           | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((ListRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInListR a then
     (case (getLeftInListR a, getRightInListR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInListR al database, toSUInListR ar, toSUInKItem c)
         of (Some al', Some ar', Some c') \<Rightarrow>
     (if (hasHoleInPat al' \<or> hasHoleInSUList ar' \<or> hasHoleInSUKItem c') then None else
       (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (ListFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
              (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', ListSubs ar', c', b) l')
                       else None | _ \<Rightarrow> None)))
           | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((SetRule a b)#l) Theory database subG = (if hasRewriteInSetR a then
     (case (getLeftInSetR a, getRightInSetR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInSetR al database, toSUInSetR ar) of (Some al', Some ar') \<Rightarrow>
     (if (hasHoleInPat al' \<or> hasHoleInSUSet ar') then None else
       (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (SetFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
              (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', SetSubs ar',
                  SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool], b) l')
          else None | _ \<Rightarrow> None)))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((SetRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInSetR a then
     (case (getLeftInSetR a, getRightInSetR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInSetR al database, toSUInSetR ar, toSUInKItem c)
         of (Some al', Some ar', Some c') \<Rightarrow>
     (if (hasHoleInPat al' \<or> hasHoleInSUSet ar' \<or> hasHoleInSUKItem c') then None else
       (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (SetFunPat ss alb) \<Rightarrow>
             if isFunctionItem ss database then
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', SetSubs ar', c', b) l')
        else None | _ \<Rightarrow> None)))
         | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((MapRule a b)#l) Theory database subG = (if hasRewriteInMapR a then
     (case (getLeftInMapR a, getRightInMapR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInMapR al database, toSUInMapR ar) of (Some al', Some ar') \<Rightarrow> 
     (if (hasHoleInPat al' \<or> hasHoleInSUMap ar') then None else
       (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (MapFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', MapSubs ar',
                  SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool], b) l')
     else None | _ \<Rightarrow> None)))
         | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((MapRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInMapR a then
     (case (getLeftInMapR a, getRightInMapR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInMapR al database, toSUInMapR ar, toSUInKItem c)
         of (Some al', Some ar', Some c') \<Rightarrow>
     (if (hasHoleInPat al' \<or> hasHoleInSUMap ar' \<or> hasHoleInSUKItem c') then None else
       (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (MapFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
              (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', MapSubs ar', c', b) l')
      else None | _ \<Rightarrow> None)))
         | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((Context a b)#l) Theory database subG = 
    (case a of (KItemC (KTerm (KLabelC ss)) alb alt) \<Rightarrow>
     if (isFunctionItem ss database \<or> \<not> validContextInKItem a
         \<or> Macro \<in> set b \<or> Anywhere \<in> set b) then None else
       (case locateHoleInKItem a of None \<Rightarrow> None
                    | Some ty \<Rightarrow> (if subsort ty KItem subG then
     (case (getLeftInKItem a, getRightInKItem a) of (Some al, Some ar) \<Rightarrow>
      (case freshVar (getAllMetaVarsInKItem al) of newVar \<Rightarrow>
      (case (toIRInKItem al database, toIRInKItem (fillHoleInKItem al (newVar) ty) database,
                  toSUInKItem (fillHoleInKItem ar (newVar) KResult))
         of (Some (NormalPat (KItemMatching alHole)),
                Some (NormalPat (KItemMatching al')), Some ar') \<Rightarrow>
       (case normalizeRules l Theory database subG of None \<Rightarrow> None 
          | Some l' \<Rightarrow>
         (case getResultSortInAttrs b of None \<Rightarrow>
    if Transition \<in> set b then
    Some ((KRulePat (KPat [al'] None) [ItemFactor (SUIdKItem (newVar) [ty]),
       ItemFactor (irToSUInKItem alHole)] (SUKItem (SUKLabel NotBool)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
          [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))] [Bool])]))] [Bool]) True)
        #((KRulePat (KPat [IRIdKItem (newVar) [KResult], alHole] None) [ItemFactor ar'] 
        (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) True)#l'))
  else Some ((KRulePat (KPat [al'] None) [ItemFactor (SUIdKItem (newVar) [ty]),
       ItemFactor (irToSUInKItem alHole)] (SUKItem (SUKLabel NotBool)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
          [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))] [Bool])]))] [Bool]) False)
        #((KRulePat (KPat [IRIdKItem (newVar) [KResult], alHole] None) [ItemFactor ar'] 
        (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#l'))
         | Some resultT \<Rightarrow>
          (case meet [KResult] [resultT] subG of [] \<Rightarrow> None
          | resultT' \<Rightarrow> if Transition \<in> set b then
     Some ((KRulePat (KPat [al'] None) [ItemFactor (SUIdKItem (newVar) [ty]),
       ItemFactor (irToSUInKItem alHole)] (SUKItem (SUKLabel NotBool)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))] [Bool])]))] [Bool]) True)
        #((KRulePat (KPat [IRIdKItem (newVar) resultT', alHole] None) [ItemFactor ar'] 
          (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) True)#l'))
    else Some ((KRulePat (KPat [al'] None) [ItemFactor (SUIdKItem (newVar) [ty]),
       ItemFactor (irToSUInKItem alHole)] (SUKItem (SUKLabel NotBool)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))] [Bool])]))] [Bool]) False)
        #((KRulePat (KPat [IRIdKItem (newVar) resultT', alHole] None) [ItemFactor ar'] 
          (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#l')))))
                   | _ \<Rightarrow> None)) | _ \<Rightarrow> None) else None)) | _ \<Rightarrow> None)"
| "normalizeRules ((ContextWithCon a c b)#l) Theory database subG =
    (case a of (KItemC (KTerm (KLabelC ss)) alb alt) \<Rightarrow>
     if (isFunctionItem ss database \<or> \<not> validContextInKItem a
         \<or> Macro \<in> set b \<or> Anywhere \<in> set b) then None else
       (case locateHoleInKItem a of None \<Rightarrow> None
                    | Some ty \<Rightarrow>
   (if subsort ty KItem subG then
     (case (getLeftInKItem a, getRightInKItem a, toSUInKItem c)
       of (Some al, Some ar, Some c') \<Rightarrow>
      if hasHoleInSUKItem c' then None else
      (case freshVar (getAllMetaVarsInKItem al) of newVar \<Rightarrow>
       (case (toIRInKItem al database, toIRInKItem (fillHoleInKItem al (newVar) ty) database,
                  toSUInKItem (fillHoleInKItem ar (newVar) KResult))
         of (Some (NormalPat (KItemMatching alHole)),
                 Some (NormalPat (KItemMatching al')), Some ar') \<Rightarrow>
       (case normalizeRules l Theory database subG of None \<Rightarrow> None 
          | Some l' \<Rightarrow>
         (case getResultSortInAttrs b of None \<Rightarrow>
          if Transition \<in> set b then
    Some ((KRulePat (KPat [al'] None) [ItemFactor (SUIdKItem (newVar) [ty]),
            ItemFactor (irToSUInKItem alHole)]
        (SUKItem (SUKLabel AndBool) [ItemKl (SUBigBag (SUK [ItemFactor c'])),
        ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel NotBool)
    [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))]
       [Bool])]))] [Bool])]))] [Bool]) True)
        #((KRulePat (KPat [IRIdKItem (newVar) [KResult], alHole] None) [ItemFactor ar'] 
            (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) True)#l'))
   else Some ((KRulePat (KPat [al'] None) [ItemFactor (SUIdKItem (newVar) [ty]),
            ItemFactor (irToSUInKItem alHole)]
        (SUKItem (SUKLabel AndBool) [ItemKl (SUBigBag (SUK [ItemFactor c'])),
        ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel NotBool)
    [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))]
       [Bool])]))] [Bool])]))] [Bool]) False)
        #((KRulePat (KPat [IRIdKItem (newVar) [KResult], alHole] None) [ItemFactor ar'] 
            (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#l'))
         | Some resultT \<Rightarrow>
          (case meet [KResult] [resultT] subG of [] \<Rightarrow> None
          | resultT' \<Rightarrow> if Transition \<in> set b then
     Some ((KRulePat (KPat [al'] None)
             [ItemFactor (SUIdKItem (newVar) [ty]), ItemFactor (irToSUInKItem alHole)]
        (SUKItem (SUKLabel AndBool) [ItemKl (SUBigBag (SUK [ItemFactor c'])),
           ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel NotBool)
           [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
                [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))]
        [Bool])]))] [Bool])]))] [Bool]) True)
        #((KRulePat (KPat [IRIdKItem (newVar) resultT', alHole] None) [ItemFactor ar'] 
           (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) True)#l'))
     else Some ((KRulePat (KPat [al'] None)
             [ItemFactor (SUIdKItem (newVar) [ty]), ItemFactor (irToSUInKItem alHole)]
        (SUKItem (SUKLabel AndBool) [ItemKl (SUBigBag (SUK [ItemFactor c'])),
           ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel NotBool)
           [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
                [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))]
        [Bool])]))] [Bool])]))] [Bool]) False)
        #((KRulePat (KPat [IRIdKItem (newVar) resultT', alHole] None) [ItemFactor ar'] 
           (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#l')))))
                   | _ \<Rightarrow> None)) | _ \<Rightarrow> None) else None)) | _ \<Rightarrow> None)"

end
