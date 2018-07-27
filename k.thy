theory k
imports Main Real List kSyntax kSort kGetters
begin

(*
assume that the parser will remove the following cases and make K to KItem:

A:K \<leadsto> c ...  becomes A:KItem \<leadsto> c ...

... c \<leadsto> A:K \<leadsto> c ... becomes ... c \<leadsto> A:KItem \<leadsto> c ...

... c \<leadsto> A:K \<leadsto> B:K becomes c \<leadsto> A:KItem \<leadsto> B:K

hence, left vars do not apply on the K case.

*)

(* translate pattern in K core to K IR *)

(* implementation of krun and ksearch *)

(* type check terms *)
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

primrec hasIdInKList where
"hasIdInKList [] = False"
| "hasIdInKList (a#l) = (case a of IdKl x \<Rightarrow> True | _ \<Rightarrow> hasIdInKList l)"

primrec numberOfItemsInKList where
"numberOfItemsInKList [] = 0"
| "numberOfItemsInKList (x#l) = (case x of IdKl a \<Rightarrow> numberOfItemsInKList l
          | ItemKl a \<Rightarrow> 1 + numberOfItemsInKList l)"

fun getIdInSUKLabel where
"getIdInSUKLabel (SUIdKLabel a) = Some a"
| "getIdInSUKLabel a = None"

fun isFunctionItemAux where
"isFunctionItemAux [] s = False"
| "isFunctionItemAux ((a,b, SingleTon t, nl, True)#l) s =
     (if (t = s) then True else isFunctionItemAux l s)"
| "isFunctionItemAux ((a,b, SetTon t, nl, True)#l) s =
     (if (t s) then True else isFunctionItemAux l s)"
| "isFunctionItemAux ((a,b, t, nl, False)#l) s = isFunctionItemAux l s"

definition isFunctionItem where
"isFunctionItem s database = isFunctionItemAux database s"

(* check if a kitem is contained in a structure, no function terms
    only used for checking correctness of configurations *)
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

primrec flattenSetAux where
"flattenSetAux [] = []"
| "flattenSetAux (x#xl) = (SetPat [x] None)#(flattenSetAux xl)"

primrec flattenSetVar where
"flattenSetVar None = []"
| "flattenSetVar (Some v) = [SetPat [] (Some v)]"

primrec flattenSet where
"flattenSet [] = Some []"
| "flattenSet (x#xl) = (case (flattenSet xl) of None \<Rightarrow> None
             | Some xl' \<Rightarrow> (case x of IRBigBag (IRSet (SetPat sl sv))
                  \<Rightarrow>  Some ((flattenSetAux sl)@(flattenSetVar sv)@xl')
                    | _ \<Rightarrow> None))"

primrec restructSet where
"restructSet [] = Some (SetPat [] None)"
| "restructSet (x#xl) = (case (restructSet xl) of None \<Rightarrow> None
             | Some (SetPat sl None) \<Rightarrow> (case x of SetPat sl' None
                   \<Rightarrow> Some (SetPat (sl'@sl) None)
                  | SetPat sl' (Some v) \<Rightarrow> Some (SetPat (sl'@sl) (Some v)))
              | Some (SetPat sl (Some v)) \<Rightarrow> (case x of SetPat sl' None
                  \<Rightarrow> Some (SetPat (sl'@sl) (Some v))
                   | SetPat sl' (Some v') \<Rightarrow> None))"

primrec flattenMapAux where
"flattenMapAux [] = []"
| "flattenMapAux (x#xl) = (MapPat [x] None)#(flattenMapAux xl)"

primrec flattenMapVar where
"flattenMapVar None = []"
| "flattenMapVar (Some v) = [MapPat [] (Some v)]"

primrec flattenMap where
"flattenMap [] = Some []"
| "flattenMap (x#xl) = (case (flattenMap xl) of None \<Rightarrow> None
             | Some xl' \<Rightarrow> (case x of IRBigBag (IRMap (MapPat sl sv))
                  \<Rightarrow>  Some ((flattenMapAux sl)@(flattenMapVar sv)@xl')
                    | _ \<Rightarrow> None))"

primrec restructMap where
"restructMap [] = Some (MapPat [] None)"
| "restructMap (x#xl) = (case (restructMap xl) of None \<Rightarrow> None
             | Some (MapPat sl None) \<Rightarrow> (case x of MapPat sl' None
                   \<Rightarrow> Some (MapPat (sl'@sl) None)
                  | MapPat sl' (Some v) \<Rightarrow> Some (MapPat (sl'@sl) (Some v)))
              | Some (MapPat sl (Some v)) \<Rightarrow> (case x of MapPat sl' None
                  \<Rightarrow> Some (MapPat (sl'@sl) (Some v))
                   | MapPat sl' (Some v') \<Rightarrow> None))"

primrec flattenListAux where
"flattenListAux [] = []"
| "flattenListAux (x#xl) = (ListPatNoVar [x])#(flattenListAux xl)"

primrec flattenList where
"flattenList [] = Some []"
| "flattenList (x#xl) = (case (flattenList xl) of None \<Rightarrow> None
             | Some xl' \<Rightarrow> (case x of IRBigBag (IRList (ListPatNoVar sl))
                  \<Rightarrow>  Some ((flattenListAux sl)@xl')
               | IRBigBag (IRList (ListPat sl1 v sl2))
                  \<Rightarrow> Some ((flattenListAux sl1)@([ListPat [] v []])@(flattenListAux sl2)@xl')
                    | _ \<Rightarrow> None))"

primrec restructList where
"restructList [] = Some (ListPatNoVar [])"
| "restructList (x#xl) = (case (restructList xl) of None \<Rightarrow> None
             | Some (ListPatNoVar sl) \<Rightarrow> (case x of ListPatNoVar sl'
                   \<Rightarrow> Some (ListPatNoVar (sl'@sl))
                  | ListPat sl1 v sl2 \<Rightarrow> Some (ListPat sl1 v (sl2@sl)))
              | Some (ListPat sl1 v sl2) \<Rightarrow> (case x of ListPatNoVar sl'
                  \<Rightarrow> Some (ListPat (sl'@sl1) v sl2)
                   | ListPat sl1' v' sl2' \<Rightarrow> None))"

fun simpleKToIR and simpleKToIRKList where 
"simpleKToIR (SimId x y) database =
   (case y of KLabel \<Rightarrow> Some (NormalPat (KLabelMatching (IRIdKLabel x)))
      | KList \<Rightarrow> Some (NormalPat (KListMatching (KListPat [] x [])))
      | K \<Rightarrow> Some (NormalPat (KMatching (KPat [] (Some x))))
      | List \<Rightarrow> Some (NormalPat (ListMatching (ListPat [] x [])))
      | Set \<Rightarrow> Some (NormalPat (SetMatching (SetPat [] (Some x))))
      | Map \<Rightarrow> Some (NormalPat (MapMatching (MapPat [] (Some x))))
      | Bag \<Rightarrow> Some (NormalPat (BagMatching (BagPat [] (Some x))))
      | _ \<Rightarrow> Some (NormalPat (KItemMatching (IRIdKItem x [y]))))"
| "simpleKToIR (SimEmpty y) database =
     (case y of KList \<Rightarrow> Some (NormalPat (KListMatching (KListPatNoVar [])))
      | K \<Rightarrow> Some (NormalPat (KMatching (KPat [] None)))
      | List \<Rightarrow> Some (NormalPat (ListMatching (ListPatNoVar [])))
      | Set \<Rightarrow> Some (NormalPat (SetMatching (SetPat [] None)))
      | Map \<Rightarrow> Some (NormalPat (MapMatching (MapPat [] None)))
      | Bag \<Rightarrow> Some (NormalPat (BagMatching (BagPat [] None)))
      | _ \<Rightarrow> Some (NormalPat (KItemMatching (IRKItem (IRKLabel (UnitLabel y)) (KListPatNoVar []) [y]))))"
| "simpleKToIR (SimLabel l) database = Some (NormalPat (KLabelMatching (IRKLabel l)))"
| "simpleKToIR (SimBag x y b) database = (case simpleKToIR b database of
       Some (NormalPat (KItemMatching s)) \<Rightarrow> Some (NormalPat
                  (BagMatching (BagPat [(x,y,IRK (KPat [s] None))] None)))
    | Some (NormalPat (KMatching s)) \<Rightarrow> Some (NormalPat
                  (BagMatching (BagPat [(x,y,IRK s)] None)))
    | Some (NormalPat (ListMatching s)) \<Rightarrow> Some (NormalPat
                  (BagMatching (BagPat [(x,y,IRList s)] None)))
    | Some (NormalPat (SetMatching s)) \<Rightarrow> Some (NormalPat
                  (BagMatching (BagPat [(x,y,IRSet s)] None)))
    | Some (NormalPat (MapMatching s)) \<Rightarrow> Some (NormalPat
                  (BagMatching (BagPat [(x,y,IRMap s)] None)))
    | Some (NormalPat (BagMatching s)) \<Rightarrow> Some (NormalPat
                  (BagMatching (BagPat [(x,y,IRBag s)] None)))
    | _ \<Rightarrow> None)"
| "simpleKToIR (SimBagCon l r) database = (case simpleKToIR l database of
      Some (NormalPat (BagMatching (BagPat sl v))) \<Rightarrow> 
       (case simpleKToIR r database of
          Some (NormalPat (BagMatching (BagPat sl' v'))) \<Rightarrow>
               (case v of None \<Rightarrow> Some (NormalPat (BagMatching (BagPat (sl@sl') v')))
                | Some n \<Rightarrow> (case v' of None \<Rightarrow> Some (NormalPat (BagMatching (BagPat (sl@sl') v)))
                    | Some n' \<Rightarrow> None)) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "simpleKToIR (SimTerm l kl) database =
    (case simpleKToIRKList kl database of None \<Rightarrow> None
       | Some kl' \<Rightarrow> 
         (if isFunctionItem l database then (case getSort l database of None \<Rightarrow> None
           | Some t \<Rightarrow> if t = [KLabel] then Some (KLabelFunPat l kl')
                else if t = [K] then Some (KFunPat l kl')
                   else if t = [List] then Some (ListFunPat l kl')
                  else if t = [Set] then Some (SetFunPat l kl')
                 else if t = [Map] then Some (MapFunPat l kl')
                   else Some (KItemFunPat l kl'))
          else (case l of SetItemLabel \<Rightarrow> 
             (case kl' of (KListPatNoVar [(IRBigBag (IRK kx))])
                          \<Rightarrow> Some (NormalPat ( SetMatching (SetPat [kx] None))) | _ \<Rightarrow> None)
             | ListItemLabel \<Rightarrow> (case kl' of (KListPatNoVar [(IRBigBag (IRK kx))])
                          \<Rightarrow> Some (NormalPat (ListMatching (ListPatNoVar [kx]))) | _ \<Rightarrow> None)
             | MapItemLabel \<Rightarrow> (case kl' of (KListPatNoVar [(IRBigBag (IRK kx)),(IRBigBag (IRK ky))])
                          \<Rightarrow> Some (NormalPat (MapMatching (MapPat [(kx, ky)] None))) | _ \<Rightarrow> None)
             | SetConLabel \<Rightarrow> (case kl' of (KListPatNoVar newkl)
                  \<Rightarrow> (case flattenSet newkl of None \<Rightarrow> None
                       | Some sl \<Rightarrow> (case restructSet sl of None \<Rightarrow> None
                           | Some sl' \<Rightarrow> Some (NormalPat (SetMatching sl')))) | _ \<Rightarrow> None)
             | MapConLabel \<Rightarrow> (case kl' of (KListPatNoVar newkl)
                  \<Rightarrow> (case flattenMap newkl of None \<Rightarrow> None
                       | Some sl \<Rightarrow> (case restructMap sl of None \<Rightarrow> None
                           | Some sl' \<Rightarrow> Some (NormalPat (MapMatching sl')))) | _ \<Rightarrow> None)
             | ListConLabel \<Rightarrow> (case kl' of (KListPatNoVar newkl)
                  \<Rightarrow> (case flattenList newkl of None \<Rightarrow> None
                       | Some sl \<Rightarrow> (case restructList sl of None \<Rightarrow> None
                           | Some sl' \<Rightarrow> Some (NormalPat (ListMatching sl')))) | _ \<Rightarrow> None)
            | _ \<Rightarrow> (case getSort l database of None \<Rightarrow> None
                 | Some t \<Rightarrow> Some (NormalPat (KItemMatching (IRKItem (IRKLabel l) kl' t)))))))"
| "simpleKToIRKList [] database = Some (KListPatNoVar [])"
| "simpleKToIRKList (x#xl) database = (case (simpleKToIRKList xl database) of None \<Rightarrow> None
          | Some (KListPatNoVar xl') \<Rightarrow> 
          (case simpleKToIR x database of None \<Rightarrow> None
              | Some (NormalPat (KListMatching (KListPatNoVar sl))) \<Rightarrow> Some (KListPatNoVar (sl@xl'))
            | Some (NormalPat (KListMatching (KListPat sl v sl'))) \<Rightarrow> Some (KListPat sl v (sl'@xl'))
           | Some (NormalPat (KLabelMatching x')) \<Rightarrow> Some (KListPatNoVar ((IRBigLabel x')#xl'))
           | Some (NormalPat (KMatching x')) \<Rightarrow> Some (KListPatNoVar ((IRBigBag (IRK x'))#xl'))
           | Some (NormalPat (ListMatching x')) \<Rightarrow> Some (KListPatNoVar ((IRBigBag (IRList x'))#xl'))
           | Some (NormalPat (SetMatching x')) \<Rightarrow> Some (KListPatNoVar ((IRBigBag (IRSet x'))#xl'))
           | Some (NormalPat (MapMatching x')) \<Rightarrow> Some (KListPatNoVar ((IRBigBag (IRMap x'))#xl'))
           | Some (NormalPat (BagMatching x')) \<Rightarrow> Some (KListPatNoVar ((IRBigBag (IRBag x'))#xl'))
           | Some (NormalPat (KItemMatching x')) \<Rightarrow> Some (KListPatNoVar ((IRBigBag (IRK (KPat [x'] None)))#xl'))
           | _ \<Rightarrow> None)
      | Some (KListPat xl1 u xl2) \<Rightarrow> (case simpleKToIR x database of None \<Rightarrow> None
              | Some (NormalPat (KListMatching (KListPatNoVar sl))) \<Rightarrow> Some (KListPat (sl@xl1) u xl2)
           | Some (NormalPat (KLabelMatching x')) \<Rightarrow> Some (KListPat ((IRBigLabel x')#xl1) u xl2)
           | Some (NormalPat (KMatching x')) \<Rightarrow> Some (KListPat ((IRBigBag (IRK x'))#xl1) u xl2)
           | Some (NormalPat (ListMatching x')) \<Rightarrow> Some (KListPat ((IRBigBag (IRList x'))#xl1) u xl2)
           | Some (NormalPat (SetMatching x')) \<Rightarrow> Some (KListPat ((IRBigBag (IRSet x'))#xl1) u xl2)
           | Some (NormalPat (MapMatching x')) \<Rightarrow> Some (KListPat ((IRBigBag (IRMap x'))#xl1) u xl2)
           | Some (NormalPat (BagMatching x')) \<Rightarrow> Some (KListPat ((IRBigBag (IRBag x'))#xl1) u xl2)
           | Some (NormalPat (KItemMatching x')) \<Rightarrow> Some (KListPat ((IRBigBag (IRK (KPat [x'] None)))#xl1) u xl2)
           | _ \<Rightarrow> None))"

primrec flattenSUSet where
"flattenSUSet [] = Some []"
| "flattenSUSet (x#xl) = (case (flattenSUSet xl) of None \<Rightarrow> None
             | Some xl' \<Rightarrow> (case x of ItemKl (SUBigBag (SUSet sl)) \<Rightarrow>  Some (sl@xl')
                    | _ \<Rightarrow> None))"

primrec flattenSUMap where
"flattenSUMap [] = Some []"
| "flattenSUMap (x#xl) = (case (flattenSUMap xl) of None \<Rightarrow> None
             | Some xl' \<Rightarrow> (case x of ItemKl (SUBigBag (SUMap sl)) \<Rightarrow>  Some (sl@xl')
                    | _ \<Rightarrow> None))"

primrec flattenSUList where
"flattenSUList [] = Some []"
| "flattenSUList (x#xl) = (case (flattenSUList xl) of None \<Rightarrow> None
             | Some xl' \<Rightarrow> (case x of ItemKl (SUBigBag (SUList sl)) \<Rightarrow>  Some (sl@xl')
                    | _ \<Rightarrow> None))"

fun simpleKToSU and simpleKToSUKList where 
"simpleKToSU (SimId x y) database =
   (case y of KLabel \<Rightarrow> Some (KLabelSubs (SUIdKLabel x))
      | KList \<Rightarrow> Some (KListSubs [(IdKl x)])
      | K \<Rightarrow> Some (KSubs [IdFactor x])
      | List \<Rightarrow> Some (ListSubs [IdL x])
      | Set \<Rightarrow> Some (SetSubs [IdS x])
      | Map \<Rightarrow> Some (MapSubs [IdM x])
      | Bag \<Rightarrow> Some (BagSubs [IdB x])
      | _ \<Rightarrow> Some (KItemSubs (SUIdKItem x [y])))"
| "simpleKToSU (SimEmpty y) database =
     (case y of KList \<Rightarrow> Some (KListSubs [])
      | K \<Rightarrow> Some (KSubs [])
      | List \<Rightarrow> Some (ListSubs [])
      | Set \<Rightarrow> Some (SetSubs [])
      | Map \<Rightarrow> Some (MapSubs [])
      | Bag \<Rightarrow> Some (BagSubs [])
      | _ \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (UnitLabel y)) [] [y])))"
| "simpleKToSU (SimLabel l) database = Some (KLabelSubs (SUKLabel l))"
| "simpleKToSU (SimBag x y b) database = (case simpleKToSU b database of
       Some (KItemSubs s) \<Rightarrow> Some
                  (BagSubs [(ItemB x y (SUK [ItemFactor s]))])
    | Some (KSubs s) \<Rightarrow> Some
                  (BagSubs [(ItemB x y (SUK s))])
    | Some (ListSubs s) \<Rightarrow> Some
                  (BagSubs [(ItemB x y (SUList s))])
    | Some (SetSubs s) \<Rightarrow> Some
                  (BagSubs [(ItemB x y (SUSet s))])
    | Some (MapSubs s) \<Rightarrow> Some
                  (BagSubs [(ItemB x y (SUMap s))])
    | Some (BagSubs s) \<Rightarrow> Some
                  (BagSubs [(ItemB x y (SUBag s))])
    | _ \<Rightarrow> None)"
| "simpleKToSU (SimBagCon l r) database = (case simpleKToSU l database of
      Some (BagSubs l') \<Rightarrow> 
       (case simpleKToSU r database of
          Some (BagSubs r') \<Rightarrow> Some (BagSubs (l'@r')) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "simpleKToSU (SimTerm l kl) database =
    (case simpleKToSUKList kl database of None \<Rightarrow> None
       | Some kl' \<Rightarrow> 
         (if isFunctionItem l database then (case getSort l database of None \<Rightarrow> None
           | Some t \<Rightarrow> if t = [KLabel] then Some (KLabelSubs (SUKLabelFun (SUKLabel l) kl'))
                else if t = [K] then Some (KSubs [SUKKItem (SUKLabel l) kl' [K]])
                   else if t = [List] then Some (ListSubs [SUListKItem (SUKLabel l) kl'])
                  else if t = [Set] then Some (SetSubs [SUSetKItem (SUKLabel l) kl'])
                 else if t = [Map] then Some (MapSubs [SUMapKItem (SUKLabel l) kl'])
                   else Some (KItemSubs (SUKItem (SUKLabel l) kl' t)))
          else (case l of SetItemLabel \<Rightarrow> 
             (case kl' of [ItemKl (SUBigBag (SUK kx))]
                          \<Rightarrow> Some (SetSubs [ItemS kx]) | _ \<Rightarrow> None)
             | ListItemLabel \<Rightarrow> (case kl' of [ItemKl (SUBigBag (SUK kx))]
                          \<Rightarrow> Some (ListSubs [ItemL kx]) | _ \<Rightarrow> None)
             | MapItemLabel \<Rightarrow> (case kl' of [ItemKl (SUBigBag (SUK kx)), ItemKl (SUBigBag (SUK ky))]
                          \<Rightarrow> Some (MapSubs [ItemM kx ky]) | _ \<Rightarrow> None)
             | SetConLabel \<Rightarrow> (case flattenSUSet kl' of Some newkl \<Rightarrow> Some (SetSubs newkl) | _ \<Rightarrow> None)
             | MapConLabel \<Rightarrow> (case flattenSUMap kl' of Some newkl \<Rightarrow> Some (MapSubs newkl) | _ \<Rightarrow> None)
             | ListConLabel \<Rightarrow>(case flattenSUList kl' of Some newkl \<Rightarrow> Some (ListSubs newkl) | _ \<Rightarrow> None)
            | _ \<Rightarrow> (case getSort l database of None \<Rightarrow> None
                 | Some t \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel l) kl' t))))))"
| "simpleKToSUKList [] database = Some []"
| "simpleKToSUKList (x#xl) database = (case (simpleKToSUKList xl database) of None \<Rightarrow> None
          | Some xl' \<Rightarrow> 
          (case simpleKToSU x database of None \<Rightarrow> None
              | Some (KListSubs sl) \<Rightarrow> Some (sl@xl')
           | Some (KLabelSubs x') \<Rightarrow> Some ((ItemKl (SUBigLabel x'))#xl')
           | Some (KSubs x') \<Rightarrow> Some ((ItemKl (SUBigBag (SUK x')))#xl')
           | Some (ListSubs x') \<Rightarrow> Some ((ItemKl (SUBigBag (SUList x')))#xl')
           | Some (SetSubs x') \<Rightarrow> Some ((ItemKl (SUBigBag (SUSet x')))#xl')
           | Some (MapSubs x') \<Rightarrow> Some ((ItemKl (SUBigBag (SUMap x')))#xl')
           | Some (BagSubs x') \<Rightarrow> Some ((ItemKl (SUBigBag (SUBag x')))#xl')
           | Some (KItemSubs x') \<Rightarrow> Some ((ItemKl (SUBigBag (SUK [ItemFactor x'])))#xl')))"

fun tupleToRulePat where
"tupleToRulePat (x,y,z,u) database = (if Macro \<in> set u then 
     (case simpleKToIR x database of Some (NormalPat (KItemMatching (IRKItem (IRKLabel l) kl t)))
        \<Rightarrow> (case simpleKToSU y database of Some (KItemSubs y')
              \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
             \<Rightarrow>  (case getKLabelInSUKItem z' of Some (ConstToLabel (BoolConst True))
                     \<Rightarrow> Some (MacroPat l kl [ItemFactor y']) | _ \<Rightarrow> None) | _ \<Rightarrow> None)
                   | Some (KSubs y') \<Rightarrow>
                        (case simpleKToSU z database of Some (KItemSubs z')
             \<Rightarrow>  (case getKLabelInSUKItem z' of Some (ConstToLabel (BoolConst True))
                     \<Rightarrow> Some (MacroPat l kl y') | _ \<Rightarrow> None) | _ \<Rightarrow> None)
                     | _ \<Rightarrow> None)
        | Some (NormalPat (KMatching (KPat [IRKItem (IRKLabel l) kl t] None)))
        \<Rightarrow> (case simpleKToSU y database of Some (KItemSubs y')
              \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
             \<Rightarrow>  (case getKLabelInSUKItem z' of Some (ConstToLabel (BoolConst True))
                     \<Rightarrow> Some (MacroPat l kl [ItemFactor y']) | _ \<Rightarrow> None) | _ \<Rightarrow> None)
                   | Some (KSubs y') \<Rightarrow>
                        (case simpleKToSU z database of Some (KItemSubs z')
             \<Rightarrow>  (case getKLabelInSUKItem z' of Some (ConstToLabel (BoolConst True))
                     \<Rightarrow> Some (MacroPat l kl y') | _ \<Rightarrow> None) | _ \<Rightarrow> None)
                     | _ \<Rightarrow> None) | _ \<Rightarrow> None)
        else if Anywhere \<in> set u then
         (case simpleKToIR x database of Some (NormalPat (KItemMatching (IRKItem (IRKLabel l) kl t)))
        \<Rightarrow> (case simpleKToSU y database of Some (KItemSubs y')
              \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                     \<Rightarrow> Some (AnywherePat l kl [ItemFactor y'] z') | _ \<Rightarrow> None)
                   | Some (KSubs y') \<Rightarrow>
                (case simpleKToSU z database of Some (KItemSubs z')
                     \<Rightarrow> Some (AnywherePat l kl y' z') | _ \<Rightarrow> None)
                     | _ \<Rightarrow> None)
        | Some (NormalPat (KMatching (KPat [IRKItem (IRKLabel l) kl t] None)))
        \<Rightarrow> (case simpleKToSU y database of Some (KItemSubs y')
              \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                     \<Rightarrow> Some (AnywherePat l kl [ItemFactor y'] z') | _ \<Rightarrow> None)
                   | Some (KSubs y') \<Rightarrow>
             (case simpleKToSU z database of Some (KItemSubs z')
                     \<Rightarrow> Some (AnywherePat l kl y' z') | _ \<Rightarrow> None)
                     | _ \<Rightarrow> None) | _ \<Rightarrow> None)
          else (case simpleKToIR x database of Some (KLabelFunPat l kl)
                   \<Rightarrow> (case simpleKToSU y database of Some (KLabelSubs y')
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> if Owise \<notin> set u
                     then Some (FunPat l [((KLabelFunPat l kl),(KLabelSubs y'),z')] None)
                     else Some (FunPat l [] (Some ((KLabelFunPat l kl),(KLabelSubs y'),z')))
                    | _ \<Rightarrow> None) | _ \<Rightarrow> None)
               | Some (KFunPat l kl)
                   \<Rightarrow> (case simpleKToSU y database of Some (KSubs y')
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> if Owise \<notin> set u
                     then Some (FunPat l [((KFunPat l kl),(KSubs y'),z')] None)
                     else Some (FunPat l [] (Some ((KFunPat l kl),(KSubs y'),z')))
                    | _ \<Rightarrow> None)
              | Some (KItemSubs y')
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> if Owise \<notin> set u
                     then Some (FunPat l [((KFunPat l kl),(KSubs [ItemFactor y']),z')] None)
                     else Some (FunPat l [] (Some ((KFunPat l kl),(KSubs [ItemFactor y']),z')))
                    | _ \<Rightarrow> None) | _ \<Rightarrow> None)
         | Some (KItemFunPat l kl)
                   \<Rightarrow> (case simpleKToSU y database of Some (KItemSubs y')
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> if Owise \<notin> set u
                     then Some (FunPat l [((KItemFunPat l kl),(KItemSubs y'),z')] None)
                     else Some (FunPat l [] (Some ((KItemFunPat l kl),(KItemSubs y'),z')))
                    | _ \<Rightarrow> None)
              | Some (KSubs [ItemFactor y'])
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> if Owise \<notin> set u
                     then Some (FunPat l [((KItemFunPat l kl),(KItemSubs y'),z')] None)
                     else Some (FunPat l [] (Some ((KItemFunPat l kl),(KItemSubs y'),z')))
                    | _ \<Rightarrow> None) | _ \<Rightarrow> None)
         | Some (ListFunPat l kl)
                   \<Rightarrow> (case simpleKToSU y database of Some (ListSubs y')
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> if Owise \<notin> set u
                     then Some (FunPat l [((ListFunPat l kl),(ListSubs y'),z')] None)
                     else Some (FunPat l [] (Some ((ListFunPat l kl),(ListSubs y'),z')))
                    | _ \<Rightarrow> None) | _ \<Rightarrow> None)
         | Some (SetFunPat l kl)
                   \<Rightarrow> (case simpleKToSU y database of Some (SetSubs y')
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> if Owise \<notin> set u
                     then Some (FunPat l [((SetFunPat l kl),(SetSubs y'),z')] None)
                     else Some (FunPat l [] (Some ((SetFunPat l kl),(SetSubs y'),z')))
                    | _ \<Rightarrow> None) | _ \<Rightarrow> None)
         | Some (MapFunPat l kl)
                   \<Rightarrow> (case simpleKToSU y database of Some (MapSubs y')
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> if Owise \<notin> set u
                     then Some (FunPat l [((MapFunPat l kl),(MapSubs y'),z')] None)
                     else Some (FunPat l [] (Some ((MapFunPat l kl),(MapSubs y'),z')))
                    | _ \<Rightarrow> None) | _ \<Rightarrow> None)
        | Some (NormalPat (KItemMatching x')) \<Rightarrow>
           (case simpleKToSU y database of Some (KItemSubs y')
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> Some (KRulePat (KPat [x'] None) [ItemFactor y'] z'
                                 (if Transition \<in> set u then True else False))
                    | _ \<Rightarrow> None)
              | Some (KSubs y')
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> Some (KRulePat (KPat [x'] None) y' z'
                                 (if Transition \<in> set u then True else False))
                    | _ \<Rightarrow> None) | _ \<Rightarrow> None)
        | Some (NormalPat (KMatching x')) \<Rightarrow>
           (case simpleKToSU y database of Some (KItemSubs y')
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> Some (KRulePat x' [ItemFactor y'] z'
                                 (if Transition \<in> set u then True else False))
                    | _ \<Rightarrow> None)
              | Some (KSubs y')
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> Some (KRulePat x' y' z' (if Transition \<in> set u then True else False))
                    | _ \<Rightarrow> None) | _ \<Rightarrow> None)
         | Some (NormalPat (BagMatching x'))
                   \<Rightarrow> (case simpleKToSU y database of Some (BagSubs y')
             \<Rightarrow> (case simpleKToSU z database of Some (KItemSubs z')
                \<Rightarrow> Some (BagRulePat x' y' z'
                                 (if Transition \<in> set u then True else False))
                    | _ \<Rightarrow> None) | _ \<Rightarrow> None)))"

fun mergeFunRules where
"mergeFunRules  l a b [] = Some [FunPat l a b]"
| "mergeFunRules  l a b (x#xl) =
 (case x of (FunPat l' a' b') \<Rightarrow> (if l = l' then 
        (case b of None \<Rightarrow> Some ((FunPat l (a'@a) b')#xl)
            | Some bo \<Rightarrow> (case b' of None \<Rightarrow> Some ((FunPat l (a'@a) (Some bo))#xl)
            | Some bo' \<Rightarrow> None)) else
         (case (mergeFunRules  l a b xl) of None \<Rightarrow> None
                | Some xl' \<Rightarrow> Some (x#xl')))
     | _ \<Rightarrow> (case (mergeFunRules  l a b xl) of None \<Rightarrow> None
                | Some xl' \<Rightarrow> Some (x#xl')))"


fun tupleToRulePats where
"tupleToRulePats [] database = Some []"
| "tupleToRulePats (x#xl) database = (case tupleToRulePat x database of None \<Rightarrow> None
             | Some (FunPat l a b) \<Rightarrow> (case tupleToRulePats xl database of None \<Rightarrow> None
                | Some xl' \<Rightarrow> mergeFunRules l a b xl')
             | Some x' \<Rightarrow> (case tupleToRulePats xl database of None \<Rightarrow> None
               | Some xl' \<Rightarrow> Some (x'#xl')))"

fun existKey where
"existKey x [] = False"
| "existKey x ((a,b)#xl) = (if x = a then True else existKey x xl)"

fun update where
"update x y [] = [(x,y)]"
| "update x y ((a,b)#xl) = (if a = x then (a,y)#xl else (a,b)#(update x y xl))"

fun lookup where
"lookup x [] = None"
| "lookup x ((a,b)#xl) = (if a = x then Some b else lookup x xl)"

fun collectSort and collectSorts where
"collectSort (SimId a b) acc = (if b = Top then Some acc else if existKey a acc then
              (case lookup a acc of None \<Rightarrow> None | Some b' \<Rightarrow> if b = b' then Some acc else None)
               else Some (update a b acc))"
| "collectSort (SimTerm a bl) acc = collectSorts bl acc"
| "collectSort (SimLabel a) acc = Some acc"
| "collectSort (SimEmpty a) acc = Some acc"
| "collectSort (SimBagCon a b) acc = (case collectSort a acc of None \<Rightarrow> None
            | Some acc' \<Rightarrow> collectSort b acc)"
| "collectSort (SimBag x y b) acc = collectSort b acc"
| "collectSorts [] acc = Some acc"
| "collectSorts (x#xl) acc = (case collectSort x acc of None \<Rightarrow> None
                | Some acc' \<Rightarrow>collectSorts xl acc')"

fun collectSortInRule where
"collectSortInRule (x,y,z,a) = (case collectSort x [] of None \<Rightarrow> None
          | Some acc \<Rightarrow> (case collectSort y acc of None \<Rightarrow> None
                | Some acc' \<Rightarrow> collectSort z acc'))"

fun assignSort and assignSorts where
"assignSort (SimId a b) acc = (if b = Top then (case lookup a acc of None \<Rightarrow> None
         | Some t \<Rightarrow> Some (SimId a t)) else Some (SimId a b))"
| "assignSort (SimTerm a bl) acc = (case assignSorts bl acc of None \<Rightarrow> None
            | Some bl' \<Rightarrow> Some (SimTerm a bl'))"
| "assignSort (SimLabel a) acc = Some (SimLabel a)"
| "assignSort (SimEmpty a) acc = Some (SimEmpty a)"
| "assignSort (SimBagCon a b) acc = (case assignSort a acc of None \<Rightarrow> None
           | Some a' \<Rightarrow> (case assignSort b acc of None \<Rightarrow> None
                | Some b' \<Rightarrow> Some (SimBagCon a' b')))"
| "assignSort (SimBag x y b) acc = (case assignSort b acc of None \<Rightarrow> None
             | Some b' \<Rightarrow> Some (SimBag x y b'))"
| "assignSorts [] acc = Some []"
| "assignSorts (x#xl) acc = (case assignSort x acc of None \<Rightarrow> None
           | Some x' \<Rightarrow> (case assignSorts xl acc of None \<Rightarrow> None
               | Some xl' \<Rightarrow> Some (x'#xl')))"

fun assignSortInRule  where
"assignSortInRule (x,y,z,a) = (case collectSortInRule (x,y,z,a) of None \<Rightarrow> None
        | Some acc \<Rightarrow> (case assignSort x acc of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case assignSort y acc of None \<Rightarrow> None
         | Some y' \<Rightarrow> (case assignSort z acc of None \<Rightarrow> None
           | Some z' \<Rightarrow> Some (x',y',z',a)))))"

fun assignSortInRules where
"assignSortInRules [] = Some []"
| "assignSortInRules (x#xl) = (case assignSortInRule x of None \<Rightarrow> None
        | Some x' \<Rightarrow> (case assignSortInRules xl of None \<Rightarrow> None
               | Some xl' \<Rightarrow> Some (x'#xl')))"

fun removeSubsorts where
"removeSubsorts [] = []"
| "removeSubsorts (x#xl) = (case x of Subsort a b \<Rightarrow> removeSubsorts xl | _ \<Rightarrow> x#(removeSubsorts xl))"

fun collectDatabase where
"collectDatabase (Parsed c a b) = syntaxSetToKItems (removeSubsorts (mergeTuples a))"

definition tupleToRuleInParsed where
"tupleToRuleInParsed a = (case a of Parsed c x y
                 \<Rightarrow> (case assignSortInRules y of None \<Rightarrow> None
          | Some y' \<Rightarrow> (case collectDatabase a of None \<Rightarrow> None
                | Some database \<Rightarrow> tupleToRulePats y' database)))"

function checkTermsInSUKLabel
    and checkTermsInSUKItem
    and checkTermsInSUKListAux
    and checkTermsInNoneSUKList
    and checkTermsInSUKList
    and checkTermsInSUK
    and checkTermsInSUList
    and checkTermsInSUSet
    and checkTermsInSUMap
    and checkTermsInSUBigKWithBag
    and checkTermsInSUBigKWithLabel
    and checkTermsInSUBag where 
  "checkTermsInSUKLabel (SUKLabel a) acc beta database subG = Some (acc,beta, SUKLabel a)"
| "checkTermsInSUKLabel (SUKLabelFun a b) acc beta database subG = (case getSUKLabelMeaning a of 
       None \<Rightarrow> (case checkTermsInSUKLabel a acc beta database subG of None \<Rightarrow> None
          | Some (acc',beta', a') \<Rightarrow>
        (case checkTermsInNoneSUKList b acc' beta' database subG of None \<Rightarrow> None
           | Some (acca,betaa, b') \<Rightarrow>
          (case getIdInSUKLabel a' of None \<Rightarrow> Some (acca,betaa,SUKLabelFun a' b')
        | Some x \<Rightarrow> (case updateMap x [KLabel] betaa subG of None \<Rightarrow> None
          | Some betab \<Rightarrow> Some (acca,betab, SUKLabelFun a' b')))))
    | Some s \<Rightarrow> (if isFunctionItem s database then 
     (case getArgSort s database of None \<Rightarrow> None
      | Some l \<Rightarrow> (case getSort s database of None \<Rightarrow> None
             | Some ty \<Rightarrow> if subsortList ty [KLabel] subG then
           (case checkTermsInSUKList b l acc beta database subG of None \<Rightarrow> None
           | Some (acc',beta', b') \<Rightarrow> Some (acc', beta', SUKLabelFun a b')) else None)) else None))"
| "checkTermsInSUKLabel (SUIdKLabel n) acc beta database subG =
   (case updateMap n [KLabel] acc subG of None \<Rightarrow> None
      | Some acc' \<Rightarrow> Some (acc', beta, SUIdKLabel n))"
| "checkTermsInSUKItem (SUKItem l r ty) maxTy acc beta database subG = 
   (if subsortList maxTy [K] subG \<and> subsortList ty [K] subG then
      (case getSUKLabelMeaning l of None \<Rightarrow> 
         (case checkTermsInSUKLabel l acc beta database subG of None \<Rightarrow> None
             | Some (acc', beta', l') \<Rightarrow>
           (case checkTermsInNoneSUKList r acc' beta' database subG of None \<Rightarrow> None
             | Some (acca, betaa, r') \<Rightarrow>
        (case meet ty maxTy subG of [] \<Rightarrow> None
            | (tya#tyl) \<Rightarrow> (case getIdInSUKLabel l' of None \<Rightarrow> 
                 Some (acca,betaa, SUKItem l' r' (tya#tyl))
          | Some newId \<Rightarrow>
          (case updateBeta newId (tya#tyl) acca subG of None \<Rightarrow> None
          | Some betab \<Rightarrow> Some (acca,betab, SUKItem l' r' (tya#tyl)))))))
         | Some s \<Rightarrow> (case getSort s database of None \<Rightarrow> None
           | Some theTy \<Rightarrow>
        (case getArgSort s database of None \<Rightarrow> None | Some tyl \<Rightarrow>
         (case checkTermsInSUKList r tyl acc beta database subG of None \<Rightarrow> None
          | Some (acc', beta', r') \<Rightarrow>
      (if isFunctionItem s database then
       (case meet theTy (meet ty maxTy subG) subG of [] \<Rightarrow> None
          | tya \<Rightarrow> Some (acc',beta', SUKItem l r' tya))
       else if subsortList theTy ty subG \<and> subsortList theTy maxTy subG then
            Some (acc',beta', SUKItem l r' theTy) else None))))) else None)"
| "checkTermsInSUKItem (SUIdKItem a b) maxTy acc beta database subG =
    (case meet b maxTy subG of [] \<Rightarrow> None
        | ty' \<Rightarrow> (case updateMap a ty' acc subG of None \<Rightarrow> None
         | Some acc' \<Rightarrow> Some (acc',beta, SUIdKItem a ty')))"
| "checkTermsInSUKItem (SUHOLE a) maxTy acc beta database subG =
    (case meet a maxTy subG of [] \<Rightarrow> None
      | ty' \<Rightarrow> Some (acc,beta,  SUHOLE ty'))"
| "checkTermsInNoneSUKList [] acc beta database subG = Some (acc, beta, [])"
| "checkTermsInNoneSUKList (x#l) acc beta database subG = (case x of IdKl a
      \<Rightarrow> (case updateMap a [KList] acc subG of None \<Rightarrow> None
           | Some acc' \<Rightarrow> (case checkTermsInNoneSUKList l acc' beta database subG of None \<Rightarrow> None
         | Some (acca, betaa, l') \<Rightarrow> Some (acca, betaa, (IdKl a)#l')))
    | ItemKl a \<Rightarrow> (case checkTermsInSUBigKWithLabel a None acc beta database subG of None \<Rightarrow> None
      | Some (acc', beta', a') \<Rightarrow> (case checkTermsInNoneSUKList l acc beta database subG
          of None \<Rightarrow> None | Some (acca, betaa, l') \<Rightarrow> Some (acca, betaa, (ItemKl a')#l'))))"
| "checkTermsInSUKListAux [] tyl acc beta database subG = Some (acc,beta, [], [])"
| "checkTermsInSUKListAux (b#l) tyl acc beta database subG =
     (case b of IdKl x \<Rightarrow>
      (case updateMap x [KList] acc subG of None \<Rightarrow> None
         | Some acc' \<Rightarrow> Some (acc',beta, [] , b#l))
    | ItemKl x \<Rightarrow> (case tyl of [] \<Rightarrow> None
         | (ty#tyl') \<Rightarrow>
      (case checkTermsInSUBigKWithLabel x (Some ty) acc beta database subG of None \<Rightarrow> None
         | Some (acc',beta', x') \<Rightarrow>
        (case checkTermsInSUKListAux l tyl' acc' beta' database subG of None \<Rightarrow> None
          | Some (acca, betaa, l', la) \<Rightarrow> Some (acca, betaa, ((ItemKl x')#l', la))))))"
| "checkTermsInSUKList l tyl acc beta database subG =
     (if numberOfItemsInKList l > length tyl then None
         else (if hasIdInKList l then
       (case checkTermsInSUKListAux l tyl acc beta database subG of None \<Rightarrow> None
           | Some (acc', beta', la, lb) \<Rightarrow> 
         (case checkTermsInSUKListAux (rev lb) (rev tyl) acc' beta' database subG of None \<Rightarrow> None
             | Some (acca, betaa, la', lb') \<Rightarrow>
      (if lb' = [] then Some (acca, betaa, la@(rev la'))
         else (case checkTermsInNoneSUKList (rev lb') acca betaa database subG of None \<Rightarrow> None
             | Some (accb, betab, lbb) \<Rightarrow> Some (accb, betab, la@lbb@(rev la'))))))
       else if numberOfItemsInKList l = length tyl
            then (case checkTermsInSUKListAux l tyl acc beta database subG
         of Some (acca,betaa, la, []) 
                 \<Rightarrow> Some (acca,betaa, la) | _ \<Rightarrow> None) else None))"
| "checkTermsInSUBigKWithLabel (SUBigBag a) ty acc beta database subG =
     (case checkTermsInSUBigKWithBag a ty acc beta database subG of None \<Rightarrow> None
         | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUBigBag a'))"
| "checkTermsInSUBigKWithLabel (SUBigLabel a) ty acc beta database subG = (case ty of None \<Rightarrow> 
   (case checkTermsInSUKLabel a acc beta database subG of None \<Rightarrow> None
         | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUBigLabel a'))
    | Some ty' \<Rightarrow> if ty' = [KLabel] then
        (case checkTermsInSUKLabel a acc beta database subG of None \<Rightarrow> None
         | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUBigLabel a')) else None)"
| "checkTermsInSUBigKWithBag (SUK a) ty acc beta database subG = (case ty of None
    \<Rightarrow> (case checkTermsInSUK a [K] acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUK a'))
              | Some ty' \<Rightarrow> (if subsortList ty' [K] subG then 
          (case checkTermsInSUK a [K] acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUK a')) else None))"
| "checkTermsInSUBigKWithBag (SUList a) ty acc beta database subG = (case ty of None
    \<Rightarrow> (case checkTermsInSUList a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUList a'))
              | Some ty' \<Rightarrow> (if ty' = [List] then 
          (case checkTermsInSUList a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUList a')) else None))"
| "checkTermsInSUBigKWithBag (SUSet a) ty acc beta database subG = (case ty of None
    \<Rightarrow> (case checkTermsInSUSet a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUSet a'))
              | Some ty' \<Rightarrow> (if ty' = [Set] then 
          (case checkTermsInSUSet a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUSet a')) else None))"
| "checkTermsInSUBigKWithBag (SUMap a) ty acc beta database subG = (case ty of None
    \<Rightarrow> (case checkTermsInSUMap a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUMap a'))
              | Some ty' \<Rightarrow> (if ty' = [Map] then 
          (case checkTermsInSUMap a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUMap a')) else None))"
| "checkTermsInSUBigKWithBag (SUBag a) ty acc beta database subG = (case ty of None
    \<Rightarrow> (case checkTermsInSUBag a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUBag a'))
              | Some ty' \<Rightarrow> (if ty' = [Bag] then 
          (case checkTermsInSUBag a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUBag a')) else None))"
| "checkTermsInSUK l ty acc beta database subG = (if ty = [K] then 
       (case l of [] \<Rightarrow> Some (acc,beta,[])
          | ((ItemFactor x)#xl) \<Rightarrow>
              (case checkTermsInSUKItem x [K] acc beta database subG of None \<Rightarrow> None
                | Some (acc',beta',x') \<Rightarrow>
        (case checkTermsInSUK xl ty acc' beta' database subG of None \<Rightarrow> None
           | Some (acca,betaa, xl') \<Rightarrow> Some (acca,betaa, (ItemFactor x')#xl')))
         | ((IdFactor x)#xl) \<Rightarrow>
         (case updateMap x [K] acc subG of None \<Rightarrow> None
          | Some acc' \<Rightarrow> (case checkTermsInSUK xl ty acc' beta database subG of
   None \<Rightarrow> None | Some (acca,betaa, xl') \<Rightarrow> Some (acca,betaa, (IdFactor x)#xl')))
         | ((SUKKItem a b ty')#xl) \<Rightarrow>
         (if subsortList ty' [K] subG then
            (case getSUKLabelMeaning a of None \<Rightarrow>
               (case checkTermsInSUKLabel a acc beta database subG of None \<Rightarrow> None
                  | Some (acc',beta', a') \<Rightarrow>
                (case checkTermsInNoneSUKList b acc' beta' database subG of None \<Rightarrow> None
                   | Some (acca,betaa, b') \<Rightarrow>
                  (case checkTermsInSUK xl ty acca betaa database subG of None \<Rightarrow> None
                     | Some (accb,betab, xl') \<Rightarrow> Some (accb,betab,(SUKKItem a' b' ty')#xl'))))
             | Some s \<Rightarrow> if isFunctionItem s database then
         (case (getSort s database, getArgSort s database) of (Some tya, Some tyl)
      \<Rightarrow> (case meet ty' tya subG of [] \<Rightarrow> None
             |  tyb \<Rightarrow>
               (case checkTermsInSUKList b tyl acc beta database subG of None \<Rightarrow> None
                | Some (acc',beta', b') \<Rightarrow>
               (case checkTermsInSUK xl ty acc' beta' database subG of None \<Rightarrow> None
                  | Some (acca,betaa, xl') \<Rightarrow> Some (acca,betaa, (SUKKItem a b' tyb)#xl'))))
              | _ \<Rightarrow> None) else None) else None))
           else if subsortList ty [KItem] subG then
          (case l of [u] \<Rightarrow> (case u of (IdFactor a) \<Rightarrow>
            (case updateMap a ty acc subG of None \<Rightarrow> None
               | Some acc' \<Rightarrow> Some (acc',beta, [ItemFactor (SUIdKItem a ty)]))
             | ItemFactor a \<Rightarrow> (case checkTermsInSUKItem a ty acc beta database subG
              of None \<Rightarrow> None
               | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', [ItemFactor a']))
             | SUKKItem a b ty' \<Rightarrow> if subsortList ty' [K] subG then
                 (case getSUKLabelMeaning a of None \<Rightarrow>
                (case checkTermsInSUKLabel a acc beta database subG of None \<Rightarrow> None
                  | Some (acc',beta', a') \<Rightarrow>
                  (case checkTermsInNoneSUKList b acc' beta' database subG of None \<Rightarrow> None
                    | Some (acca,betaa, b') \<Rightarrow>
                (case meet ty ty' subG of [] \<Rightarrow> None | tya \<Rightarrow>
                  Some (acca,betaa,[SUKKItem a' b' tya]))))
                  | Some s \<Rightarrow> if isFunctionItem s database
                 then (case (getSort s database, getArgSort s database)
                     of (Some theTy, Some tyl) \<Rightarrow>
       (case checkTermsInSUKList b tyl acc beta database subG of None \<Rightarrow> None
           | Some (acc',beta', b') \<Rightarrow>
    (case meet ty (meet ty' theTy subG) subG of [] \<Rightarrow> None
         | tya \<Rightarrow> Some (acc', beta', [SUKKItem a b' tya])))) else None)
           else None)) else None)"
| "checkTermsInSUList [] acc beta database subG = Some (acc,beta,[])"
| "checkTermsInSUList (b#l) acc beta database subG = (case b of ItemL x \<Rightarrow>
             (case checkTermsInSUK x [K] acc beta database subG of None \<Rightarrow> None
                | Some (acc',beta', x') \<Rightarrow>
         (case checkTermsInSUList l acc' beta' database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (ItemL x')#l')))
         | IdL x \<Rightarrow> (case updateMap x [List] acc subG of None \<Rightarrow> None
            | Some acc' \<Rightarrow> (case checkTermsInSUList l acc' beta database subG of
            None \<Rightarrow> None | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (IdL x)#l')))
        | SUListKItem x y \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> 
           (case checkTermsInSUKLabel x acc beta database subG of None \<Rightarrow> None
             | Some (acc',beta', x') \<Rightarrow>
              (case checkTermsInNoneSUKList y acc' beta' database subG of None \<Rightarrow> None
                 | Some (acca, betaa, y') \<Rightarrow>
               (case checkTermsInSUList l acca betaa database subG of None \<Rightarrow> None
            | Some (accb,betab, l') \<Rightarrow> (case getIdInSUKLabel x' of None \<Rightarrow> 
                   Some (accb,betab,(SUListKItem x' y')#l')
          | Some xx \<Rightarrow> (case updateMap xx [List] betab subG of None \<Rightarrow> None
            | Some betac \<Rightarrow> Some (accb,betac, (SUListKItem x' y')#l'))))))
           | Some s \<Rightarrow> if isFunctionItem s database
            then (case (getSort s database, getArgSort s database) of
             (Some ty, Some tyl) \<Rightarrow> if ty = [List] then 
                 (case checkTermsInSUKList y tyl acc beta database subG of None \<Rightarrow> None
                 | Some (acc',beta', y') \<Rightarrow>
               (case checkTermsInSUList l acc' beta' database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (SUListKItem x y')#l')))
              else None | _ \<Rightarrow> None) else None))"
| "checkTermsInSUSet [] acc beta database subG = Some (acc,beta, [])"
| "checkTermsInSUSet (b#l) acc beta database subG = (case b of ItemS x \<Rightarrow>
             (case checkTermsInSUK x [K] acc beta database subG of None \<Rightarrow> None
                | Some (acc',beta', x') \<Rightarrow>
         (case checkTermsInSUSet l acc' beta' database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (ItemS x')#l')))
         | IdS x \<Rightarrow> (case updateMap x [Set] acc subG of None \<Rightarrow> None
            | Some acc' \<Rightarrow> (case checkTermsInSUSet l acc' beta database subG of None \<Rightarrow> None
            | Some (acca, betaa, l') \<Rightarrow> Some (acca,betaa, (IdS x)#l')))
        | SUSetKItem x y \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> 
           (case checkTermsInSUKLabel x acc beta database subG of None \<Rightarrow> None
             | Some (acc',beta', x') \<Rightarrow>
              (case checkTermsInNoneSUKList y acc' beta' database subG of None \<Rightarrow> None
                 | Some (acca,betaa, y') \<Rightarrow>
               (case checkTermsInSUSet l acca betaa database subG of None \<Rightarrow> None
            | Some (accb, betab, l') \<Rightarrow> (case getIdInSUKLabel x' of None 
               \<Rightarrow> Some (accb,betab,(SUSetKItem x' y')#l') | Some xx \<Rightarrow>
          (case updateMap xx [Set] betab subG of None \<Rightarrow> None
            | Some betac \<Rightarrow> Some (accb,betac,(SUSetKItem x' y')#l'))))))
           | Some s \<Rightarrow> if isFunctionItem s database then
            (case (getSort s database, getArgSort s database) of
             (Some ty, Some tyl) \<Rightarrow> if subsortList ty [Set] subG then 
                 (case checkTermsInSUKList y tyl acc beta database subG of None \<Rightarrow> None
                 | Some (acc',beta', y') \<Rightarrow>
               (case checkTermsInSUSet l acc' beta' database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (SUSetKItem x y')#l')))
              else None | _ \<Rightarrow> None) else None))"
| "checkTermsInSUMap [] acc beta database subG = Some (acc,beta, [])"
| "checkTermsInSUMap (b#l) acc beta database subG = (case b of ItemM x y \<Rightarrow>
             (case checkTermsInSUK x [K] acc beta database subG of None \<Rightarrow> None
                | Some (acc',beta', x') \<Rightarrow>
               (case checkTermsInSUK y [K] acc' beta' database subG of None \<Rightarrow> None
                   | Some (acca,betaa, y') \<Rightarrow>
         (case checkTermsInSUMap l acca betaa database subG of None \<Rightarrow> None
            | Some (accb,betab, l') \<Rightarrow> Some (accb, betab, (ItemM x' y')#l'))))
         | IdM x \<Rightarrow> (case updateMap x [Map] acc subG of None \<Rightarrow> None
            | Some acc' \<Rightarrow> (case checkTermsInSUMap l acc' beta database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca, betaa, (IdM x)#l')))
        | SUMapKItem x y \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> 
           (case checkTermsInSUKLabel x acc beta database subG of None \<Rightarrow> None
             | Some (acc',beta', x') \<Rightarrow>
              (case checkTermsInNoneSUKList y acc' beta' database subG of None \<Rightarrow> None
                 | Some (acca,betaa, y') \<Rightarrow>
               (case checkTermsInSUMap l acca betaa database subG of None \<Rightarrow> None
            | Some (accb, betab, l') \<Rightarrow> (case getIdInSUKLabel x' of None \<Rightarrow>
                   Some (accb, betab, (SUMapKItem x' y')#l')
            | Some xx \<Rightarrow> (case updateMap xx [Map] betab subG of None \<Rightarrow> None
            | Some betac \<Rightarrow> Some (accb, betac, (SUMapKItem x' y')#l'))))))
           | Some s \<Rightarrow> if isFunctionItem s database then
          (case (getSort s database, getArgSort s database) of
             (Some ty, Some tyl) \<Rightarrow> if subsortList ty [Map] subG then 
                 (case checkTermsInSUKList y tyl acc beta database subG of None \<Rightarrow> None
                 | Some (acc', beta', y') \<Rightarrow>
               (case checkTermsInSUMap l acc' beta' database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (SUMapKItem x y')#l')))
              else None | _ \<Rightarrow> None) else None))"
| "checkTermsInSUBag [] acc beta database subG = Some (acc,beta, [])"
| "checkTermsInSUBag (b#l) acc beta database subG = (case b of ItemB x y z \<Rightarrow>
             (case checkTermsInSUBigKWithBag z None acc beta database subG of None \<Rightarrow> None
                | Some (acc',beta', z') \<Rightarrow>
         (case checkTermsInSUBag l acc' beta' database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (ItemB x y z')#l')))
         | IdB x \<Rightarrow> (case updateMap x [Bag] acc subG of None \<Rightarrow> None
   | Some acc' \<Rightarrow> (case checkTermsInSUBag l acc' beta database subG of None \<Rightarrow> None
   | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (IdB x)#l'))))"
by pat_completeness auto

termination sorry

(* merge duplicate copys of set and map 
     and if there is a map being non-functional, return none *)
(* check the syntatic congruence of two ir terms *)
function syntacticMonoidInSUKLabel
    and syntacticMonoidInSUKItem
    and syntacticMonoidInSUKList
    and syntacticMonoidInSUK
    and syntacticMonoidInSUList
    and syntacticMonoidInSUSet
    and syntacticMonoidInSUMap
    and syntacticMonoidInSUBigKWithBag
    and syntacticMonoidInSUBigKWithLabel
    and syntacticMonoidInSUBag
    and syntacticMonoidInSUSubSet
    and syntacticMonoidInSUMember
    and syntacticMonoidInSUSubMap
    and syntacticMonoidInSUMapMember
    and syntacticMonoidInSUBagMember where
 "syntacticMonoidInSUKLabel (SUKLabel a) S subG =
   (case S of (SUKLabel a') \<Rightarrow>
      (if a = a' then Some (SUKLabel a) else None)
       | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKLabel (SUIdKLabel a) B subG = (case B of SUIdKLabel a' \<Rightarrow>
                                  if a = a' then Some (SUIdKLabel a)
                                  else None | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKLabel (SUKLabelFun a b) B subG = (case B of SUKLabelFun a' b' \<Rightarrow>
     (case syntacticMonoidInSUKLabel a a' subG of None \<Rightarrow> None
    | Some a1 \<Rightarrow> (case syntacticMonoidInSUKList b b' subG of None \<Rightarrow> None
                 | Some ba \<Rightarrow> Some (SUKLabelFun a1 ba))) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKItem (SUKItem l r ty) S subG = (case S of (SUKItem l' r' ty') \<Rightarrow>
  (case (syntacticMonoidInSUKLabel l l' subG, syntacticMonoidInSUKList r r' subG) of (Some la, Some ra)
       \<Rightarrow> (case meet ty ty' subG of [] \<Rightarrow> None
       | (x#xl) \<Rightarrow> Some (SUKItem la ra (x#xl)))
    | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKItem (SUHOLE a) S subG = (case S of (SUHOLE a') \<Rightarrow>
     (case meet a a' subG of [] \<Rightarrow> None | (x#xl) \<Rightarrow>
               Some (SUHOLE (x#xl))) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKItem (SUIdKItem a b) B subG = (case B of SUIdKItem a' b' \<Rightarrow>
         if (a = a') then (case meet b b' subG of [] \<Rightarrow> None
         | (x#xl) \<Rightarrow> Some (SUIdKItem a (x#xl))) else None | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKList [] S subG = (case S of [] \<Rightarrow> Some [] | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKList (b#l) S subG = (case S of [] \<Rightarrow> None
         | (b'#l') \<Rightarrow> (case (b,b') of (ItemKl bs, ItemKl bs') \<Rightarrow>
         (case syntacticMonoidInSUBigKWithLabel bs bs' subG of None \<Rightarrow> None
       | Some bsa \<Rightarrow> (case syntacticMonoidInSUKList l l' subG of None \<Rightarrow> None
       | Some la \<Rightarrow> Some ((ItemKl bsa)#la)))
         | (IdKl x, IdKl x') \<Rightarrow>  if x = x' then
       (case syntacticMonoidInSUKList l l' subG of None \<Rightarrow> None
           | Some la \<Rightarrow> Some ((IdKl x)#la)) else None | _ \<Rightarrow> None))"
| "syntacticMonoidInSUBigKWithLabel (SUBigBag a) b subG =
   (case b of (SUBigBag a') \<Rightarrow>
   (case syntacticMonoidInSUBigKWithBag a a' subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUBigBag aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBigKWithLabel (SUBigLabel a) b subG =
   (case b of (SUBigLabel a') \<Rightarrow>
   (case syntacticMonoidInSUKLabel a a' subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUBigLabel aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBigKWithBag (SUK a) b subG =
   (case b of (SUK a') \<Rightarrow>
   (case syntacticMonoidInSUK a a' subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUK aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBigKWithBag (SUList a) b subG =
   (case b of (SUList a') \<Rightarrow>
   (case syntacticMonoidInSUList a a' subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUList aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBigKWithBag (SUSet a) b subG =
   (case b of (SUSet a') \<Rightarrow>
   (case syntacticMonoidInSUSet a a' a subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUSet aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBigKWithBag (SUMap a) b subG =
   (case b of (SUMap a') \<Rightarrow>
   (case syntacticMonoidInSUMap a a' a subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUMap aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBigKWithBag (SUBag a) b subG =
   (case b of (SUBag a') \<Rightarrow>
   (case syntacticMonoidInSUBag a a' subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUBag aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUK [] S subG = (case S of [] \<Rightarrow> Some [] | _ \<Rightarrow> None)"
| "syntacticMonoidInSUK (b#l) S subG = (case S of (b'#l') \<Rightarrow>
       (case (b,b') of (ItemFactor x, ItemFactor x') \<Rightarrow>
          (case (syntacticMonoidInSUKItem x x' subG, syntacticMonoidInSUK l l' subG)
           of (Some xa, Some la) \<Rightarrow> Some ((ItemFactor xa)#la) | _ \<Rightarrow> None)
          | (IdFactor x, IdFactor x') \<Rightarrow> if x = x' then
            (case (syntacticMonoidInSUK l l' subG) of None \<Rightarrow> None
               | Some la \<Rightarrow> Some ((IdFactor x)#la)) else None
          | (IdFactor x, ItemFactor (SUIdKItem x' ty)) \<Rightarrow> 
             if x = x' then (case syntacticMonoidInSUK l l' subG of None \<Rightarrow> None
                 | Some la \<Rightarrow> Some ((ItemFactor (SUIdKItem x' ty))#la)) else None
          | (ItemFactor (SUIdKItem x ty), IdFactor x') \<Rightarrow> if x = x' then
              (case syntacticMonoidInSUK l l' subG of None \<Rightarrow> None
                 | Some la \<Rightarrow> Some ((ItemFactor (SUIdKItem x ty))#la)) else None
   | (SUKKItem x y ty, SUKKItem x' y' ty')
      \<Rightarrow> (case (syntacticMonoidInSUKLabel x x' subG,
       syntacticMonoidInSUKList y y' subG, syntacticMonoidInSUK l l' subG) of 
       (Some xa, Some ya, Some la) \<Rightarrow> (case meet ty ty' subG of [] \<Rightarrow> None
          | (newTy#newTyl) \<Rightarrow> Some ((SUKKItem xa ya (newTy#newTyl))#la))
        | _ \<Rightarrow> None) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUList [] S subG = (case S of [] \<Rightarrow> Some [] | _ \<Rightarrow> None)"
| "syntacticMonoidInSUList (b#l) S subG = (case S of (b'#l') \<Rightarrow>
       (case (b,b') of (ItemL x, ItemL x') \<Rightarrow>
     (case (syntacticMonoidInSUK x x' subG, syntacticMonoidInSUList l l' subG)
       of (Some xa, Some la) \<Rightarrow> Some ((ItemL xa)#la) | _ \<Rightarrow> None)
      | (IdL x, IdL x') \<Rightarrow> if x = x' then
     (case syntacticMonoidInSUList l l' subG of None \<Rightarrow> None
        | Some la \<Rightarrow> Some ((IdL x)#la)) else None
      | (SUListKItem x y, SUListKItem x' y') \<Rightarrow>
     (case (syntacticMonoidInSUKLabel x x' subG, syntacticMonoidInSUKList y y' subG,
       syntacticMonoidInSUList l l' subG) of (Some xa, Some ya, Some la) \<Rightarrow>
           Some ((SUListKItem xa ya)#la) | _ \<Rightarrow> None)
        | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUMember b [] subG = None"
| "syntacticMonoidInSUMember b (b'#l) subG = (case (b,b')
   of (ItemS x, ItemS x') \<Rightarrow>
   (case syntacticMonoidInSUK x' x subG of None \<Rightarrow> syntacticMonoidInSUMember b l subG
      | Some xa \<Rightarrow> Some (ItemS xa))
    | (IdS x, IdS x') \<Rightarrow> if x = x' then Some (IdS x) else syntacticMonoidInSUMember b l subG
    | (SUSetKItem x y, SUSetKItem x' y') \<Rightarrow>
     (case (syntacticMonoidInSUKLabel x' x subG, syntacticMonoidInSUKList y' y subG)
      of (Some xa, Some ya) \<Rightarrow> Some (SUSetKItem xa ya)
        | _ \<Rightarrow> syntacticMonoidInSUMember b l subG) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUSubSet [] T subG = Some []"
| "syntacticMonoidInSUSubSet (b#l) T subG =
      (case syntacticMonoidInSUMember b T subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case syntacticMonoidInSUSubSet l T subG of None \<Rightarrow> None
      | Some l' \<Rightarrow> Some (b'#l')))"
| "syntacticMonoidInSUSet [] S T subG = syntacticMonoidInSUSubSet S T subG"
| "syntacticMonoidInSUSet (b#l) S T subG =
    (case syntacticMonoidInSUMember b S subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> syntacticMonoidInSUSet l S T subG)"
| "syntacticMonoidInSUMapMember b [] subG = None"
| "syntacticMonoidInSUMapMember b (b'#l) subG = (case (b,b')
   of (ItemM x y, ItemM x' y') \<Rightarrow>
   (case syntacticMonoidInSUK x' x subG of None \<Rightarrow> syntacticMonoidInSUMapMember b l subG
      | Some xa \<Rightarrow> (case syntacticMonoidInSUK y' y subG of None \<Rightarrow> None
       | Some ya \<Rightarrow> Some (ItemM xa ya)))
    | (IdM x, IdM x') \<Rightarrow> if x = x' then Some (IdM x)
                 else syntacticMonoidInSUMapMember b l subG
    | (SUMapKItem x y, SUMapKItem x' y') \<Rightarrow>
     (case (syntacticMonoidInSUKLabel x' x subG, syntacticMonoidInSUKList y' y subG)
      of (Some xa, Some ya) \<Rightarrow> Some (SUMapKItem xa ya)
        | _ \<Rightarrow> syntacticMonoidInSUMapMember b l subG) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUSubMap [] T subG = Some []"
| "syntacticMonoidInSUSubMap (b#l) T subG =
      (case syntacticMonoidInSUMapMember b T subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case syntacticMonoidInSUSubMap l T subG of None \<Rightarrow> None
      | Some l' \<Rightarrow> Some (b'#l')))"
| "syntacticMonoidInSUMap [] S T subG = syntacticMonoidInSUSubMap S T subG"
| "syntacticMonoidInSUMap (b#l) S T subG =
    (case syntacticMonoidInSUMapMember b S subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> syntacticMonoidInSUMap l S T subG)"
| "syntacticMonoidInSUBagMember b [] subG = None"
| "syntacticMonoidInSUBagMember b (b'#l) subG = (case (b,b') of
       (ItemB x y z,ItemB x' y' z') \<Rightarrow>
     (if x = x' then (case syntacticMonoidInSUBigKWithBag z' z subG of None \<Rightarrow> None
        | Some za \<Rightarrow> Some (ItemB x y za, l)) else
     (case syntacticMonoidInSUBagMember b l subG of None \<Rightarrow> None
       | Some (ba,la) \<Rightarrow> Some (ba,b'#la)))
     | (IdB x, IdB x') \<Rightarrow> if x = x' then Some (IdB x, l)
          else (case syntacticMonoidInSUBagMember b l subG of None \<Rightarrow> None
           | Some (ba, la) \<Rightarrow> Some (ba, (IdB x')#la))
     | _ \<Rightarrow> (case syntacticMonoidInSUBagMember b l subG of None \<Rightarrow> None
         | Some (ba,la) \<Rightarrow> Some (ba, b'#la)))"
| "syntacticMonoidInSUBag [] S subG = (case S of [] \<Rightarrow> Some [] | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBag (b#l) S subG =
    (case syntacticMonoidInSUBagMember b S subG of None \<Rightarrow> None
       | Some (ba, S') \<Rightarrow> (case syntacticMonoidInSUBag l S' subG of None \<Rightarrow> None
           | Some la \<Rightarrow> Some (ba#la)))"
by pat_completeness auto

termination sorry

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

primrec regularizeInSUKLabel
    and regularizeInSUKItem
    and regularizeInSUKListElem
    and regularizeInSUKList
    and regularizeInSUKElem
    and regularizeInSUK
    and regularizeInSUListElem
    and regularizeInSUList
    and regularizeInSUSetElem
    and regularizeInSUSet
    and regularizeInSUMapElem
    and regularizeInSUMap
    and regularizeInSUBigKWithBag
    and regularizeInSUBigKWithLabel
    and regularizeInSUBagElem
    and regularizeInSUBag where
 "regularizeInSUKLabel (SUKLabel a) subG = Some (SUKLabel a)"
| "regularizeInSUKLabel (SUIdKLabel a) subG = Some (SUIdKLabel a)"
| "regularizeInSUKLabel (SUKLabelFun a b) subG =
   (case (regularizeInSUKLabel a subG) of None \<Rightarrow> None
       | Some a' \<Rightarrow> (case (regularizeInSUKList b subG) of None \<Rightarrow> None
          | Some b' \<Rightarrow> Some (SUKLabelFun a' b')))"
| "regularizeInSUKItem (SUKItem l r ty) subG=
   (case (regularizeInSUKLabel l subG) of None \<Rightarrow> None
       | Some a' \<Rightarrow> (case (regularizeInSUKList r subG) of None \<Rightarrow> None
          | Some b' \<Rightarrow> Some (SUKItem a' b' ty)))"
| "regularizeInSUKItem (SUHOLE a) subG = Some (SUHOLE a)"
| "regularizeInSUKItem (SUIdKItem a b) subG = Some (SUIdKItem a b)"
| "regularizeInSUKListElem (IdKl x) subG = Some (IdKl x)"
| "regularizeInSUKListElem (ItemKl x) subG = (case (regularizeInSUBigKWithLabel x subG)
    of None \<Rightarrow> None | Some x' \<Rightarrow> Some (ItemKl x'))"
| "regularizeInSUKList [] subG = Some []"
| "regularizeInSUKList (b#l) subG =
   (case regularizeInSUKListElem b subG of None \<Rightarrow> None
     | Some b' \<Rightarrow> (case regularizeInSUKList l subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some (b'#l')))"
| "regularizeInSUBigKWithLabel (SUBigBag a) subG =
    (case regularizeInSUBigKWithBag a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "regularizeInSUBigKWithLabel (SUBigLabel a) subG =
    (case regularizeInSUKLabel a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBigLabel a'))"
| "regularizeInSUBigKWithBag (SUK a) subG =
    (case regularizeInSUK a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUK a'))"
| "regularizeInSUBigKWithBag (SUList a) subG =
    (case regularizeInSUList a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUList a'))"
| "regularizeInSUBigKWithBag (SUSet a) subG =
    (case regularizeInSUSet a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUSet a'))"
| "regularizeInSUBigKWithBag (SUMap a) subG =
    (case regularizeInSUMap a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUMap a'))"
| "regularizeInSUBigKWithBag (SUBag a) subG =
    (case regularizeInSUBag a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBag a'))"
| "regularizeInSUKElem (IdFactor x) subG = Some (IdFactor x)"
| "regularizeInSUKElem (ItemFactor x) subG = (case (regularizeInSUKItem x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow> Some (ItemFactor x'))"
| "regularizeInSUKElem (SUKKItem x y z) subG = (case (regularizeInSUKLabel x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow>
    (case regularizeInSUKList y subG of None \<Rightarrow> None
       | Some y' \<Rightarrow> Some (SUKKItem x' y' z)))"
| "regularizeInSUK [] subG = Some []"
| "regularizeInSUK (b#l) subG =
   (case regularizeInSUKElem b subG of None \<Rightarrow> None
     | Some b' \<Rightarrow> (case regularizeInSUK l subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some (b'#l')))"
| "regularizeInSUListElem (IdL x) subG = Some (IdL x)"
| "regularizeInSUListElem (ItemL x) subG = (case (regularizeInSUK x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow> Some (ItemL x'))"
| "regularizeInSUListElem (SUListKItem x y) subG = (case (regularizeInSUKLabel x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow>
    (case regularizeInSUKList y subG of None \<Rightarrow> None
       | Some y' \<Rightarrow> Some (SUListKItem x' y')))"
| "regularizeInSUList [] subG = Some []"
| "regularizeInSUList (b#l) subG =
   (case regularizeInSUListElem b subG of None \<Rightarrow> None
     | Some b' \<Rightarrow> (case regularizeInSUList l subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some (b'#l')))"
| "regularizeInSUSetElem (IdS x) subG = Some (IdS x)"
| "regularizeInSUSetElem (ItemS x) subG = (case (regularizeInSUK x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow> Some (ItemS x'))"
| "regularizeInSUSetElem (SUSetKItem x y) subG = (case (regularizeInSUKLabel x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow>
    (case regularizeInSUKList y subG of None \<Rightarrow> None
       | Some y' \<Rightarrow> Some (SUSetKItem x' y')))"
| "regularizeInSUSet [] subG = Some []"
| "regularizeInSUSet (b#l) subG =
   (case regularizeInSUSetElem b subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case regularizeInSUSet l subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> (if isCommonElemInSUSet b' l' subG
            then Some l' else Some (b'#l'))))"
| "regularizeInSUMapElem (IdM x) subG = Some (IdM x)"
| "regularizeInSUMapElem (ItemM x y) subG = (case (regularizeInSUK x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow> (case regularizeInSUK y subG of None \<Rightarrow> None
          | Some y' \<Rightarrow>  Some (ItemM x' y')))"
| "regularizeInSUMapElem (SUMapKItem x y) subG = (case (regularizeInSUKLabel x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow>
    (case regularizeInSUKList y subG of None \<Rightarrow> None
       | Some y' \<Rightarrow> Some (SUMapKItem x' y')))"
| "regularizeInSUMap [] subG = Some []"
| "regularizeInSUMap (b#l) subG =
   (case regularizeInSUMapElem b subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case regularizeInSUMap l subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> (if isCommonElemInSUMap b' l' subG
            then Some l' else 
   (case b' of (ItemM x y) \<Rightarrow> (case getValueInSUMap x l' subG of None \<Rightarrow> Some (b'#l')
          | Some y' \<Rightarrow> None)
     | _ \<Rightarrow> Some (b'#l')))))"
| "regularizeInSUBagElem (IdB x) subG = Some (IdB x)"
| "regularizeInSUBagElem (ItemB x y z) subG = (case (regularizeInSUBigKWithBag z subG)
    of None \<Rightarrow> None | Some z' \<Rightarrow> Some (ItemB x y z'))"
| "regularizeInSUBag [] subG = Some []"
| "regularizeInSUBag (b#l) subG =
   (case regularizeInSUBagElem b subG of None \<Rightarrow> None
     | Some b' \<Rightarrow> (case regularizeInSUBag l subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some (b'#l')))"

(* type check programs *)
definition typeCheckProgramState where
"typeCheckProgramState a database subG = (if isGroundTermInSUBag a
    then (case checkTermsInSUBag a [] [] database subG
          of None \<Rightarrow> None | Some (acc,beta,aa) \<Rightarrow>
        regularizeInSUBag aa subG) else None)"

definition typeCheckCondition where
"typeCheckCondition a database subG = (if isGroundTermInSUKItem a
    then (case checkTermsInSUKItem a [Bool] [] [] database subG
          of None \<Rightarrow> None | Some (acc,beta,aa) \<Rightarrow>
         regularizeInSUKItem aa subG) else None)"

(*
definition validConfiguration where
"validConfiguration a = (case uniqueCellNameInSUBag a [] of None \<Rightarrow> False
     | _ \<Rightarrow> (noDotInSUBag a \<and> hasNoBagVarInSUBag a))"
*)
(* check and get all macro rules *)

primrec subSyntaxInSUKLabel
    and subSyntaxInSUKItem
    and subSyntaxInSUKListElem
    and subSyntaxInSUKList
    and subSyntaxInSUKElem
    and subSyntaxInSUK
    and subSyntaxInSUListElem
    and subSyntaxInSUList
    and subSyntaxInSUSetElem
    and subSyntaxInSUSet
    and subSyntaxInSUMapElem
    and subSyntaxInSUMap
    and subSyntaxInSUBigKWithBag
    and subSyntaxInSUBigKWithLabel
    and subSyntaxInSUBagElem
    and subSyntaxInSUBag where
 "subSyntaxInSUKLabel s kl (SUKLabel a') subG = False"
| "subSyntaxInSUKLabel s kl (SUIdKLabel a) subG = False"
| "subSyntaxInSUKLabel s kl (SUKLabelFun a b) subG =
           (subSyntaxInSUKLabel s kl a subG \<or> subSyntaxInSUKList s kl b subG)"
| "subSyntaxInSUKItem s kl (SUKItem l r ty) subG = (case getSUKLabelMeaning l of None \<Rightarrow>
          (subSyntaxInSUKLabel s kl l subG \<or> subSyntaxInSUKList s kl r subG)
       | Some ss \<Rightarrow> if s = ss then
         (case syntacticMonoidInSUKList kl r subG of None \<Rightarrow> subSyntaxInSUKList s kl r subG
             | Some kl' \<Rightarrow> True) else subSyntaxInSUKList s kl r subG)"
| "subSyntaxInSUKItem s kl (SUHOLE a) subG = False"
| "subSyntaxInSUKItem s kl (SUIdKItem a b) subG = False"
| "subSyntaxInSUKListElem s kl (IdKl x) subG = False"
| "subSyntaxInSUKListElem s kl (ItemKl x) subG = subSyntaxInSUBigKWithLabel s kl x subG"
| "subSyntaxInSUKList s kl [] subG = False"
| "subSyntaxInSUKList s kl (b#l) subG = 
     (subSyntaxInSUKListElem s kl b subG \<or> subSyntaxInSUKList s kl l subG)"
| "subSyntaxInSUBigKWithLabel s kl (SUBigBag a) subG = subSyntaxInSUBigKWithBag s kl a subG"
| "subSyntaxInSUBigKWithLabel s kl (SUBigLabel a) subG = subSyntaxInSUKLabel s kl a subG"
| "subSyntaxInSUBigKWithBag s kl (SUK a) subG = subSyntaxInSUK s kl a subG"
| "subSyntaxInSUBigKWithBag s kl (SUList a) subG = subSyntaxInSUList s kl a subG"
| "subSyntaxInSUBigKWithBag s kl (SUSet a) subG = subSyntaxInSUSet s kl a subG"
| "subSyntaxInSUBigKWithBag s kl (SUMap a) subG = subSyntaxInSUMap s kl a subG"
| "subSyntaxInSUBigKWithBag s kl (SUBag a) subG = subSyntaxInSUBag s kl a subG"
| "subSyntaxInSUKElem s kl (IdFactor x) subG = False"
| "subSyntaxInSUKElem s kl (ItemFactor x) subG = subSyntaxInSUKItem s kl x subG"
| "subSyntaxInSUKElem s kl (SUKKItem x y ty) subG =
    (subSyntaxInSUKLabel s kl x subG \<or> subSyntaxInSUKList s kl y subG)"
| "subSyntaxInSUK s kl [] subG = False"
| "subSyntaxInSUK s kl (b#l) subG = (subSyntaxInSUKElem s kl b subG \<or> subSyntaxInSUK s kl l subG)"
| "subSyntaxInSUListElem s kl (IdL x) subG = False"
| "subSyntaxInSUListElem s kl (ItemL x) subG = subSyntaxInSUK s kl x subG"
| "subSyntaxInSUListElem s kl (SUListKItem x y) subG =
    (subSyntaxInSUKLabel s kl x subG \<or> subSyntaxInSUKList s kl y subG)"
| "subSyntaxInSUList s kl [] subG = False"
| "subSyntaxInSUList s kl (b#l) subG =
            (subSyntaxInSUListElem s kl b subG \<or> subSyntaxInSUList s kl l subG)"
| "subSyntaxInSUSetElem s kl (IdS x) subG = False"
| "subSyntaxInSUSetElem s kl (ItemS x) subG = subSyntaxInSUK s kl x subG"
| "subSyntaxInSUSetElem s kl (SUSetKItem x y) subG =
    (subSyntaxInSUKLabel s kl x subG \<or> subSyntaxInSUKList s kl y subG)"
| "subSyntaxInSUSet s kl [] subG = False"
| "subSyntaxInSUSet s kl (b#l) subG = 
   (subSyntaxInSUSetElem s kl b subG \<or> subSyntaxInSUSet s kl l subG)"
| "subSyntaxInSUMapElem s kl (IdM x) subG = False"
| "subSyntaxInSUMapElem s kl (ItemM x y) subG =
    (subSyntaxInSUK s kl x subG \<or> subSyntaxInSUK s kl y subG)"
| "subSyntaxInSUMapElem s kl (SUMapKItem x y) subG =
    (subSyntaxInSUKLabel s kl x subG \<or> subSyntaxInSUKList s kl y subG)"
| "subSyntaxInSUMap s kl [] subG = False"
| "subSyntaxInSUMap s kl (b#l) subG =
   (subSyntaxInSUMapElem s kl b subG \<or> subSyntaxInSUMap s kl l subG)"
| "subSyntaxInSUBagElem s kl (IdB x) subG = False"
| "subSyntaxInSUBagElem s kl (ItemB x y z) subG = subSyntaxInSUBigKWithBag s kl z subG"
| "subSyntaxInSUBag s kl [] subG = False"
| "subSyntaxInSUBag s kl (b#l) subG = 
      (subSyntaxInSUBagElem s kl b subG \<or> subSyntaxInSUBag s kl l subG)"

primrec irToSUInKLabel where
  "irToSUInKLabel (IRKLabel a) = SUKLabel a"
| "irToSUInKLabel (IRIdKLabel n) = (SUIdKLabel n)"

fun irToSUInKItem
    and irToSUInKList
    and irToSUInK
    and irToSUInList
    and irToSUInSet
    and irToSUInMap
    and irToSUInBigKWithBag
    and irToSUInBigKWithLabel
    and irToSUInBag where 
 "irToSUInKItem (IRKItem l r ty) = (SUKItem (irToSUInKLabel l) (irToSUInKList r) ty)"
| "irToSUInKItem (IRIdKItem a b) = (SUIdKItem a b)"
| "irToSUInKItem (IRHOLE a) = (SUHOLE a)"
| "irToSUInKList (KListPatNoVar l) = 
   (List.map (\<lambda> x . ItemKl (irToSUInBigKWithLabel x)) l)"
| "irToSUInKList (KListPat l a r) = 
   (List.map (\<lambda> x . ItemKl (irToSUInBigKWithLabel x)) l)@[IdKl a]
          @((List.map (\<lambda> x . ItemKl (irToSUInBigKWithLabel x)) r))"
| "irToSUInBigKWithLabel (IRBigBag a) = SUBigBag (irToSUInBigKWithBag a)"
| "irToSUInBigKWithLabel (IRBigLabel a) = SUBigLabel (irToSUInKLabel a)"
| "irToSUInBigKWithBag (IRK a) = SUK (irToSUInK a)"
| "irToSUInBigKWithBag (IRList a) = SUList (irToSUInList a)"
| "irToSUInBigKWithBag (IRSet a) = SUSet (irToSUInSet a)"
| "irToSUInBigKWithBag (IRMap a) = SUMap (irToSUInMap a)"
| "irToSUInBigKWithBag (IRBag a) = SUBag (irToSUInBag a)"
| "irToSUInK (KPat l a) = (case a of None
       \<Rightarrow> List.map (\<lambda> x . (case x of (IRIdKItem u v) \<Rightarrow>
           if v = [K] then (IdFactor u) else ItemFactor (irToSUInKItem x)
            | _ \<Rightarrow> ItemFactor (irToSUInKItem x))) l
   | Some a'
      \<Rightarrow> (List.map (\<lambda> x . (case x of (IRIdKItem u v) \<Rightarrow>
           if v = [K] then (IdFactor u) else ItemFactor (irToSUInKItem x)
            | _ \<Rightarrow> ItemFactor (irToSUInKItem x))) l)@[(IdFactor a')])"
| "irToSUInList (ListPatNoVar l) =
     (List.map (\<lambda> x . ItemL (irToSUInK x)) l)"
| "irToSUInList (ListPat l a r) =
     (List.map (\<lambda> x . ItemL (irToSUInK x)) l)@[IdL a]
          @((List.map (\<lambda> x . ItemL (irToSUInK x)) r))"
| "irToSUInSet (SetPat l a) = (case a of None
       \<Rightarrow> List.map (\<lambda> x . ItemS (irToSUInK x)) l
   | Some a'
      \<Rightarrow> (List.map (\<lambda> x . ItemS (irToSUInK x)) l)@[(IdS a')])"
| "irToSUInMap (MapPat l a) = (case a of None
       \<Rightarrow> List.map (\<lambda> (x,y) . ItemM (irToSUInK x) (irToSUInK y)) l
   | Some a'
      \<Rightarrow> (List.map (\<lambda> (x,y) . ItemM (irToSUInK x) (irToSUInK y)) l)@[(IdM a')])"
| "irToSUInBag (BagPat l a) = (case a of None
       \<Rightarrow> List.map (\<lambda> (a,b,c) . ItemB a b (irToSUInBigKWithBag c)) l
   | Some a'  \<Rightarrow>
        (List.map (\<lambda> (a,b,c) . ItemB a b (irToSUInBigKWithBag c)) l)@[(IdB a')])"

primrec irToSUInMatchFactor where
"irToSUInMatchFactor (KLabelMatching a) = KLabelSubs (irToSUInKLabel a)"
| "irToSUInMatchFactor (KItemMatching a) = KItemSubs (irToSUInKItem a)"
| "irToSUInMatchFactor (KMatching a) = KSubs (irToSUInK a)"
| "irToSUInMatchFactor (KListMatching a) = KListSubs (irToSUInKList a)"
| "irToSUInMatchFactor (ListMatching a) = ListSubs (irToSUInList a)"
| "irToSUInMatchFactor (SetMatching a) = SetSubs (irToSUInSet a)"
| "irToSUInMatchFactor (MapMatching a) = MapSubs (irToSUInMap a)"
| "irToSUInMatchFactor (BagMatching a) = BagSubs (irToSUInBag a)"

primrec irToSUInPat where
"irToSUInPat (KLabelFunPat s l) database = KLabelSubs (SUKLabelFun (SUKLabel s) (irToSUInKList l))"
| "irToSUInPat (KItemFunPat s l) database = (case getSort s database of Some ty
              \<Rightarrow> KItemSubs (SUKItem (SUKLabel s) (irToSUInKList l) ty)
             | _ \<Rightarrow> KItemSubs (SUKItem (SUKLabel s) (irToSUInKList l) [KItem]))"
| "irToSUInPat (KFunPat s l) database = KSubs [SUKKItem (SUKLabel s) (irToSUInKList l) [K]]"
| "irToSUInPat (ListFunPat s l) database = ListSubs [SUListKItem (SUKLabel s) (irToSUInKList l)]"
| "irToSUInPat (SetFunPat s l) database = SetSubs [SUSetKItem (SUKLabel s) (irToSUInKList l)]"
| "irToSUInPat (MapFunPat s l) database = MapSubs [SUMapKItem (SUKLabel s) (irToSUInKList l)]"
| "irToSUInPat (NormalPat a) database = irToSUInMatchFactor a"

fun irToSUInIRBagList where
"irToSUInIRBagList [] = []"
| "irToSUInIRBagList ((x,y,z)#l) = (ItemB x y (irToSUInBigKWithBag z))#(irToSUInIRBagList l)"

primrec sizeInSUKLabel
  and sizeInSUKItem
  and sizeInSUKListElem
  and sizeInSUKList
  and sizeInSUKElem
  and sizeInSUK
  and sizeInSUListElem
  and sizeInSUList
  and sizeInSUSetElem
  and sizeInSUSet
  and sizeInSUMapElem
  and sizeInSUMap
  and sizeInSUBigKWithBag
  and sizeInSUBigKWithLabel
  and sizeInSUBagElem
  and sizeInSUBag where
"sizeInSUKLabel (SUKLabel a) = 0"
|"sizeInSUKLabel (SUIdKLabel a) = 0"
| "sizeInSUKLabel (SUKLabelFun a b) = 1 + (sizeInSUKLabel a) + (sizeInSUKList b)"
| "sizeInSUKItem (SUKItem a b t) = 1 + (sizeInSUKLabel a) + (sizeInSUKList b)"
| "sizeInSUKItem (SUIdKItem a t) = 0"
| "sizeInSUKItem (SUHOLE t) = 0"
| "sizeInSUKListElem (ItemKl a) = 1 + (sizeInSUBigKWithLabel a)"
| "sizeInSUKListElem (IdKl a) = 0"
| "sizeInSUKList [] = 0"
| "sizeInSUKList (a#l) = 1 + (sizeInSUKListElem a) + (sizeInSUKList l)"
| "sizeInSUKElem (ItemFactor a) = 1 + (sizeInSUKItem a)"
| "sizeInSUKElem (IdFactor a) = 0"
| "sizeInSUKElem (SUKKItem a b t) = 1 + (sizeInSUKLabel a) + (sizeInSUKList b)"
| "sizeInSUK [] = 0"
| "sizeInSUK (a#l) = 1 + (sizeInSUKElem a) + (sizeInSUK l)"
| "sizeInSUListElem (ItemL a) = 1 + (sizeInSUK a)"
| "sizeInSUListElem (IdL a) = 0"
| "sizeInSUListElem (SUListKItem a b) = 1 + (sizeInSUKLabel a) + (sizeInSUKList b)"
| "sizeInSUList [] = 0"
| "sizeInSUList (a#l) = 1 + (sizeInSUListElem a) + (sizeInSUList l)"
| "sizeInSUSetElem (ItemS a) = 1 + (sizeInSUK a)"
| "sizeInSUSetElem (IdS a) = 0"
| "sizeInSUSetElem (SUSetKItem a b) = 1 + (sizeInSUKLabel a) + (sizeInSUKList b)"
| "sizeInSUSet [] = 0"
| "sizeInSUSet (a#l) = 1 + (sizeInSUSetElem a) + (sizeInSUSet l)"
| "sizeInSUMapElem (ItemM a b) = 1 + (sizeInSUK a) + (sizeInSUK b)"
| "sizeInSUMapElem (IdM a) = 0"
| "sizeInSUMapElem (SUMapKItem a b) = 1 + (sizeInSUKLabel a) + (sizeInSUKList b)"
| "sizeInSUMap [] = 0"
| "sizeInSUMap (a#l) = 1 + (sizeInSUMapElem a) + (sizeInSUMap l)"
| "sizeInSUBigKWithBag (SUK a) = 1 + (sizeInSUK a)"
| "sizeInSUBigKWithBag (SUList a) = 1 + (sizeInSUList a)"
| "sizeInSUBigKWithBag (SUSet a) = 1 + (sizeInSUSet a)"
| "sizeInSUBigKWithBag (SUMap a) = 1 + (sizeInSUMap a)"
| "sizeInSUBigKWithBag (SUBag a) = 1 + (sizeInSUBag a)"
| "sizeInSUBigKWithLabel (SUBigBag a) = 1 + (sizeInSUBigKWithBag a)"
| "sizeInSUBigKWithLabel (SUBigLabel a) = 1 + (sizeInSUKLabel a)"
| "sizeInSUBagElem (ItemB x y z) = 1 + (sizeInSUBigKWithBag z)"
| "sizeInSUBagElem (IdB a) = 0"
| "sizeInSUBag [] = 0"
| "sizeInSUBag (a#l) = 1 + (sizeInSUBagElem a) + (sizeInSUBag l)"

function suToIRInKLabel
    and suToIRInKItem
    and suToIRInKList
    and suToIRInK
    and suToIRInList
    and suToIRInSet
    and suToIRInMap
    and suToIRInBigKWithBag
    and suToIRInBigKWithLabel
    and suToIRInBag  where 
  "suToIRInKLabel (SUKLabel a) database = Some (NormalPat (KLabelMatching (IRKLabel a)))"
| "suToIRInKLabel (SUKLabelFun a b) database = (case getSUKLabelMeaning a of None \<Rightarrow> None
         | Some s \<Rightarrow> (case (suToIRInKList b database) of None \<Rightarrow> None
         | Some b' \<Rightarrow> Some (KLabelFunPat s b')))"
| "suToIRInKLabel (SUIdKLabel n) database = Some (NormalPat (KLabelMatching (IRIdKLabel n)))"
| "suToIRInKItem (SUKItem l r ty) database = (case getSUKLabelMeaning l of None \<Rightarrow>
     (case (suToIRInKLabel l database, suToIRInKList r database) 
        of (Some (NormalPat (KLabelMatching l')), Some r')
             \<Rightarrow> Some (NormalPat (KItemMatching (IRKItem l' r' ty)))
         | _ \<Rightarrow> None)
      | Some s \<Rightarrow> (if isFunctionItem s database then
      (case suToIRInKList r database of None \<Rightarrow> None
          | Some r' \<Rightarrow> Some (KFunPat s r')) else
            (case (suToIRInKLabel l database, suToIRInKList r database) 
        of (Some (NormalPat (KLabelMatching l')), Some r')
                \<Rightarrow> Some (NormalPat (KItemMatching (IRKItem l' r' ty)))
         | _ \<Rightarrow> None)))"
| "suToIRInKItem (SUIdKItem a b) database = Some (NormalPat (KItemMatching (IRIdKItem a b)))"
| "suToIRInKItem (SUHOLE a) database = Some (NormalPat (KItemMatching (IRHOLE a)))"
| "suToIRInKList [] database = Some (KListPatNoVar [])"
| "suToIRInKList (b#l) database = (case suToIRInKList l database of None \<Rightarrow> None
        | Some (KListPatNoVar la) \<Rightarrow> (case b of (ItemKl x) 
         \<Rightarrow> (case suToIRInBigKWithLabel x database of None \<Rightarrow> None
            | Some x' \<Rightarrow> Some (KListPatNoVar (x'#la)))
           | IdKl x \<Rightarrow> Some (KListPat [] x la))
        | Some (KListPat la x ra) \<Rightarrow> (case b of (ItemKl u) 
         \<Rightarrow> (case suToIRInBigKWithLabel u database of None \<Rightarrow> None
            | Some u' \<Rightarrow> Some (KListPat (u'#la) x ra))
             | IdKl u \<Rightarrow> None))"
| "suToIRInBigKWithLabel (SUBigBag a) database =
      (case (suToIRInBigKWithBag a database) of None \<Rightarrow> None
                    | Some a' \<Rightarrow> Some (IRBigBag a'))"
| "suToIRInBigKWithLabel (SUBigLabel a) database = (case (suToIRInKLabel a database) of
        Some (NormalPat (KLabelMatching a')) \<Rightarrow> Some (IRBigLabel a')
                    | _ \<Rightarrow> None)"
| "suToIRInBigKWithBag (SUK a) database = (case (suToIRInK a database) of
         Some (NormalPat (KMatching a')) \<Rightarrow> Some (IRK a')
                    | _ \<Rightarrow> None)"
| "suToIRInBigKWithBag (SUList a) database = (case (suToIRInList a database) of
         Some (NormalPat (ListMatching a')) \<Rightarrow> Some (IRList a')
                    | _ \<Rightarrow> None)"
| "suToIRInBigKWithBag (SUSet a) database = (case (suToIRInSet a database) of
         Some (NormalPat (SetMatching a')) \<Rightarrow> Some (IRSet a')
                    | _ \<Rightarrow> None)"
| "suToIRInBigKWithBag (SUMap a) database = (case (suToIRInMap a database) of
         Some (NormalPat (MapMatching a')) \<Rightarrow> Some (IRMap a')
                    | _ \<Rightarrow> None)"
| "suToIRInBigKWithBag (SUBag a) database = (case (suToIRInBag a database) of None \<Rightarrow> None
                    | Some a' \<Rightarrow> Some (IRBag a'))"
| "suToIRInK [] database = Some (NormalPat (KMatching (KPat [] None)))"
| "suToIRInK (b#l) database = (case suToIRInK l database of
        Some (NormalPat (KMatching (KPat t None)))
          \<Rightarrow> (case b of (ItemFactor x) 
             \<Rightarrow> (if t = [] then (case x of (SUIdKItem xa xty) \<Rightarrow>
               if xty = [K] then Some (NormalPat (KMatching (KPat [] (Some xa))))
                 else Some (NormalPat (KMatching (KPat [(IRIdKItem xa xty)] None)))
           | _ \<Rightarrow> (case suToIRInKItem x database of Some (NormalPat (KItemMatching x'))
                 \<Rightarrow> Some (NormalPat (KMatching (KPat [x'] None)))))
     else (case suToIRInKItem x database of Some (NormalPat (KItemMatching x'))
                 \<Rightarrow> Some (NormalPat (KMatching (KPat (x'#t) None)))
             | _ \<Rightarrow> None))
           | IdFactor x \<Rightarrow> (if t = [] then
                 Some (NormalPat (KMatching (KPat [] (Some x)))) else
                 Some (NormalPat (KMatching (KPat ((IRIdKItem x [K])#t) None))))
           | SUKKItem u v ty \<Rightarrow> (if t = [] then
           (case getSUKLabelMeaning u of None \<Rightarrow> None
              | Some s \<Rightarrow> if isFunctionItem s database then
               (case suToIRInKList v database of Some v'
                    \<Rightarrow> Some (KFunPat s v')
                 | _ \<Rightarrow> None) else None) else None))
        | Some (NormalPat (KMatching (KPat t (Some v))))
         \<Rightarrow> (case b of (ItemFactor x) 
            \<Rightarrow> (case suToIRInKItem x database of Some (NormalPat (KItemMatching x'))
                 \<Rightarrow> Some (NormalPat (KMatching (KPat (x'#t) None)))
             | _ \<Rightarrow> None)
             | IdFactor x \<Rightarrow>
                   Some (NormalPat (KMatching (KPat ((IRIdKItem x [K])#t) (Some v))))
             | SUKKItem u v ty \<Rightarrow> None)
        | _ \<Rightarrow> None)"
| "suToIRInList [] database = Some (NormalPat (ListMatching (ListPatNoVar [])))"
| "suToIRInList (b#l) database = (case suToIRInList l database of
       Some (NormalPat (ListMatching (ListPatNoVar la)))
         \<Rightarrow> (case b of (ItemL x)
           \<Rightarrow> (case suToIRInK x database of Some (NormalPat (KMatching x'))
            \<Rightarrow> Some (NormalPat (ListMatching (ListPatNoVar (x'#la))))
                       | _ \<Rightarrow> None)
           | IdL x \<Rightarrow> Some (NormalPat (ListMatching (ListPat [] x la)))
           | SUListKItem u v \<Rightarrow> if la = [] then 
             (case getSUKLabelMeaning u of None \<Rightarrow> None
                | Some s \<Rightarrow> (if isFunctionItem s database then
                  (case suToIRInKList v database of None \<Rightarrow> None
                    | Some v' \<Rightarrow> Some (ListFunPat s v')) else None))
                    else None)
        | Some (NormalPat (ListMatching (ListPat la x ra)))
           \<Rightarrow> (case b of (ItemL u)
             \<Rightarrow> (case suToIRInK u database of Some (NormalPat (KMatching u'))
              \<Rightarrow> Some (NormalPat (ListMatching (ListPat (u'#la) x ra)))
                  | _ \<Rightarrow> None)
                | IdL u \<Rightarrow> None
               | SUListKItem u v \<Rightarrow> None)
           | _ \<Rightarrow> None)"
| "suToIRInSet [] database = Some (NormalPat (SetMatching (SetPat [] None)))"
| "suToIRInSet (b#l) database = (case suToIRInSet l database of 
       Some (NormalPat (SetMatching (SetPat t None)))
       \<Rightarrow> (case b of (ItemS x) 
         \<Rightarrow> (case suToIRInK x database of Some (NormalPat (KMatching x'))
           \<Rightarrow> Some (NormalPat (SetMatching (SetPat (x'#t) None)))
                | _ \<Rightarrow> None)
           | IdS x \<Rightarrow> Some (NormalPat (SetMatching (SetPat t (Some x))))
          | SUSetKItem u v \<Rightarrow> if t = [] then
            (case getSUKLabelMeaning u of None \<Rightarrow> None
                | Some u' \<Rightarrow> if isFunctionItem u' database then
                 (case suToIRInKList v database of None \<Rightarrow> None
                    | Some v' \<Rightarrow> Some (SetFunPat u' v')) else None) else None)
        | Some (NormalPat (SetMatching (SetPat t (Some v))))
         \<Rightarrow> (case b of (ItemS x) 
         \<Rightarrow> (case suToIRInK x database of Some (NormalPat (KMatching x'))
            \<Rightarrow> Some (NormalPat (SetMatching (SetPat (x'#t) (Some v))))
                | _ \<Rightarrow> None)
             | IdS x \<Rightarrow> None
             | (SUSetKItem u v) \<Rightarrow> None)
        | _ \<Rightarrow> None)"
| "suToIRInMap [] database = Some (NormalPat (MapMatching (MapPat [] None)))"
| "suToIRInMap (b#l) database = (case suToIRInMap l database of 
       Some (NormalPat (MapMatching (MapPat t None)))
       \<Rightarrow> (case b of (ItemM x y) 
         \<Rightarrow> (case (suToIRInK x database, suToIRInK y database)
          of (Some (NormalPat (KMatching x')), Some (NormalPat (KMatching y')))
           \<Rightarrow> Some (NormalPat (MapMatching (MapPat ((x',y')#t) None)))
                | _ \<Rightarrow> None)
           | IdM x \<Rightarrow> Some (NormalPat (MapMatching (MapPat t (Some x))))
          | SUMapKItem u v \<Rightarrow> if t = [] then
            (case getSUKLabelMeaning u of None \<Rightarrow> None
                | Some u' \<Rightarrow> if isFunctionItem u' database then
                 (case suToIRInKList v database of None \<Rightarrow> None
                    | Some v' \<Rightarrow> Some (MapFunPat u' v')) else None) else None)
        | Some (NormalPat (MapMatching (MapPat t (Some v))))
         \<Rightarrow> (case b of (ItemM x y)  \<Rightarrow> 
              (case (suToIRInK x database, suToIRInK y database) of
          (Some (NormalPat (KMatching x')), Some (NormalPat (KMatching y')))
            \<Rightarrow> Some (NormalPat (MapMatching (MapPat ((x',y')#t) (Some v))))
                | _ \<Rightarrow> None)
             | IdM x \<Rightarrow> None
             | (SUMapKItem u v) \<Rightarrow> None)
        | _ \<Rightarrow> None)"
| "suToIRInBag [] database = Some (BagPat [] None)"
| "suToIRInBag (b#l) database = (case suToIRInBag l database of None \<Rightarrow> None
        | Some (BagPat t None) \<Rightarrow> (case b of (ItemB a b c) 
         \<Rightarrow> (case suToIRInBigKWithBag c database of None \<Rightarrow> None
            | Some c' \<Rightarrow> Some (BagPat ((a,b,c')#t) None))
           | IdB x \<Rightarrow> Some (BagPat t (Some x)))
        | Some (BagPat t (Some v)) \<Rightarrow> (case b of (ItemB a b c) 
         \<Rightarrow> (case suToIRInBigKWithBag c database of None \<Rightarrow> None
            | Some c' \<Rightarrow> Some (BagPat ((a,b,c')#t) (Some v)))
           | IdB x \<Rightarrow> None))"
by pat_completeness auto

termination
by (relation "measure (\<lambda> x . (case x of Inl x1 => (case x1 of Inl x2
       \<Rightarrow> (case x2 of Inl (a,b) \<Rightarrow> sizeInSUKLabel a | Inr (a,b) \<Rightarrow> sizeInSUKItem a)
        | Inr x3 \<Rightarrow> (case x3 of Inl (a,b) \<Rightarrow> sizeInSUKList a | Inr x4 \<Rightarrow> 
       (case x4 of Inl (a,b) \<Rightarrow> sizeInSUK a | Inr (a,b) \<Rightarrow> sizeInSUList a)))
      | Inr x1 => (case x1 of Inl x2
       \<Rightarrow> (case x2 of Inl (a,b) \<Rightarrow> sizeInSUSet a | Inr (a,b) \<Rightarrow> sizeInSUMap a)
        | Inr x3 \<Rightarrow> (case x3 of Inl (a,b) \<Rightarrow> sizeInSUBigKWithBag a | Inr x4 \<Rightarrow> 
       (case x4 of Inl (a,b) \<Rightarrow> sizeInSUBigKWithLabel a | Inr (a,b) \<Rightarrow> sizeInSUBag a)))))") auto

primrec suToIRInSubsFactor where
"suToIRInSubsFactor (KLabelSubs a) database = (suToIRInKLabel a database)"
| "suToIRInSubsFactor (KItemSubs a) database = (suToIRInKItem a database)"
| "suToIRInSubsFactor (KSubs a) database = (suToIRInK a database)"
| "suToIRInSubsFactor (KListSubs a) database = (case suToIRInKList a database of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (NormalPat (KListMatching a')))"
| "suToIRInSubsFactor (ListSubs a) database = (suToIRInList a database)"
| "suToIRInSubsFactor (SetSubs a) database = (suToIRInSet a database)"
| "suToIRInSubsFactor (MapSubs a) database = (suToIRInMap a database)"
| "suToIRInSubsFactor (BagSubs a) database = (case suToIRInBag a database of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (NormalPat (BagMatching a')))"

fun divideMacroRules where
"divideMacroRules [] subG = Some ([],[])"
| "divideMacroRules ((MacroPat x y z)#l) subG = (if subSyntaxInSUK x (irToSUInKList y) z subG
               then (case divideMacroRules l subG of None \<Rightarrow> None
                 | Some (l',S) \<Rightarrow> Some (Some (x,y,z)#l',S)) else None)"
| "divideMacroRules (x#l) subG = (case divideMacroRules l subG of None \<Rightarrow> None
       | Some (l', S)  \<Rightarrow> Some (l', x#S))"

(* type check all rules 
definition typeCheckRules where
"typeCheckRules Theory database subG =
    (case normalizeRules (getAllRules Theory) Theory database subG of None \<Rightarrow> None
       | Some l \<Rightarrow> if wellFormRules l then
         inferTypesInRules l Theory database subG else None)"

(* check uniqueness of KLabel in a spec *)
definition uniqueKLabelSyntax where
"uniqueKLabelSyntax Theory = isUnitLabel (syntaxSetToKItemSet Theory)"
*)
(* giving a list of input initial program and a configuration, generating a initial program state *)
fun bagContainsCell :: "'var var \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
                  \<Rightarrow> bool"
   and bagContainsCellAux :: "'var var
      \<Rightarrow> ('upVar, 'var, 'metaVar) suBigKWithBag
                  \<Rightarrow> bool"
 where
"bagContainsCell x [] = False"
| "bagContainsCell x (b#l) = (case b of IdB a \<Rightarrow> bagContainsCell x l
          | ItemB u v w \<Rightarrow> if x = u then True else
         (bagContainsCellAux x w \<or> bagContainsCell x l))"
| "bagContainsCellAux x (SUBag y) = bagContainsCell x y"
| "bagContainsCellAux x y = False"

fun createInitState
    and createInitStateAux where
"createInitState [] = Some []"
| "createInitState (b#l) = (case b of IdB x \<Rightarrow> None
         | ItemB x y z \<Rightarrow> if Multiplicity Star \<in> set y
               \<or> Multiplicity Question \<in> set y then
       (if bagContainsCellAux LittleK z then (case createInitStateAux z of None \<Rightarrow> None
            | Some z' \<Rightarrow> (case createInitState l of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((ItemB x y z')#l')))
     else (case createInitState l of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some l')) else
        (case createInitStateAux z of None \<Rightarrow> None
            | Some z' \<Rightarrow> (case createInitState l of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((ItemB x y z')#l'))))"
| "createInitStateAux (SUBag x) = (case createInitState x of None \<Rightarrow> None
            | Some x' \<Rightarrow> Some (SUBag x'))"
| "createInitStateAux a = Some a"

(* checks needing to be made: 1, it is a ground term. 2, it is type checked 
definition configurationTest where
"configurationTest Theory database subG = (case getConfiguration Theory of [a] \<Rightarrow>
        (case toSUInBag a of None \<Rightarrow> None | Some a' \<Rightarrow>
        if validConfiguration a' then 
       (case checkTermsInSUBag a' []
                  (constructSortMap (getDomainInSUBag a')) database subG of None \<Rightarrow> None
           | Some (acc,beta, akl) \<Rightarrow> if hasNoTop acc \<and> hasNoTop beta then
        (case replaceVarSortInSUBag akl acc beta subG of None \<Rightarrow> None
       | Some kla \<Rightarrow> regularizeInSUBag kla subG) else None) else None) | _ \<Rightarrow> None)"

definition realConfigurationTest where
"realConfigurationTest l Theory database subG 
    = (case getConfiguration Theory of [a] \<Rightarrow>
        (case toSUInBag a of None \<Rightarrow> None | Some a' \<Rightarrow>
        if validConfiguration a' then 
          (case composeConfiAndProgInSUBag a' l subG of None \<Rightarrow> None
             | Some aa \<Rightarrow>
         typeCheckProgramState aa database subG) else None))"
*)
(*
(checkTermsInSUBag (irToSUInBag kl) [],
              checkTermsInSUBag r [], checkTermsInSUKItem c KItem [])
           of (Some (acckl, kl'), Some (accsl, sl'), Some (accz, z')) \<Rightarrow>
    (case (makeSortMap acckl, makeSortMap accsl, makeSortMap accz) of
        (Some acckl', Some accsl', Some accz') \<Rightarrow>
      (case (replaceVarSortInSUBag kl' acckl', replaceVarSortInSUBag sl' accsl',
      replaceVarSortInSUKItem z' accz') of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUBag kla *)

(* the pattern matching algorithm *)
fun macroEquality where
"macroEquality (KLabelSubs a) (KLabelSubs b) subG = 
      (case syntacticMonoidInSUKLabel a b subG of Some a' \<Rightarrow> Some (KLabelSubs a')
          | None \<Rightarrow> None)"
| "macroEquality (KItemSubs a) (KItemSubs b) subG =
  (case syntacticMonoidInSUKItem a b subG
     of Some a' \<Rightarrow> Some (KItemSubs a')
      | _ \<Rightarrow> None)"
| "macroEquality (KListSubs a) (KListSubs b) subG =
   (case syntacticMonoidInSUKList a b subG
       of Some a' \<Rightarrow> Some (KListSubs a')
        | _ \<Rightarrow> None)"
| "macroEquality (KSubs a) (KSubs b) subG =
   (case syntacticMonoidInSUK a b subG
        of Some a' \<Rightarrow> Some (KSubs a')
                 | _ \<Rightarrow> None)"
| "macroEquality (ListSubs a) (ListSubs b) subG =
 (case syntacticMonoidInSUList a b subG
    of Some a' \<Rightarrow> Some (ListSubs a')
     | _ \<Rightarrow> None)"
| "macroEquality (SetSubs a) (SetSubs b) subG =
  (case syntacticMonoidInSUSet a b a subG
     of Some a' \<Rightarrow> Some (SetSubs a')
      | _ \<Rightarrow> None)"
| "macroEquality (MapSubs a) (MapSubs b) subG =
  (case syntacticMonoidInSUMap a b a subG
     of Some a' \<Rightarrow> Some (MapSubs a')
      | _ \<Rightarrow> None)"
| "macroEquality (BagSubs a) (BagSubs b) subG =
  (case syntacticMonoidInSUBag a b subG
     of Some a' \<Rightarrow> Some (BagSubs a')
     | _ \<Rightarrow> None)"
| "macroEquality A B subG = None"

fun updateMatchingMapMacro where
"updateMatchingMapMacro x y [] subG = Some [(x,y)]"
| "updateMatchingMapMacro x y ((a,b)#l) subG = (if x = a then
           (case macroEquality y b subG of None \<Rightarrow> None
               | Some y' \<Rightarrow> Some ((a,y')#l))
             else (case updateMatchingMapMacro x y l subG of None \<Rightarrow> None
                 | Some l' \<Rightarrow> Some ((a,b)#l')))"

primrec getValueInMatchingMap where
"getValueInMatchingMap a [] = None"
| "getValueInMatchingMap a (b#l) = (case b of (x',y') \<Rightarrow>
               if a = x' then Some y' else getValueInMatchingMap a l)"

(* divide the map into two parts: one's values have zero list,
          the other's value have more than zero element list*)
fun searchZero where
"searchZero [] = ([],[])"
| "searchZero ((a,b)#l) = (case searchZero l of (have, noHave) \<Rightarrow>
                     if b = [] then ((a,b)#have,noHave) else (have,(a,b)#noHave))"

fun eliminateEntry where
"eliminateEntry a [] = []"
| "eliminateEntry a ((b,c)#l) = (if a = b then l else (b,c)#eliminateEntry a l)"

fun eliminateEntryList where
"eliminateEntryList a [] = []"
| "eliminateEntryList a ((b,c)#l) = (b,eliminateEntry a c)#eliminateEntryList a l"

fun eliminateEntryMap where
"eliminateEntryMap [] S = Some S"
| "eliminateEntryMap ((a,(b,c))#l) S = eliminateEntryMap l (eliminateEntryList b S)"

fun searchOneAux where
"searchOneAux [] = ([],[])"
| "searchOneAux ((a,b)#l) = (case searchOneAux l of (have, noHave) \<Rightarrow>
       (case b of [b'] \<Rightarrow> ((a,b')#have,noHave)
            | _ \<Rightarrow> (have,(a,b)#noHave)))"

function searchOne where
"searchOne l acc = (case searchZero l of (x,y) \<Rightarrow>
            if x = [] then (case searchOneAux y of (u,v) \<Rightarrow>
               if u = [] then Some (acc,v)
            else  (case eliminateEntryMap u v of None \<Rightarrow> None
            | Some v' \<Rightarrow> searchOne v' (u@acc))) else None)"
by pat_completeness auto

termination sorry

(* a function to find a way to match each pattern to a expression one by one and on two *)
function findBijection and findBijectionAux where
"findBijection l = (case searchOne l [] of None \<Rightarrow> None
        | Some (ones, mores) \<Rightarrow> (case mores of []
        \<Rightarrow> Some (ones,[]) | ((a,b)#al)
      \<Rightarrow> if al = [] then Some (ones,b) else findBijectionAux a b al))"
| "findBijectionAux a [] S = None"
| "findBijectionAux a ((b,c)#al) S =
     (case searchOne (eliminateEntryList b S) [] of None \<Rightarrow>
        findBijectionAux a al S | Some (ones, mores) \<Rightarrow> 
            if mores = [] then Some ((a,(b,c))#ones,[])
              else (case findBijection mores of None \<Rightarrow> None
         | Some (ones',remains) \<Rightarrow> Some ((a,(b,c))#ones@ones', remains)))"
by pat_completeness auto

termination sorry

fun mergePatMatchMap where
"mergePatMatchMap [] S subG = Some S"
| "mergePatMatchMap ((a,b)#l) S subG = (case updateMatchingMapMacro a b S subG
     of None \<Rightarrow> None | Some S' \<Rightarrow> mergePatMatchMap l S' subG)"

fun mergeMapWithOnes where
"mergeMapWithOnes [] acc subG = Some acc"
| "mergeMapWithOnes ((a,b,c)#l) acc subG =
    (case mergePatMatchMap c acc subG of None \<Rightarrow> None
       | Some acc' \<Rightarrow> mergeMapWithOnes l acc' subG)"

primrec searchAllNonTermsInSUSet where
"searchAllNonTermsInSUSet [] = []"
| "searchAllNonTermsInSUSet (a#l) = (case a of ItemS a' \<Rightarrow> searchAllNonTermsInSUSet l
               | _ \<Rightarrow> a#searchAllNonTermsInSUSet l)"

primrec searchAllNonTermsInSUMap where
"searchAllNonTermsInSUMap [] = []"
| "searchAllNonTermsInSUMap (a#l) = (case a of ItemM a' b \<Rightarrow> searchAllNonTermsInSUMap l
               | _ \<Rightarrow> a#searchAllNonTermsInSUMap l)"

primrec searchAllNonTermsInSUBag where
"searchAllNonTermsInSUBag [] = []"
| "searchAllNonTermsInSUBag (a#l) = (case a of ItemB a' b c \<Rightarrow> searchAllNonTermsInSUBag l
               | _ \<Rightarrow> a#searchAllNonTermsInSUBag l)"

(* a pattern matching algorithm that allowing non-linear commutativity equestional rewriting *)
function patternMacroingInSUKLabel
   and patternMacroingInSUKItem
   and patternMacroingInSUKList
   and patternMacroingInSUBigKWithLabel
   and patternMacroingInSUBigKWithBag
   and patternMacroingInSUK
   and patternMacroingInSUList
   and patternMacroingInSUSet
   and patternMacroingInSUSetAux
   and patternMacroingInSUMember
   and patternMacroingInSUMapMember
   and patternMacroingInSUMapAux
   and patternMacroingInSUBagMember
   and patternMacroingInSUBagAux
   and patternMacroingInSUMap
   and patternMacroingInSUBag
  where
"patternMacroingInSUKLabel (IRKLabel a) S acc subG =
    (case S of (SUKLabel b) \<Rightarrow>
     if a = b then Some acc else None
       | _ \<Rightarrow> None)"
| "patternMacroingInSUKLabel (IRIdKLabel a) S acc subG
           = (updateMatchingMapMacro a (KLabelSubs S) acc subG)"
| "patternMacroingInSUKItem (IRKItem l r ty) S acc subG = (case S of (SUKItem l' r' ty') \<Rightarrow>
 (if subsortList ty' ty subG then
       (case patternMacroingInSUKLabel l l' acc subG of None \<Rightarrow> None
         | Some acc' \<Rightarrow>
              (case patternMacroingInSUKList r r' acc' subG of None \<Rightarrow> None
          | Some acca \<Rightarrow> Some acca)) else None) | _ \<Rightarrow> None)"
| "patternMacroingInSUKItem (IRHOLE a) S acc subG = (case S of (SUHOLE a') \<Rightarrow>
     (if (subsortList a' a subG) then Some acc else None)
      | _ \<Rightarrow> None)"
| "patternMacroingInSUKItem (IRIdKItem a b) B acc subG = (case B of (SUIdKItem a' b')
         \<Rightarrow> (if subsortList b' b subG then
                updateMatchingMapMacro a (KItemSubs (SUIdKItem a' b')) acc subG
            else None)
       | (SUKItem l r ty) \<Rightarrow> (if subsortList ty b subG then
       updateMatchingMapMacro a (KItemSubs (SUKItem l r ty)) acc subG else None)
       | _ \<Rightarrow> None)"
| "patternMacroingInSUKList (KListPatNoVar l) S acc subG =
    (case l of [] \<Rightarrow> (case S of [] \<Rightarrow> Some acc | (sua#sul) \<Rightarrow> None)
        | la#ll \<Rightarrow> (case S of [] \<Rightarrow> None
          | (sua#sul) \<Rightarrow> (case sua of ItemKl x \<Rightarrow> 
          (case patternMacroingInSUBigKWithLabel la x acc subG of None \<Rightarrow> None
         | Some acc' \<Rightarrow> (case patternMacroingInSUKList (KListPatNoVar ll) sul acc' subG
           of None \<Rightarrow> None | Some acca \<Rightarrow> Some acca)) | _ \<Rightarrow> None)))"
| "patternMacroingInSUKList (KListPat l n r) S acc subG = (case l of [] \<Rightarrow>
     (case rev r of [] \<Rightarrow> (updateMatchingMapMacro n (KListSubs S) acc subG)
       | (ra#rl) \<Rightarrow> (case rev S of [] \<Rightarrow> None
       | (sua#sul) \<Rightarrow> (case sua of ItemKl x \<Rightarrow>
         (case patternMacroingInSUBigKWithLabel ra x acc subG of None \<Rightarrow> None
              | Some acc' \<Rightarrow>
         (case patternMacroingInSUKList (KListPat l n (rev rl)) (rev sul) acc' subG
           of None \<Rightarrow> None | Some acca \<Rightarrow> Some acca))
         | IdKl x \<Rightarrow> None)))
       | (la#ll) \<Rightarrow> (case S of [] \<Rightarrow> None
          | (sua#sul) \<Rightarrow> (case sua of ItemKl x \<Rightarrow>
         (case patternMacroingInSUBigKWithLabel la x acc subG of None \<Rightarrow> None
              | Some acc' \<Rightarrow>
         (case patternMacroingInSUKList (KListPat ll n r) sul acc' subG
           of None \<Rightarrow> None | Some acca \<Rightarrow> Some acca))
            | _ \<Rightarrow> None)))"
| "patternMacroingInSUK (KPat l n) S acc subG = (case l of [] \<Rightarrow>
           (case n of None \<Rightarrow> (case S of [] \<Rightarrow> Some acc
             | (sua#sul) \<Rightarrow> None)
               | Some v \<Rightarrow> updateMatchingMapMacro v (KSubs S) acc subG)
          | (la#ll) \<Rightarrow> (case S of [] \<Rightarrow> None
           | (sua#sul) \<Rightarrow> (case sua of ItemFactor x \<Rightarrow>
          (case patternMacroingInSUKItem la x acc subG of None \<Rightarrow> None
              | Some acc' \<Rightarrow> patternMacroingInSUK (KPat ll n) sul acc' subG)
          | IdFactor x \<Rightarrow> (case la of (IRIdKItem x' ty) \<Rightarrow> 
            if ty = [K] then (case updateMatchingMapMacro x' (KSubs [(IdFactor x)]) acc subG
                 of None \<Rightarrow> None | Some acc'
                 \<Rightarrow> patternMacroingInSUK (KPat ll n) sul acc' subG) else None
            | _ \<Rightarrow> None)
          | SUKKItem x y ty \<Rightarrow> (case la of (IRIdKItem x' ty') \<Rightarrow>
            if ty = [K] then (case updateMatchingMapMacro x' (KSubs [(SUKKItem x y ty)]) acc subG
            of None \<Rightarrow> None | Some acc'
                \<Rightarrow> patternMacroingInSUK (KPat ll n) sul acc' subG) else None
              |  _ \<Rightarrow> None))))"
| "patternMacroingInSUList (ListPatNoVar l) S acc subG = (case l of [] \<Rightarrow> 
       (case S of [] \<Rightarrow> Some acc | (sua#sul) \<Rightarrow> None)
      | (la#ll) \<Rightarrow> (case S of [] \<Rightarrow> None | (sua#sul) \<Rightarrow> 
         (case sua of ItemL x \<Rightarrow> (case patternMacroingInSUK la x acc subG of None \<Rightarrow> None
         | Some acc' \<Rightarrow> patternMacroingInSUList (ListPatNoVar ll) sul acc' subG)
      | _ \<Rightarrow> None)))"
| "patternMacroingInSUList (ListPat l n r) S acc subG = (case l of [] \<Rightarrow>
          (case rev r of [] \<Rightarrow>
           (updateMatchingMapMacro n (ListSubs S) acc subG)
            | (ra#rl) \<Rightarrow> (case rev S of [] \<Rightarrow> None
                | (sua#sul) \<Rightarrow> (case sua of ItemL x \<Rightarrow>
          (case patternMacroingInSUK ra x acc subG of None \<Rightarrow> None
              | Some acc' \<Rightarrow>
                    patternMacroingInSUList (ListPat l n (rev rl)) (rev sul) acc' subG)
              | _ \<Rightarrow> None)))
          | (la#ll) \<Rightarrow> (case S of [] \<Rightarrow> None
           | (sua#sul) \<Rightarrow> (case sua of ItemL x \<Rightarrow>
          (case patternMacroingInSUK la x acc subG of None \<Rightarrow> None
              | Some acc' \<Rightarrow> patternMacroingInSUList (ListPat ll n r) sul acc' subG)
          | _ \<Rightarrow> None)))"
| "patternMacroingInSUMember a [] acc subG = (a,[])"
| "patternMacroingInSUMember a (t#l) acc subG = (case t of (ItemS x) \<Rightarrow>
   (case patternMacroingInSUK a x acc subG of None
      \<Rightarrow> patternMacroingInSUMember a l acc subG
       | Some acc' \<Rightarrow> (case patternMacroingInSUMember a l acc subG
          of (u,v) \<Rightarrow> (u,(t,acc')#v)))
     | _ \<Rightarrow> patternMacroingInSUMember a l acc subG)"
| "patternMacroingInSUSetAux [] S acc subG = []"
| "patternMacroingInSUSetAux (a#l) S acc subG =
          (patternMacroingInSUMember a S acc subG)#(patternMacroingInSUSetAux l S acc subG)"
| "patternMacroingInSUSet (SetPat l n) S acc subG =
      (case patternMacroingInSUSetAux l S acc subG of S' \<Rightarrow>
       (case findBijection S' of None \<Rightarrow> None
      | Some (ones, remains) \<Rightarrow>
    (case searchAllNonTermsInSUSet S of rest \<Rightarrow>
       (case n of None \<Rightarrow> if rest = [] \<and> remains = [] then 
        mergeMapWithOnes ones acc subG else None
         | Some var \<Rightarrow>
   (case updateMatchingMapMacro var (SetSubs (rest@(keys remains))) acc subG of
        None \<Rightarrow> None | Some acc' \<Rightarrow> mergeMapWithOnes ones acc' subG)))))"
| "patternMacroingInSUMapMember a [] acc subG = (a,[])"
| "patternMacroingInSUMapMember a (t#l) acc subG = (case a of (b,c) \<Rightarrow>
      (case t of (ItemM x y) \<Rightarrow>
   (case patternMacroingInSUK b x acc subG of None
      \<Rightarrow> patternMacroingInSUMapMember a l acc subG
       | Some acc' \<Rightarrow> (case patternMacroingInSUK c y acc' subG of None \<Rightarrow>
        patternMacroingInSUMapMember a l acc subG | Some acca \<Rightarrow>
     (case patternMacroingInSUMapMember a l acc subG
          of (u,v) \<Rightarrow> (u,(t,acca)#v))))
     | _ \<Rightarrow> patternMacroingInSUMapMember a l acc subG))"
| "patternMacroingInSUMapAux [] S acc subG = []"
| "patternMacroingInSUMapAux (a#l) S acc subG =
          (patternMacroingInSUMapMember a S acc subG)#(patternMacroingInSUMapAux l S acc subG)"
| "patternMacroingInSUMap (MapPat l n) S acc subG =
   (case patternMacroingInSUMapAux l S acc subG of S' \<Rightarrow>
       (case findBijection S' of None \<Rightarrow> None
      | Some (ones, remains) \<Rightarrow>
    (case searchAllNonTermsInSUMap S of rest \<Rightarrow>
       (case n of None \<Rightarrow> if rest = [] \<and> remains = [] then 
        mergeMapWithOnes ones acc subG else None
         | Some var \<Rightarrow>
   (case updateMatchingMapMacro var (MapSubs (rest@(keys remains))) acc subG of
        None \<Rightarrow> None | Some acc' \<Rightarrow> mergeMapWithOnes ones acc' subG)))))"
| "patternMacroingInSUBagMember a [] acc subG = (a,[])"
| "patternMacroingInSUBagMember a (t#l) acc subG = (case a of (b,c,d) \<Rightarrow>
      (case t of (ItemB x y z) \<Rightarrow> if b = x then
   (case patternMacroingInSUBigKWithBag d z acc subG of None
      \<Rightarrow> patternMacroingInSUBagMember a l acc subG
       | Some acc' \<Rightarrow> (case patternMacroingInSUBagMember a l acc subG
          of (u,v) \<Rightarrow> (u,(t,acc')#v))) else patternMacroingInSUBagMember a l acc subG
     | _ \<Rightarrow> patternMacroingInSUBagMember a l acc subG))"
| "patternMacroingInSUBagAux [] S acc subG = []"
| "patternMacroingInSUBagAux (a#l) S acc subG =
          (patternMacroingInSUBagMember a S acc subG)#(patternMacroingInSUBagAux l S acc subG)"
| "patternMacroingInSUBag (BagPat l n) S acc subG =
    (case patternMacroingInSUBagAux l S acc subG of S' \<Rightarrow>
       (case findBijection S' of None \<Rightarrow> None
      | Some (ones, remains) \<Rightarrow>
    (case searchAllNonTermsInSUBag S of rest \<Rightarrow>
       (case n of None \<Rightarrow> if rest = [] \<and> remains = [] then 
        mergeMapWithOnes ones acc subG else None
         | Some var \<Rightarrow>
   (case updateMatchingMapMacro var (BagSubs (rest@(keys remains))) acc subG of
        None \<Rightarrow> None | Some acc' \<Rightarrow> mergeMapWithOnes ones acc' subG)))))"
| "patternMacroingInSUBigKWithBag (IRK t) S acc subG =
        (case S of (SUK r) \<Rightarrow> patternMacroingInSUK t r acc subG
           | _ \<Rightarrow> None)"
| "patternMacroingInSUBigKWithBag (IRBag t) S acc subG =
        (case S of (SUBag r) \<Rightarrow> patternMacroingInSUBag t r acc subG
            | _ \<Rightarrow> None)"
| "patternMacroingInSUBigKWithBag (IRList t) S acc subG =
        (case S of (SUList r) \<Rightarrow> patternMacroingInSUList t r acc subG
            | _ \<Rightarrow> None)"
| "patternMacroingInSUBigKWithBag (IRSet t) S acc subG =
        (case S of (SUSet r) \<Rightarrow> patternMacroingInSUSet t r acc subG
            | _ \<Rightarrow> None)"
| "patternMacroingInSUBigKWithBag (IRMap t) S acc subG =
        (case S of (SUMap r) \<Rightarrow> patternMacroingInSUMap t r acc subG
            | _ \<Rightarrow> None)"
| "patternMacroingInSUBigKWithLabel (IRBigBag t) S acc subG =
        (case S of (SUBigBag t') \<Rightarrow> patternMacroingInSUBigKWithBag t t' acc subG
          | _ \<Rightarrow> None)"
| "patternMacroingInSUBigKWithLabel (IRBigLabel t) S acc subG =
        (case S of (SUBigLabel t') \<Rightarrow> patternMacroingInSUKLabel t t' acc subG
          | _ \<Rightarrow> None)"
by pat_completeness auto

termination sorry

function substitutionInSUKLabel :: "('upVar, 'var, 'metaVar) suKLabel
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suKLabel option"
    and substitutionInSUKItem :: "('upVar, 'var, 'metaVar) suKItem
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suKItem option"
    and substitutionInSUKList :: "('upVar, 'var, 'metaVar) suKl list
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suKl list option"
    and substitutionInSUBigKWithBag :: "('upVar, 'var, 'metaVar) suBigKWithBag
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suBigKWithBag option"
    and substitutionInSUBigKWithLabel :: "('upVar, 'var, 'metaVar) suBigKWithLabel
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suBigKWithLabel option"
    and substitutionInSUK :: "('upVar, 'var, 'metaVar) suKFactor list
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suKFactor list option"
    and substitutionInSUList :: "('upVar, 'var, 'metaVar) suL list
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suL list option"
    and substitutionInSUSet :: "('upVar, 'var, 'metaVar) suS list
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suS list option"
    and substitutionInSUMap :: "('upVar, 'var, 'metaVar) suM list
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suM list option"
    and substitutionInSUBag :: "('upVar, 'var, 'metaVar) suB list
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suB list option" where
 "substitutionInSUKLabel (SUKLabel a) acc = Some (SUKLabel a)"
| "substitutionInSUKLabel (SUIdKLabel a) acc =
         (case getValueInMatchingMap a acc of Some (KLabelSubs x) \<Rightarrow> Some x
             | _ \<Rightarrow> None)"
| "substitutionInSUKLabel (SUKLabelFun a b) acc =
     (case (substitutionInSUKLabel a acc, substitutionInSUKList b acc)
       of (Some x, Some y) \<Rightarrow> Some (SUKLabelFun x y)
          | _ \<Rightarrow> None)"
| "substitutionInSUKItem (SUKItem l r ty) acc =
   (case (substitutionInSUKLabel l acc, substitutionInSUKList r acc) of (Some x, Some y)
      \<Rightarrow> Some (SUKItem x y ty) | _ \<Rightarrow> None)"
| "substitutionInSUKItem (SUHOLE a) acc = Some (SUHOLE a)"
| "substitutionInSUKItem (SUIdKItem a b) acc = (case getValueInMatchingMap a acc
     of Some (KItemSubs a') \<Rightarrow> Some a' | _ \<Rightarrow> None)"
| "substitutionInSUKList [] acc = Some []"
| "substitutionInSUKList (b#l) acc = (case b of IdKl x \<Rightarrow>
         (case getValueInMatchingMap x acc of Some (KListSubs x') \<Rightarrow>
           (case substitutionInSUKList l acc of None \<Rightarrow> None
              | Some l' \<Rightarrow> Some (x'@l'))
             | _ \<Rightarrow> None)
       | ItemKl x \<Rightarrow>
        (case substitutionInSUBigKWithLabel x acc of None \<Rightarrow> None
           | Some x' \<Rightarrow>
           (case substitutionInSUKList l acc of None \<Rightarrow> None
              | Some l' \<Rightarrow> Some ((ItemKl x')#l'))))"
| "substitutionInSUK [] acc = Some []"
| "substitutionInSUK (b#l) acc = (case b of IdFactor x \<Rightarrow>
      (case getValueInMatchingMap x acc of Some (KSubs x') \<Rightarrow>
           (case substitutionInSUK l acc of None \<Rightarrow> None
               | Some l' \<Rightarrow> Some (x'@l')) | _ \<Rightarrow> None)
    | ItemFactor x \<Rightarrow> (case substitutionInSUKItem x acc of None \<Rightarrow> None
           | Some x' \<Rightarrow> (case substitutionInSUK l acc of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((ItemFactor x')#l')))
    | SUKKItem x y ty \<Rightarrow> (case (substitutionInSUKLabel x acc,
       substitutionInSUKList y acc, substitutionInSUK l acc)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUKKItem x' y' ty)#l')
              | _ \<Rightarrow> None))"
| "substitutionInSUList [] acc = Some []"
| "substitutionInSUList (b#l) acc = (case b of IdL x \<Rightarrow>
      (case getValueInMatchingMap x acc of Some (ListSubs x') \<Rightarrow>
           (case substitutionInSUList l acc of None \<Rightarrow> None
               | Some l' \<Rightarrow> Some (x'@l')) | _ \<Rightarrow> None)
    | ItemL x \<Rightarrow> (case substitutionInSUK x acc of None \<Rightarrow> None
           | Some x' \<Rightarrow> (case substitutionInSUList l acc of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((ItemL x')#l')))
    | SUListKItem x y \<Rightarrow> (case (substitutionInSUKLabel x acc,
       substitutionInSUKList y acc, substitutionInSUList l acc)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUListKItem x' y')#l')
              | _ \<Rightarrow> None))"
| "substitutionInSUSet [] acc = Some []"
| "substitutionInSUSet (b#l) acc = (case b of IdS x \<Rightarrow>
      (case getValueInMatchingMap x acc of Some (SetSubs x') \<Rightarrow>
           (case substitutionInSUSet l acc of None \<Rightarrow> None
               | Some l' \<Rightarrow> Some (x'@l')) | _ \<Rightarrow> None)
    | ItemS x \<Rightarrow> (case substitutionInSUK x acc of None \<Rightarrow> None
           | Some x' \<Rightarrow> (case substitutionInSUSet l acc of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((ItemS x')#l')))
    | SUSetKItem x y \<Rightarrow> (case (substitutionInSUKLabel x acc,
       substitutionInSUKList y acc, substitutionInSUSet l acc)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUSetKItem x' y')#l')
              | _ \<Rightarrow> None))"
| "substitutionInSUMap [] acc = Some []"
| "substitutionInSUMap (b#l) acc = (case b of IdM x \<Rightarrow>
      (case getValueInMatchingMap x acc of Some (MapSubs x') \<Rightarrow>
           (case substitutionInSUMap l acc of None \<Rightarrow> None
               | Some l' \<Rightarrow> Some (x'@l')) | _ \<Rightarrow> None)
    | ItemM x y \<Rightarrow> (case (substitutionInSUK x acc, substitutionInSUK y acc,
         substitutionInSUMap l acc) of (Some x', Some y', Some l')
         \<Rightarrow> Some ((ItemM x' y')#l') | _ \<Rightarrow> None)
    | SUMapKItem x y \<Rightarrow> (case (substitutionInSUKLabel x acc,
       substitutionInSUKList y acc, substitutionInSUMap l acc)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUMapKItem x' y')#l')
              | _ \<Rightarrow> None))"
| "substitutionInSUBigKWithBag (SUK a) acc = (case substitutionInSUK a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUK a'))"
| "substitutionInSUBigKWithBag (SUList a) acc = (case substitutionInSUList a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUList a'))"
| "substitutionInSUBigKWithBag (SUSet a) acc = (case substitutionInSUSet a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUSet a'))"
| "substitutionInSUBigKWithBag (SUMap a) acc = (case substitutionInSUMap a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUMap a'))"
| "substitutionInSUBigKWithBag (SUBag a) acc = (case substitutionInSUBag a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUBag a'))"
| "substitutionInSUBigKWithLabel (SUBigBag a) acc = (case substitutionInSUBigKWithBag a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "substitutionInSUBigKWithLabel (SUBigLabel a) acc = (case substitutionInSUKLabel a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUBigLabel a'))"
| "substitutionInSUBag [] acc = Some []"
| "substitutionInSUBag (b#l) acc = (case b of IdB x \<Rightarrow>
         (case getValueInMatchingMap x acc of Some (BagSubs x') \<Rightarrow>
           (case substitutionInSUBag l acc of None \<Rightarrow> None
              | Some l' \<Rightarrow> Some (x'@l'))
             | _ \<Rightarrow> None)
       | ItemB x y z \<Rightarrow>
        (case substitutionInSUBigKWithBag z acc of None \<Rightarrow> None
           | Some z' \<Rightarrow>
           (case substitutionInSUBag l acc of None \<Rightarrow> None
              | Some l' \<Rightarrow> Some ((ItemB x y z')#l'))))"
by pat_completeness auto

termination sorry

fun substitutionInSubsFactor where
"substitutionInSubsFactor (KLabelSubs a) acc = (case substitutionInSUKLabel a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (KLabelSubs a'))"
| "substitutionInSubsFactor (KItemSubs a) acc = (case substitutionInSUKItem a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (KItemSubs a'))"
| "substitutionInSubsFactor (KListSubs a) acc = (case substitutionInSUKList a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (KListSubs a'))"
| "substitutionInSubsFactor (KSubs a) acc = (case substitutionInSUK a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (KSubs a'))"
| "substitutionInSubsFactor (ListSubs a) acc = (case substitutionInSUList a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (ListSubs a'))"
| "substitutionInSubsFactor (SetSubs a) acc = (case substitutionInSUSet a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (SetSubs a'))"
| "substitutionInSubsFactor (MapSubs a) acc = (case substitutionInSUMap a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (MapSubs a'))"
| "substitutionInSubsFactor (BagSubs a) acc = (case substitutionInSUBag a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (BagSubs a'))"

(* dealing with macro rules *)
function applyMacroRuleInSUKLabel
    and applyMacroRuleInSUKItem
    and applyMacroRuleInSUKList
    and applyMacroRuleInSUBigKWithBag
    and applyMacroRuleInSUBigKWithLabel
    and applyMacroRuleInSUK
    and applyMacroRuleInSUList
    and applyMacroRuleInSUSet
    and applyMacroRuleInSUMap
    and applyMacroRuleInSUBag where
 "applyMacroRuleInSUKLabel s kl t (SUKLabel a) subG = Some (SUKLabel a)"
| "applyMacroRuleInSUKLabel s kl t (SUIdKLabel a) subG = Some (SUIdKLabel a)"
| "applyMacroRuleInSUKLabel s kl t (SUKLabelFun a b) subG =
     (case (applyMacroRuleInSUKLabel s kl t a subG, applyMacroRuleInSUKList s kl t b subG)
       of (Some a', Some b') \<Rightarrow> Some (SUKLabelFun a' b') | _ \<Rightarrow> None)"
| "applyMacroRuleInSUKItem s kl t (SUKItem l r ty) subG =
  (case (applyMacroRuleInSUKLabel s kl t l subG, applyMacroRuleInSUKList s kl t r subG)
       of (Some l', Some r') \<Rightarrow>
     (case getSUKLabelMeaning l' of None \<Rightarrow> Some [ItemFactor (SUKItem l' r' ty)]
         | Some ss \<Rightarrow> if s = ss then
    (case patternMacroingInSUKList kl r' [] subG of None \<Rightarrow>
          Some [ItemFactor (SUKItem l' r' ty)]
      | Some acc \<Rightarrow> (case substitutionInSUK t acc of None \<Rightarrow>
          Some [ItemFactor (SUKItem l' r' ty)]
        | Some t' \<Rightarrow> Some t'))
     else Some [ItemFactor (SUKItem l' r' ty)]))"
| "applyMacroRuleInSUKItem s kl t (SUHOLE a) subG = Some [ItemFactor (SUHOLE a)]"
| "applyMacroRuleInSUKItem s kl t (SUIdKItem a b) subG = Some [ItemFactor (SUIdKItem a b)]"
| "applyMacroRuleInSUKList s kl t [] subG = Some []"
| "applyMacroRuleInSUKList s kl t (b#l) subG = (case b of IdKl x \<Rightarrow>
         (case applyMacroRuleInSUKList s kl t l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some (b#l'))
    | ItemKl x \<Rightarrow>
         (case (applyMacroRuleInSUBigKWithLabel s kl t x subG, applyMacroRuleInSUKList s kl t l subG)
          of (Some x', Some l') \<Rightarrow> Some ((ItemKl x')#l') | _ \<Rightarrow> None))"
| "applyMacroRuleInSUK s kl t [] subG = Some []"
| "applyMacroRuleInSUK s kl t  (b#l) subG = (case b of IdFactor x \<Rightarrow>
         (case applyMacroRuleInSUK s kl t l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some (b#l'))
    | ItemFactor x \<Rightarrow>
       (case (applyMacroRuleInSUKItem s kl t x subG, applyMacroRuleInSUK s kl t l subG)
          of (Some x', Some l') \<Rightarrow> Some (x'@l') | _ \<Rightarrow> None)
    | SUKKItem x y ty \<Rightarrow> (case (applyMacroRuleInSUKLabel s kl t x subG,
       applyMacroRuleInSUKList s kl t y subG, applyMacroRuleInSUK s kl t l subG)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUKKItem x' y' ty)#l')
              | _ \<Rightarrow> None))"
| "applyMacroRuleInSUList s kl t [] subG = Some []"
| "applyMacroRuleInSUList s kl t (b#l) subG = (case b of IdL x \<Rightarrow>
         (case applyMacroRuleInSUList s kl t l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some (b#l'))
    | ItemL x \<Rightarrow>
       (case (applyMacroRuleInSUK s kl t x subG, applyMacroRuleInSUList s kl t l subG)
          of (Some x', Some l') \<Rightarrow> Some ((ItemL x')#l') | _ \<Rightarrow> None)
    | SUListKItem x y \<Rightarrow> (case (applyMacroRuleInSUKLabel s kl t x subG,
       applyMacroRuleInSUKList s kl t y subG, applyMacroRuleInSUList s kl t l subG)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUListKItem x' y')#l')
              | _ \<Rightarrow> None))"
| "applyMacroRuleInSUSet s kl t [] subG = Some []"
| "applyMacroRuleInSUSet s kl t (b#l) subG = (case b of IdS x \<Rightarrow>
         (case applyMacroRuleInSUSet s kl t l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some (b#l'))
    | ItemS x \<Rightarrow>
       (case (applyMacroRuleInSUK s kl t x subG, applyMacroRuleInSUSet s kl t l subG)
          of (Some x', Some l') \<Rightarrow> Some ((ItemS x')#l') | _ \<Rightarrow> None)
    | SUSetKItem x y \<Rightarrow> (case (applyMacroRuleInSUKLabel s kl t x subG,
       applyMacroRuleInSUKList s kl t y subG, applyMacroRuleInSUSet s kl t l subG)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUSetKItem x' y')#l')
              | _ \<Rightarrow> None))"
| "applyMacroRuleInSUMap s kl t [] subG = Some []"
| "applyMacroRuleInSUMap s kl t (b#l) subG = (case b of IdM x \<Rightarrow>
         (case applyMacroRuleInSUMap s kl t l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some (b#l'))
    | ItemM x y \<Rightarrow>
       (case (applyMacroRuleInSUK s kl t x subG, applyMacroRuleInSUK s kl t x subG, 
             applyMacroRuleInSUMap s kl t l subG)
          of (Some x', Some y', Some l')
            \<Rightarrow> Some ((ItemM x' y')#l') | _ \<Rightarrow> None)
    | SUMapKItem x y \<Rightarrow> (case (applyMacroRuleInSUKLabel s kl t x subG,
       applyMacroRuleInSUKList s kl t y subG, applyMacroRuleInSUMap s kl t l subG)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUMapKItem x' y')#l')
              | _ \<Rightarrow> None))"
| "applyMacroRuleInSUBigKWithBag s kl t (SUK a) subG = (case applyMacroRuleInSUK  s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUK a'))"
| "applyMacroRuleInSUBigKWithBag s kl t (SUList a) subG = (case applyMacroRuleInSUList s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUList a'))"
| "applyMacroRuleInSUBigKWithBag s kl t (SUSet a) subG = (case applyMacroRuleInSUSet s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUSet a'))"
| "applyMacroRuleInSUBigKWithBag s kl t (SUMap a) subG = (case applyMacroRuleInSUMap s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUMap a'))"
| "applyMacroRuleInSUBigKWithBag s kl t (SUBag a) subG = (case applyMacroRuleInSUBag s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUBag a'))"
| "applyMacroRuleInSUBigKWithLabel s kl t (SUBigBag a) subG =
     (case applyMacroRuleInSUBigKWithBag s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "applyMacroRuleInSUBigKWithLabel s kl t (SUBigLabel a) subG =
     (case applyMacroRuleInSUKLabel s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUBigLabel a'))"
| "applyMacroRuleInSUBag s kl t [] subG = Some []"
| "applyMacroRuleInSUBag s kl t (b#l) subG =  (case b of IdB x \<Rightarrow>
         (case applyMacroRuleInSUBag s kl t l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some (b#l'))
    | ItemB x y z \<Rightarrow>
         (case (applyMacroRuleInSUBigKWithBag s kl t z subG, applyMacroRuleInSUBag s kl t l subG)
          of (Some z', Some l') \<Rightarrow> Some ((ItemB x y z')#l') | _ \<Rightarrow> None))"
by pat_completeness auto

termination sorry

primrec applyMacroRuleInSubsFactor where
"applyMacroRuleInSubsFactor s kl t (KLabelSubs a) subG =
       (case applyMacroRuleInSUKLabel s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (KLabelSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (KItemSubs a) subG =
       (case applyMacroRuleInSUKItem s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (KSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (KListSubs a) subG =
       (case applyMacroRuleInSUKList s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (KListSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (KSubs a) subG =
       (case applyMacroRuleInSUK s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (KSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (ListSubs a) subG =
       (case applyMacroRuleInSUList s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (ListSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (SetSubs a) subG =
       (case applyMacroRuleInSUSet s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (SetSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (MapSubs a) subG =
       (case applyMacroRuleInSUMap s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (MapSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (BagSubs a) subG =
       (case applyMacroRuleInSUBag s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (BagSubs a'))"

primrec applyMacroRulesInFun ::
    "'a label
      \<Rightarrow> ('a, 'b, 'c) irKList
         \<Rightarrow> ('a, 'b, 'c) suKFactor list
            \<Rightarrow> (('a, 'b, 'c) pat \<times> ('a, 'b, 'c) subsFactor \<times> ('a, 'b, 'c) suKItem) list
               \<Rightarrow> ('a kSyntax.sort list \<times> 'a kSyntax.sort list list
          \<times> 'a label KItemSyntax \<times> 'e \<times> bool) list
                  \<Rightarrow> ('a kSyntax.sort \<times> 'a kSyntax.sort list) list
     \<Rightarrow> (('a, 'b, 'c) pat \<times> ('a, 'b, 'c) subsFactor \<times> ('a, 'b, 'c) suKItem) list option"where
"applyMacroRulesInFun s kl t [] database subG = Some []"
| "applyMacroRulesInFun s kl t (b#l) database subG = (case b of (u,v,w) \<Rightarrow>
       (case (applyMacroRuleInSubsFactor s kl t (irToSUInPat u database) subG,
             applyMacroRuleInSubsFactor s kl t v subG,
                       applyMacroRuleInSUKItem s kl t w subG)
      of (Some u', Some v', Some [ItemFactor w']) \<Rightarrow>
       (case suToIRInSubsFactor u' database of None \<Rightarrow> None
           | Some ua \<Rightarrow> (case applyMacroRulesInFun s kl t l database subG of
              None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((ua,v',w')#l'))) | _ \<Rightarrow> None))"

fun applyMacroRules :: "'a label
     \<Rightarrow> ('a, 'b, 'c) irKList
        \<Rightarrow> ('a, 'b, 'c) suKFactor list
           \<Rightarrow> ('a, 'b, 'c) rulePat list
              \<Rightarrow> ('a kSyntax.sort list \<times> 'a kSyntax.sort list list
             \<times> 'a label KItemSyntax \<times> 'e \<times> bool) list
                 \<Rightarrow> ('a kSyntax.sort \<times> 'a kSyntax.sort list) list
           \<Rightarrow> ('a, 'b, 'c) rulePat list option" where
"applyMacroRules s kl t [] database subG = Some []"
| "applyMacroRules s kl t ((FunPat ss L ow)#l) database subG =
         (case applyMacroRulesInFun s kl t L database subG of None \<Rightarrow> None
           | Some L' \<Rightarrow> (case ow of None \<Rightarrow>
            (case applyMacroRules s kl t l database subG of None \<Rightarrow> None
                | Some l' \<Rightarrow> Some ((FunPat ss L' ow)#l'))
               | Some q \<Rightarrow>
           (case applyMacroRulesInFun s kl t [q] database subG of None \<Rightarrow> None
                 | Some [q'] \<Rightarrow>
             (case applyMacroRules s kl t l database subG of None \<Rightarrow> None
                | Some l' \<Rightarrow> Some ((FunPat ss L' (Some q'))#l')))))"
| "applyMacroRules s kl t ((MacroPat ss kl' t')#l) database subG =
      (case getSort ss database of None \<Rightarrow> None
          | Some ty \<Rightarrow> 
      (case (applyMacroRuleInSUKItem s kl t (SUKItem (SUKLabel ss) (irToSUInKList kl') ty) subG,
              applyMacroRuleInSUK s kl t t' subG) of (Some mla, Some ta) \<Rightarrow>
    (case suToIRInK mla database of None \<Rightarrow> None
     | Some (NormalPat (KMatching (KPat [IRKItem (IRKLabel ss') kla ty'] None))) \<Rightarrow>
         (case applyMacroRules s kl t l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((MacroPat ss' kla ta)#l')) | _ \<Rightarrow> None)))"
| "applyMacroRules s kl t ((AnywherePat ss u v w)#l) database subG =
    (case (applyMacroRuleInSUKList s kl t (irToSUInKList u) subG, applyMacroRuleInSUK s kl t v subG,
     applyMacroRuleInSUKItem s kl t w subG) of (Some u', Some v', Some [ItemFactor w']) \<Rightarrow>
    (case suToIRInKList u' database of Some ua
          \<Rightarrow> (case applyMacroRules s kl t l database subG of None \<Rightarrow> None
          | Some l' \<Rightarrow> Some ((AnywherePat ss ua v' w')#l'))
            | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "applyMacroRules s kl t ((KRulePat u v w tb)#l) database subG =
    (case (applyMacroRuleInSUK s kl t (irToSUInK u) subG, applyMacroRuleInSUK s kl t v subG,
     applyMacroRuleInSUKItem s kl t w subG) of (Some u', Some v', Some [ItemFactor w']) \<Rightarrow>
    (case suToIRInK u' database of Some (NormalPat (KMatching ua)) \<Rightarrow>
           (case applyMacroRules s kl t l database subG of None \<Rightarrow> None
          | Some l' \<Rightarrow> Some ((KRulePat ua v' w' tb)#l'))
            | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "applyMacroRules s kl t ((BagRulePat u v w tb)#l) database subG =
    (case (applyMacroRuleInSUBag s kl t (irToSUInBag u) subG, applyMacroRuleInSUBag s kl t v subG,
     applyMacroRuleInSUKItem s kl t w subG) of (Some u', Some v', Some [ItemFactor w']) \<Rightarrow>
    (case suToIRInBag u' database of Some ua \<Rightarrow>
           (case applyMacroRules s kl t l database subG of None \<Rightarrow> None
          | Some l' \<Rightarrow> Some ((BagRulePat ua v' w' tb)#l'))
            | _ \<Rightarrow> None) | _ \<Rightarrow> None)"

fun applyAllMacroRulesInList where
"applyAllMacroRulesInList [] L confi database subG = (case L of None \<Rightarrow> None
       | Some L' \<Rightarrow> Some (L', confi))"
| "applyAllMacroRulesInList (b#l) L confi database subG =
      (case (b,L) of (Some (x,y,z), Some L') \<Rightarrow>
    (case applyMacroRuleInSUBag x y z confi subG of None \<Rightarrow> None
          | Some confi' \<Rightarrow>
        applyAllMacroRulesInList (List.map (\<lambda> t . (case t of None \<Rightarrow> None
            | Some (a,b,c) \<Rightarrow>
               (case applyMacroRules x y z [MacroPat a b c] database subG of 
           Some [MacroPat a' b' c'] \<Rightarrow> Some (a',b',c') | _ \<Rightarrow> None))) l)
        (applyMacroRules x y z L' database subG) confi' database subG) | _ \<Rightarrow> None)"

fun adjustKSortsInIRKItem
  and adjustKSortsInIRBigKWithBag
  and adjustKSortsInIRBigKWithLabel
  and adjustKSortsInIRK
  and adjustKSortsInIRKList
  and adjustKSortsInIRList
  and adjustKSortsInIRSet
  and adjustKSortsInIRMap
  and adjustKSortsInIRBag where
"adjustKSortsInIRKItem (IRKItem a b ty ) = (IRKItem a (adjustKSortsInIRKList b) ty)"
| "adjustKSortsInIRKItem (IRIdKItem a ty) = IRIdKItem a ty"
| "adjustKSortsInIRKItem (IRHOLE ty) = (IRHOLE ty)"
| "adjustKSortsInIRBigKWithBag (IRK a) = IRK (adjustKSortsInIRK a)"
| "adjustKSortsInIRBigKWithBag (IRList a) = IRList (adjustKSortsInIRList a)"
| "adjustKSortsInIRBigKWithBag (IRSet a) = IRSet (adjustKSortsInIRSet a)"
| "adjustKSortsInIRBigKWithBag (IRMap a) = IRMap (adjustKSortsInIRMap a)"
| "adjustKSortsInIRBigKWithBag (IRBag a) = IRBag (adjustKSortsInIRBag a)"
| "adjustKSortsInIRBigKWithLabel (IRBigBag a) = IRBigBag (adjustKSortsInIRBigKWithBag a)"
| "adjustKSortsInIRBigKWithLabel (IRBigLabel a) = (IRBigLabel a)"
| "adjustKSortsInIRK (KPat [] b) = (KPat [] b)"
| "adjustKSortsInIRK (KPat (x#l) b) = (case adjustKSortsInIRK (KPat l b) of 
          (KPat l' b') \<Rightarrow> (case x of (IRIdKItem a [K]) \<Rightarrow> 
            KPat ((IRIdKItem a [KItem])#l') b' | _ \<Rightarrow> (KPat (x#l') b')))"
| "adjustKSortsInIRKList (KListPatNoVar l) = (case l of [] \<Rightarrow> KListPatNoVar []
        | la#ll \<Rightarrow> (case adjustKSortsInIRKList (KListPatNoVar ll) of (KListPatNoVar ll') 
          \<Rightarrow> (KListPatNoVar ((adjustKSortsInIRBigKWithLabel la)#ll'))
           | _ \<Rightarrow> KListPatNoVar l))"
| "adjustKSortsInIRKList (KListPat [] y []) = (KListPat [] y [])"
|  "adjustKSortsInIRKList (KListPat [] y (x#l)) = 
     (case adjustKSortsInIRKList (KListPat [] y l) of (KListPat [] y' l')
        \<Rightarrow>  (KListPat [] y' ((adjustKSortsInIRBigKWithLabel x)#l'))
       | _ \<Rightarrow> (KListPat [] y (x#l)))"
|  "adjustKSortsInIRKList (KListPat (x#l) y S) = 
     (case adjustKSortsInIRKList (KListPat l y S) of (KListPat l' y' S')
        \<Rightarrow>  (KListPat ((adjustKSortsInIRBigKWithLabel x)#l') y' S')
       | _ \<Rightarrow> (KListPat (x#l) y S))"
| "adjustKSortsInIRList (ListPatNoVar l) = (case l of [] \<Rightarrow> ListPatNoVar []
        | la#ll \<Rightarrow> (case adjustKSortsInIRList (ListPatNoVar ll) of (ListPatNoVar ll') 
          \<Rightarrow> (ListPatNoVar ((adjustKSortsInIRK la)#ll'))
           | _ \<Rightarrow> ListPatNoVar l))"
| "adjustKSortsInIRList (ListPat [] y []) = (ListPat [] y [])"
|  "adjustKSortsInIRList (ListPat [] y (x#l)) = 
     (case adjustKSortsInIRList (ListPat [] y l) of (ListPat [] y' l')
        \<Rightarrow>  (ListPat [] y' ((adjustKSortsInIRK x)#l'))
       | _ \<Rightarrow> (ListPat [] y (x#l)))"
| "adjustKSortsInIRList (ListPat (x#l) y S) = 
     (case adjustKSortsInIRList (ListPat l y S) of (ListPat l' y' S')
        \<Rightarrow>  (ListPat ((adjustKSortsInIRK x)#l') y' S')
       | _ \<Rightarrow> (ListPat (x#l) y S))"
| "adjustKSortsInIRSet (SetPat [] b) = (SetPat [] b)"
| "adjustKSortsInIRSet (SetPat (x#l) b) = (case adjustKSortsInIRSet (SetPat l b) of 
          (SetPat l' b') \<Rightarrow> SetPat ((adjustKSortsInIRK x)#l') b')"
| "adjustKSortsInIRMap (MapPat [] b) = (MapPat [] b)"
| "adjustKSortsInIRMap (MapPat ((x,y)#l) b) = (case adjustKSortsInIRMap (MapPat l b) of 
          (MapPat l' b') \<Rightarrow> MapPat ((adjustKSortsInIRK x,adjustKSortsInIRK y)#l') b')"
| "adjustKSortsInIRBag (BagPat [] b) = (BagPat [] b)"
| "adjustKSortsInIRBag (BagPat ((x,y,z)#l) b) = (case adjustKSortsInIRBag (BagPat l b) of 
          (BagPat l' b') \<Rightarrow> BagPat ((x,y,(adjustKSortsInIRBigKWithBag z))#l') b')"

primrec adjustKSortsInMatchFactor where
"adjustKSortsInMatchFactor (KLabelMatching l) = (KLabelMatching l)"
| "adjustKSortsInMatchFactor (KItemMatching l) = (KItemMatching (adjustKSortsInIRKItem l))"
| "adjustKSortsInMatchFactor (KListMatching l) = (KListMatching (adjustKSortsInIRKList l))"
| "adjustKSortsInMatchFactor (KMatching l) = (KMatching (adjustKSortsInIRK l))"
| "adjustKSortsInMatchFactor (ListMatching l) = (ListMatching (adjustKSortsInIRList l))"
| "adjustKSortsInMatchFactor (SetMatching l) = (SetMatching (adjustKSortsInIRSet l))"
| "adjustKSortsInMatchFactor (MapMatching l) = (MapMatching (adjustKSortsInIRMap l))"
| "adjustKSortsInMatchFactor (BagMatching l) = (BagMatching (adjustKSortsInIRBag l))"

primrec adjustKSortsInPat where
"adjustKSortsInPat (KLabelFunPat x y) = (KLabelFunPat x (adjustKSortsInIRKList y))"
| "adjustKSortsInPat (KFunPat x y) = (KFunPat x (adjustKSortsInIRKList y))"
| "adjustKSortsInPat (KItemFunPat x y) = (KItemFunPat x (adjustKSortsInIRKList y))"
| "adjustKSortsInPat (ListFunPat x y) = (ListFunPat x (adjustKSortsInIRKList y))"
| "adjustKSortsInPat (SetFunPat x y) = (SetFunPat x (adjustKSortsInIRKList y))"
| "adjustKSortsInPat (MapFunPat x y) = (MapFunPat x (adjustKSortsInIRKList y))"
| "adjustKSortsInPat (NormalPat x) = (NormalPat (adjustKSortsInMatchFactor x))"

fun adjustKSortsInFunPatList where
"adjustKSortsInFunPatList [] = []"
| "adjustKSortsInFunPatList ((x,y,z)#l) = (adjustKSortsInPat x,y,z)#(adjustKSortsInFunPatList l)"

fun adjustKSortsInRulePats where
"adjustKSortsInRulePats [] = []"
| "adjustKSortsInRulePats ((FunPat x y z)#l) = 
   (case z of None \<Rightarrow> (FunPat x (adjustKSortsInFunPatList y) None)#(adjustKSortsInRulePats l)
    | Some (a,b,c) \<Rightarrow> (FunPat x (adjustKSortsInFunPatList y)
                          (Some (adjustKSortsInPat a,b,c)))#adjustKSortsInRulePats l)"
| "adjustKSortsInRulePats ((MacroPat x y z)#l) =
                (MacroPat x (adjustKSortsInIRKList y) z)#(adjustKSortsInRulePats l)"
| "adjustKSortsInRulePats ((AnywherePat a b c d)#l) =
                (AnywherePat a (adjustKSortsInIRKList b) c d)#(adjustKSortsInRulePats l)"
| "adjustKSortsInRulePats ((KRulePat a b c d)#l) =
                (KRulePat (adjustKSortsInIRK a) b c d)#(adjustKSortsInRulePats l)"
| "adjustKSortsInRulePats ((BagRulePat a b c d)#l) =
                (BagRulePat (adjustKSortsInIRBag a) b c d)#(adjustKSortsInRulePats l)"

(*
definition applyAllMacroRulesCheck where
"applyAllMacroRulesCheck stl Theory database subG =
    (case typeCheckRules Theory database subG of None \<Rightarrow> None
          | Some l \<Rightarrow> (case realConfigurationTest stl Theory database subG 
      of None \<Rightarrow> None
         | Some bl \<Rightarrow> (case divideMacroRules l subG of Some (x,y)
       \<Rightarrow> (case applyAllMacroRulesInList x (Some y) bl database subG of
         None \<Rightarrow> None | Some (l', confi) \<Rightarrow> if wellFormRules l'
        then (case inferTypesInRules l' Theory database subG of None \<Rightarrow> None
             | Some la \<Rightarrow> (case adjustKSortsInRulePats la of la' \<Rightarrow>
      (case inferTypesInRules la' Theory database subG of None \<Rightarrow> None
          | Some lb \<Rightarrow> (case typeCheckProgramState confi database subG of None \<Rightarrow> None
      | Some confi' \<Rightarrow> Some (lb, confi'))))) else None))))"
*)

(* dealing with function rules *)
function hasFunLabelInSUKLabel
    and hasFunLabelInSUKItem
    and hasFunLabelInSUKList
    and hasFunLabelInSUBigKWithBag
    and hasFunLabelInSUBigKWithLabel
    and hasFunLabelInSUK
    and hasFunLabelInSUList
    and hasFunLabelInSUSet
    and hasFunLabelInSUMap
    and hasFunLabelInSUBag where
"hasFunLabelInSUKLabel (SUKLabel a) database = False"
| "hasFunLabelInSUKLabel (SUIdKLabel a) database = False"
| "hasFunLabelInSUKLabel (SUKLabelFun x y) database = (hasFunLabelInSUKLabel x database \<or>
         hasFunLabelInSUKList y database \<or>
          (case getSUKLabelMeaning x of None \<Rightarrow> False
            | Some s \<Rightarrow> if isFunctionItem s database then True else False))"
| "hasFunLabelInSUKItem (SUKItem x y z) database = (hasFunLabelInSUKLabel x database \<or>
         hasFunLabelInSUKList y database \<or>
          (case getSUKLabelMeaning x of None \<Rightarrow> False
            | Some s \<Rightarrow> if isFunctionItem s database then True else False))"
| "hasFunLabelInSUKItem (SUIdKItem x y) database = False"
| "hasFunLabelInSUKItem (SUHOLE x) database = False"
| "hasFunLabelInSUKList [] database = False"
| "hasFunLabelInSUKList (a#l) database = (case a of ItemKl x \<Rightarrow> 
       hasFunLabelInSUBigKWithLabel x database \<or> hasFunLabelInSUKList l database
       | _ \<Rightarrow> hasFunLabelInSUKList l database)"
| "hasFunLabelInSUBigKWithBag (SUK a) database = hasFunLabelInSUK a database"
| "hasFunLabelInSUBigKWithBag (SUList a) database = hasFunLabelInSUList a database"
| "hasFunLabelInSUBigKWithBag (SUSet a) database = hasFunLabelInSUSet a database"
| "hasFunLabelInSUBigKWithBag (SUMap a) database = hasFunLabelInSUMap a database"
| "hasFunLabelInSUBigKWithBag (SUBag a) database = hasFunLabelInSUBag a database"
| "hasFunLabelInSUBigKWithLabel (SUBigBag a) database = hasFunLabelInSUBigKWithBag a database"
| "hasFunLabelInSUBigKWithLabel (SUBigLabel a) database = hasFunLabelInSUKLabel a database"
| "hasFunLabelInSUK [] database = False"
| "hasFunLabelInSUK (a#l) database = (case a of ItemFactor x \<Rightarrow> 
       hasFunLabelInSUKItem x database \<or> hasFunLabelInSUK l database
       | SUKKItem x y z \<Rightarrow> (hasFunLabelInSUKLabel x database \<or>
         hasFunLabelInSUKList y database \<or> hasFunLabelInSUK l database \<or>
          (case getSUKLabelMeaning x of None \<Rightarrow> False
            | Some s \<Rightarrow> if isFunctionItem s database then True else False))
      | _ \<Rightarrow> hasFunLabelInSUK l database)"
| "hasFunLabelInSUList [] database = False"
| "hasFunLabelInSUList (a#l) database = (case a of ItemL x \<Rightarrow> 
       hasFunLabelInSUK x database \<or> hasFunLabelInSUList l database
       | SUListKItem x y \<Rightarrow> (hasFunLabelInSUKLabel x database \<or>
         hasFunLabelInSUKList y database \<or> hasFunLabelInSUList l database \<or>
          (case getSUKLabelMeaning x of None \<Rightarrow> False
            | Some s \<Rightarrow> if isFunctionItem s database then True else False))
      | _ \<Rightarrow> hasFunLabelInSUList l database)"
| "hasFunLabelInSUSet [] database = False"
| "hasFunLabelInSUSet (a#l) database = (case a of ItemS x \<Rightarrow> 
       hasFunLabelInSUK x database \<or> hasFunLabelInSUSet l database
       | SUSetKItem x y \<Rightarrow> (hasFunLabelInSUKLabel x database \<or>
         hasFunLabelInSUKList y database \<or> hasFunLabelInSUSet l database \<or>
          (case getSUKLabelMeaning x of None \<Rightarrow> False
            | Some s \<Rightarrow> if isFunctionItem s database then True else False))
      | _ \<Rightarrow> hasFunLabelInSUSet l database)"
| "hasFunLabelInSUMap [] database = False"
| "hasFunLabelInSUMap (a#l) database = (case a of ItemM x y \<Rightarrow> 
       hasFunLabelInSUK x database \<or> hasFunLabelInSUK y database \<or>
     hasFunLabelInSUMap l database
       | SUMapKItem x y \<Rightarrow> (hasFunLabelInSUKLabel x database \<or>
         hasFunLabelInSUKList y database \<or> hasFunLabelInSUMap l database \<or>
          (case getSUKLabelMeaning x of None \<Rightarrow> False
            | Some s \<Rightarrow> if isFunctionItem s database then True else False))
      | _ \<Rightarrow> hasFunLabelInSUMap l database)"
| "hasFunLabelInSUBag [] database = False"
| "hasFunLabelInSUBag (a#l) database = (case a of ItemB x y z \<Rightarrow> 
       hasFunLabelInSUBigKWithBag z database \<or> hasFunLabelInSUBag l database
       | _ \<Rightarrow> hasFunLabelInSUBag l database)"
by pat_completeness auto

termination sorry

function localteFunTermInSUKLabel
    and localteFunTermInSUKItem
    and localteFunTermInSUKList
    and localteFunTermInSUBigKWithBag
    and localteFunTermInSUBigKWithLabel
    and localteFunTermInSUK
    and localteFunTermInSUList
    and localteFunTermInSUSet
    and localteFunTermInSUMap
    and localteFunTermInSUBag where
"localteFunTermInSUKLabel (SUKLabel a) database = None"
| "localteFunTermInSUKLabel (SUIdKLabel a) database = None"
| "localteFunTermInSUKLabel (SUKLabelFun x y) database =
    (case localteFunTermInSUKLabel x database of None \<Rightarrow> 
      (case localteFunTermInSUKList y database of None \<Rightarrow> 
    (case getSUKLabelMeaning x of None \<Rightarrow> None
      | Some s \<Rightarrow> if isFunctionItem s database then
          Some (s, y, [KLabel], SUIdKLabel FunHole) else None)
           | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUKLabelFun x r))
          | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUKLabelFun r y))"
| "localteFunTermInSUKItem (SUKItem x y z) database =
       (case localteFunTermInSUKLabel x database of None \<Rightarrow> 
      (case localteFunTermInSUKList y database of None \<Rightarrow> 
    (case getSUKLabelMeaning x of None \<Rightarrow> None
      | Some s \<Rightarrow> if isFunctionItem s database then
          Some (s, y, z, SUIdKItem FunHole z) else None)
           | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUKItem x r z))
          | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUKItem r y z))"
| "localteFunTermInSUKItem (SUIdKItem x y) database = None"
| "localteFunTermInSUKItem (SUHOLE x) database = None"
| "localteFunTermInSUKList [] database = None"
| "localteFunTermInSUKList (a#l) database = (case a of ItemKl x \<Rightarrow>
       (case localteFunTermInSUBigKWithLabel x database
       of None \<Rightarrow> (case localteFunTermInSUKList l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
       | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (ItemKl r)#l))
       | _ \<Rightarrow> (case localteFunTermInSUKList l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r)))"
| "localteFunTermInSUBigKWithBag (SUK a) database = (case localteFunTermInSUK a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUK r))"
| "localteFunTermInSUBigKWithBag (SUList a) database = (case localteFunTermInSUList a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUList r))"
| "localteFunTermInSUBigKWithBag (SUSet a) database = (case localteFunTermInSUSet a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUSet r))"
| "localteFunTermInSUBigKWithBag (SUMap a) database = (case localteFunTermInSUMap a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUMap r))"
| "localteFunTermInSUBigKWithBag (SUBag a) database = (case localteFunTermInSUBag a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUBag r))"
| "localteFunTermInSUBigKWithLabel (SUBigBag a) database =
      (case localteFunTermInSUBigKWithBag a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUBigBag r))"
| "localteFunTermInSUBigKWithLabel (SUBigLabel a) database =
          (case localteFunTermInSUKLabel a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUBigLabel r))"
| "localteFunTermInSUK [] database = None"
| "localteFunTermInSUK (a#l) database = (case a of ItemFactor x \<Rightarrow> 
      (case localteFunTermInSUKItem x database of None \<Rightarrow>
        (case localteFunTermInSUK l database of None \<Rightarrow> None
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (ItemFactor r)#l))
       | SUKKItem x y z \<Rightarrow>
       (case localteFunTermInSUKLabel x database of None \<Rightarrow>
        (case localteFunTermInSUKList y database of None \<Rightarrow>
       (case localteFunTermInSUK l database of None \<Rightarrow> 
            (case getSUKLabelMeaning x of None \<Rightarrow> None
          | Some s \<Rightarrow> if isFunctionItem s database then
            Some (s, y,z, (if z = [K] then IdFactor FunHole else ItemFactor (SUIdKItem (FunHole) z))#l)
              else None)
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUKKItem x r z)#l))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUKKItem r y z)#l))
      | _ \<Rightarrow> (case localteFunTermInSUK l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r)))"
| "localteFunTermInSUList [] database = None"
| "localteFunTermInSUList (a#l) database = (case a of ItemL x \<Rightarrow> 
      (case localteFunTermInSUK x database of None \<Rightarrow>
        (case localteFunTermInSUList l database of None \<Rightarrow> None
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (ItemL r)#l))
       | SUListKItem x y \<Rightarrow>
       (case localteFunTermInSUKLabel x database of None \<Rightarrow>
        (case localteFunTermInSUKList y database of None \<Rightarrow>
       (case localteFunTermInSUList l database of None \<Rightarrow>
        (case getSUKLabelMeaning x of None \<Rightarrow> None
          | Some s \<Rightarrow> if isFunctionItem s database then
            Some (s, y,[List], (IdL FunHole)#l)
              else None)
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUListKItem x r)#l))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUListKItem r y)#l))
      | _ \<Rightarrow> (case localteFunTermInSUList l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun, ty,a#r)))"
| "localteFunTermInSUSet [] database = None"
| "localteFunTermInSUSet (a#l) database = (case a of ItemS x \<Rightarrow> 
      (case localteFunTermInSUK x database of None \<Rightarrow>
        (case localteFunTermInSUSet l database of None \<Rightarrow> None
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (ItemS r)#l))
       | SUSetKItem x y \<Rightarrow>
       (case localteFunTermInSUKLabel x database of None \<Rightarrow>
        (case localteFunTermInSUKList y database of None \<Rightarrow>
       (case localteFunTermInSUSet l database of None \<Rightarrow>
        (case getSUKLabelMeaning x of None \<Rightarrow> None
          | Some s \<Rightarrow> if isFunctionItem s database then
            Some (s, y, [Set], (IdS FunHole)#l)
              else None)
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUSetKItem x r)#l))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUSetKItem r y)#l))
      | _ \<Rightarrow> (case localteFunTermInSUSet l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r)))"
| "localteFunTermInSUMap [] database = None"
| "localteFunTermInSUMap (a#l) database = (case a of ItemM x y \<Rightarrow> 
      (case localteFunTermInSUK x database of None \<Rightarrow>
      (case localteFunTermInSUK y database of None \<Rightarrow>
        (case localteFunTermInSUMap l database of None \<Rightarrow> None
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (ItemM x r)#l))
       | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun, ty,(ItemM r y)#l))
       | SUMapKItem x y \<Rightarrow>
       (case localteFunTermInSUKLabel x database of None \<Rightarrow>
        (case localteFunTermInSUKList y database of None \<Rightarrow>
       (case localteFunTermInSUMap l database of None \<Rightarrow>
        (case getSUKLabelMeaning x of None \<Rightarrow> None
          | Some s \<Rightarrow> if isFunctionItem s database then
            Some (s, y,[Map], (IdM FunHole)#l)
              else None)
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUMapKItem x r)#l))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUMapKItem r y)#l))
      | _ \<Rightarrow> (case localteFunTermInSUMap l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r)))"
| "localteFunTermInSUBag [] database = None"
| "localteFunTermInSUBag (a#l) database = (case a of ItemB x y z \<Rightarrow>
       (case localteFunTermInSUBigKWithBag z database
       of None \<Rightarrow> (case localteFunTermInSUBag l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
       | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (ItemB x y r)#l))
       | _ \<Rightarrow> (case localteFunTermInSUBag l database of None \<Rightarrow> None
         | Some (la, fun, ty, r) \<Rightarrow> Some (la, fun,ty, a#r)))"
by pat_completeness auto

termination sorry

fun getFunRules :: "('upVar, 'var, 'metaVar) rulePat list
                   \<Rightarrow> ('upVar, 'var, 'metaVar) rulePat list" where
"getFunRules [] = []"
| "getFunRules ((FunPat s fl f)#l) = (FunPat s fl f)#(getFunRules l)"
| "getFunRules (x#l) = getFunRules l"

fun getRidOfLabel where
"getRidOfLabel [] = Some []"
| "getRidOfLabel ((KLabelFunPat s kl,b,c)#l) = (case getRidOfLabel l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((kl,b,c)#l'))"
| "getRidOfLabel ((KFunPat s kl,b,c)#l) = (case getRidOfLabel l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((kl,b,c)#l'))"
| "getRidOfLabel ((KItemFunPat s kl,b,c)#l) = (case getRidOfLabel l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((kl,b,c)#l'))"
| "getRidOfLabel ((ListFunPat s kl,b,c)#l) = (case getRidOfLabel l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((kl,b,c)#l'))"
| "getRidOfLabel ((SetFunPat s kl,b,c)#l) = (case getRidOfLabel l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((kl,b,c)#l'))"
| "getRidOfLabel ((MapFunPat s kl,b,c)#l) = (case getRidOfLabel l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((kl,b,c)#l'))"
| "getRidOfLabel ((NormalPat a,b,c)#l) = None"

fun getFunRule where
"getFunRule s [] = None"
| "getFunRule s ((FunPat s' fl f)#l) = (if s = s' then
    (case f of None \<Rightarrow> getRidOfLabel fl 
       | Some f' \<Rightarrow> getRidOfLabel (fl@[f'])) else getFunRule s l)"
| "getFunRule s (x#l) = getFunRule s l"

definition builtinLabels where
"builtinLabels = [GetKLabel, IsKResult, AndBool, NotBool,
                      OrBool, Sort, MapUpdate, EqualK, NotEqualK, EqualSet, EqualMap,
                       EqualKLabel, NotEqualKLabel, PlusInt, MinusInt, TimesInt]"

primrec inLabelList where
"inLabelList a [] = False"
| "inLabelList a (x#l) = (if a = x then True else inLabelList a l)"

fun evalMapUpdate where
"evalMapUpdate [] a b = [(ItemM a b)]"
| "evalMapUpdate (x#xl) a b = (case x of ItemM u v \<Rightarrow>
                      if u = a then (ItemM a b)#xl else x#(evalMapUpdate xl a b) | _ \<Rightarrow> x#xl)"

fun turnSet where
"turnSet [] = {}"
| "turnSet ((ItemS s)#l) = insert s (turnSet l)"
| "turnSet (a#l) = turnSet l"

definition evalEqualSet where
"evalEqualSet a b = ((turnSet a) = (turnSet b))"

fun turnMap where
"turnMap [] = {}"
| "turnMap ((ItemM a b)#l) = insert (a,b) (turnMap l)"
| "turnMap (a#l) = turnMap l"

definition evalEqualMap where
"evalEqualMap a b = ((turnMap a) = (turnMap b))"

fun evalBuiltinFun where
"evalBuiltinFun GetKLabel kl database subG =
    (case kl of [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem l newl t)]))]
                \<Rightarrow> Some (KLabelSubs l) | _ \<Rightarrow> None)"
| "evalBuiltinFun IsKResult kl database subG =
    (case kl of [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel s) newl t)]))]
                \<Rightarrow> (case getSort s database of None \<Rightarrow> None
                    | Some t' \<Rightarrow> if subsortList t' [KResult] subG
          then Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]))
          else Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (BoolConst False))) [] [Bool])))
                    | _ \<Rightarrow> None)"
| "evalBuiltinFun AndBool kl database subG =
    (case kl of [ItemKl (SUBigBag (SUK [ItemFactor
                               (SUKItem (SUKLabel (ConstToLabel (BoolConst b1))) newl1 [Bool])])),
                 ItemKl (SUBigBag (SUK [ItemFactor
                               (SUKItem (SUKLabel (ConstToLabel (BoolConst b2))) newl2 [Bool])]))]
                \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (BoolConst (b1 \<and> b2)))) [] [Bool]))
                    | _ \<Rightarrow> None)"
| "evalBuiltinFun OrBool kl database subG =
    (case kl of [ItemKl (SUBigBag (SUK [ItemFactor
                               (SUKItem (SUKLabel (ConstToLabel (BoolConst b1))) newl1 [Bool])])),
                 ItemKl (SUBigBag (SUK [ItemFactor
                               (SUKItem (SUKLabel (ConstToLabel (BoolConst b2))) newl2 [Bool])]))]
                \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (BoolConst (b1 \<or> b2)))) [] [Bool]))
                    | _ \<Rightarrow> None)"
| "evalBuiltinFun NotBool kl database subG =
    (case kl of [ItemKl (SUBigBag (SUK [ItemFactor
                               (SUKItem (SUKLabel (ConstToLabel (BoolConst b1))) newl1 [Bool])]))]
                \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (BoolConst (\<not> b1)))) [] [Bool]))
                    | _ \<Rightarrow> None)"
| "evalBuiltinFun MapUpdate kl database subG =
    (case kl of [ItemKl (SUBigBag (SUMap ml)), ItemKl (SUBigBag (SUK key)),ItemKl (SUBigBag (SUK v))]
                \<Rightarrow> Some (MapSubs (evalMapUpdate ml key v)) | _ \<Rightarrow> None)"
| "evalBuiltinFun EqualSet kl database subG =
    (case kl of [ItemKl (SUBigBag (SUSet a)),ItemKl (SUBigBag (SUSet b))]
           \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (BoolConst (evalEqualSet a b)))) [] [Bool]))
                        | _ \<Rightarrow> None)"
| "evalBuiltinFun EqualMap kl database subG =
    (case kl of [ItemKl (SUBigBag (SUMap a)),ItemKl (SUBigBag (SUMap b))]
           \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (BoolConst (evalEqualMap a b)))) [] [Bool]))
                        | _ \<Rightarrow> None)"
| "evalBuiltinFun EqualK kl database subG =
    (case kl of [ItemKl (SUBigBag (SUK a)),ItemKl (SUBigBag (SUK b))]
           \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (BoolConst (a = b)))) [] [Bool]))
                        | _ \<Rightarrow> None)"
| "evalBuiltinFun NotEqualK kl database subG =
    (case kl of [ItemKl (SUBigBag (SUK a)),ItemKl (SUBigBag (SUK b))]
           \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (BoolConst (a \<noteq> b)))) [] [Bool]))
                        | _ \<Rightarrow> None)"
| "evalBuiltinFun EqualKLabel kl database subG =
    (case kl of [ItemKl (SUBigLabel (SUKLabel a)),ItemKl (SUBigLabel (SUKLabel b))]
           \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (BoolConst (a = b)))) [] [Bool]))
                        | _ \<Rightarrow> None)"
| "evalBuiltinFun NotEqualKLabel kl database subG =
    (case kl of [ItemKl (SUBigLabel (SUKLabel a)),ItemKl (SUBigLabel (SUKLabel b))]
           \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (BoolConst (a \<noteq> b)))) [] [Bool]))
                        | _ \<Rightarrow> None)"
| "evalBuiltinFun PlusInt kl database subG =
    (case kl of [ItemKl (SUBigBag (SUK [ItemFactor
                               (SUKItem (SUKLabel (ConstToLabel (IntConst b1))) newl1 t1)])),
                 ItemKl (SUBigBag (SUK [ItemFactor
                               (SUKItem (SUKLabel (ConstToLabel (IntConst b2))) newl2 t2)]))]
                \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (IntConst (b1 + b2)))) [] [kSyntax.Int]))
                    | _ \<Rightarrow> None)"
| "evalBuiltinFun MinusInt kl database subG =
    (case kl of [ItemKl (SUBigBag (SUK [ItemFactor
                               (SUKItem (SUKLabel (ConstToLabel (IntConst b1))) newl1 t1)])),
                 ItemKl (SUBigBag (SUK [ItemFactor
                               (SUKItem (SUKLabel (ConstToLabel (IntConst b2))) newl2 t2)]))]
                \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (IntConst (b1 - b2)))) [] [kSyntax.Int]))
                    | _ \<Rightarrow> None)"
| "evalBuiltinFun TimesInt kl database subG =
    (case kl of [ItemKl (SUBigBag (SUK [ItemFactor
                               (SUKItem (SUKLabel (ConstToLabel (IntConst b1))) newl1 t1)])),
                 ItemKl (SUBigBag (SUK [ItemFactor
                               (SUKItem (SUKLabel (ConstToLabel (IntConst b2))) newl2 t2)]))]
                \<Rightarrow> Some (KItemSubs (SUKItem (SUKLabel (ConstToLabel (IntConst (b1 * b2)))) [] [kSyntax.Int]))
                    | _ \<Rightarrow> None)"
| "evalBuiltinFun A kl database subG = None"

inductive funEvaluationBool and funEvaluationBoolAux where
 conZeroStep : " \<not> hasFunLabelInSUKItem C database
    \<Longrightarrow> funEvaluationBool allRules database subG (Continue C) (Stop C)"
| conFunStep : "\<lbrakk> hasFunLabelInSUKItem C database ; l \<in> set builtinLabels;
    localteFunTermInSUKItem C database = Some (l, fun, ty, Cr);
            evalBuiltinFun l fun database subG = Some r;
      substitutionInSUKItem Cr [(FunHole, r)] = Some C';
       funEvaluationBool allRules database subG (Continue C') (Stop C'') \<rbrakk>
        \<Longrightarrow> funEvaluationBool allRules database subG (Continue C) (Stop C'')"
| conOneStep : "\<lbrakk> hasFunLabelInSUKItem C database ; l \<notin> set builtinLabels;
    localteFunTermInSUKItem C database = Some (l, fun, ty, Cr); getFunRule l allRules = Some fl;
          funEvaluationBoolAux allRules database subG fl fun (Continue Cr) (Stop C');
       funEvaluationBool allRules database subG (Continue C') (Stop C'') \<rbrakk>
        \<Longrightarrow> funEvaluationBool allRules database subG (Continue C) (Stop C'')"
| emptyRule : "funEvaluationBoolAux allRules database subG [] fun (Continue Cr) (Div Cr)"
| noPatRule : "\<lbrakk> patternMacroingInSUKList p fun [] subG = None ;
   funEvaluationBoolAux allRules database subG fl fun (Continue Cr) (Stop C') \<rbrakk>
         \<Longrightarrow> funEvaluationBoolAux allRules database subG
                               ((p,r,c)#fl) fun (Continue Cr) (Stop C')"
| falseRule : "\<lbrakk> patternMacroingInSUKList p fun [] subG = Some acc ;
   substitutionInSUKItem c acc  = Some value ;
   funEvaluationBool allRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst False));
   funEvaluationBoolAux allRules database subG fl fun (Continue Cr) (Stop C') \<rbrakk>
         \<Longrightarrow> funEvaluationBoolAux allRules database subG
                               ((p,r,c)#fl) fun (Continue Cr) (Stop C')"
| trueRule : "\<lbrakk> patternMacroingInSUKList p fun [] subG = Some acc ;
   substitutionInSUKItem c acc  = Some value ;
   funEvaluationBool allRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst True));
   substitutionInSubsFactor r acc = Some r' ; substitutionInSUKItem Cr [(FunHole, r')] = Some C';
     typeCheckCondition C' database subG = Some C'' \<rbrakk> 
                \<Longrightarrow> funEvaluationBoolAux allRules database subG
       ((p,r,c)#l) fun (Continue Cr) (Stop C'')"

code_pred funEvaluationBoolAux .
code_pred funEvaluationBool .

definition boolEvalFun where
"boolEvalFun allRules database subG C =
         Predicate.the (funEvaluationBool_i_i_i_i_o allRules database subG (Continue C))"

inductive funEvaluation and funEvaluationAux
where
 conZeroStep : " \<not> hasFunLabelInSUBag B database
                 \<Longrightarrow> funEvaluation allRules database subG (Continue B) (Stop B)"
| conFunStep : "\<lbrakk> hasFunLabelInSUBag C database ; l \<in> set builtinLabels;
    localteFunTermInSUBag C database = Some (l, fun, ty, Cr);
            evalBuiltinFun l fun database subG = Some r;
      substitutionInSUBag Cr [(FunHole, r)] = Some C';
       funEvaluation allRules database subG (Continue C') (Stop C'') \<rbrakk>
        \<Longrightarrow> funEvaluation allRules database subG (Continue C) (Stop C'')"
| conOneStep : "\<lbrakk> hasFunLabelInSUBag B database ; l \<notin> set builtinLabels;
    localteFunTermInSUBag B database = Some (l, fun, ty, Br); getFunRule l allRules = Some fl;
          funEvaluationAux allRules database subG fl fun (Continue Br) (Stop B');
       funEvaluation allRules database subG (Continue B') (Stop B'') \<rbrakk>
        \<Longrightarrow> funEvaluation allRules database subG (Continue B) (Stop B'')"
| emptyRule : "funEvaluationAux allRules database subG [] fun (Continue Br) (Div Br)"
| noPatRule : "\<lbrakk> patternMacroingInSUKList p fun [] subG = None ;
   funEvaluationAux allRules database subG fl fun (Continue Br) (Stop B') \<rbrakk>
         \<Longrightarrow> funEvaluationAux allRules database subG
                               ((p,r,c)#fl) fun (Continue Br) (Stop B')"
| falseRule : "\<lbrakk> patternMacroingInSUKList p fun [] subG = Some acc ;
   substitutionInSUKItem c acc  = Some value ;
   funEvaluationBool allRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst False));
   funEvaluationAux allRules database subG fl fun (Continue Br) (Stop B') \<rbrakk>
         \<Longrightarrow> funEvaluationAux allRules database subG
                               ((p,r,c)#fl) fun (Continue Br) (Stop B')"
| trueRule : "\<lbrakk> patternMacroingInSUKList p fun [] subG = Some acc ;
   substitutionInSUKItem c acc  = Some value ;
   funEvaluationBool allRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst True));
   substitutionInSubsFactor r acc = Some r' ; substitutionInSUBag Br [(FunHole, r')] = Some B';
     typeCheckProgramState B' database subG = Some B'' \<rbrakk> 
                \<Longrightarrow> funEvaluationAux allRules database subG
       ((p,r,c)#l) fun (Continue Br) (Stop B'')"

code_pred funEvaluation .
code_pred funEvaluationAux .

definition funRuleEvalFun where
"funRuleEvalFun allRules database subG C =
         Predicate.the (funEvaluation_i_i_i_i_o allRules database subG (Continue C))"

export_code Eps Continue Success FunTrans Single IntConst Bool kSyntax.Set Defined UnitLabel NonTerminal
    Strict Syntax Star Stdin Multiplicity KTerm KLabelC Heat TheSyntax IRKLabel IRKItem SimId
       KLabelMatching KLabelFunPat SUKLabel KLabelSubs FunPat SingleTon OtherVar 
    Parsed AChar Suc Char Num.One Int.Pos Num.inc formGraph syntaxSetToKItemSetAux
   symbolsToKLabel syntaxToKItem getKLabelName subsort getNonTerminalInList builtinConstTable
    getValueTerm irToSUInKLabel irToSUInKItem irToSUInPat irToSUInMatchFactor subsortGraph
    AllSubsorts kResultSubsorts getKResultSubsorts preSubsortGraph preSubsortTerms syntaxSetToKItems
     PreAllSubsorts getAllSubsortInKFile mergeTuples mergeList getAllSorts simpleKToIR
     simpleKToIRKList simpleKToSU simpleKToSUKList  suToIRInKLabel suToIRInSubsFactor
    boolEvalFun funRuleEvalFun tupleToRulePats assignSortInRules collectDatabase tupleToRulePats
   tupleToRulePat tupleToRuleInParsed isFunctionItem getSort in OCaml  module_name K file "k.ml"



(* dealing with anywhere rules *)

fun getAnywhereRules where
"getAnywhereRules [] = []"
| "getAnywhereRules ((AnywherePat s pl right con)#l) =
                    (s, pl, right, con)#(getAnywhereRules l)"
| "getAnywhereRules (x#l) = getAnywhereRules l"

function applyAnywhereRuleInSUKItem
    and applyAnywhereRuleInSUKList
    and applyAnywhereRuleInSUBigKWithBag
    and applyAnywhereRuleInSUBigKWithLabel
    and applyAnywhereRuleInSUK
    and applyAnywhereRuleInSUList
    and applyAnywhereRuleInSUSet
    and applyAnywhereRuleInSUMap
    and applyAnywhereRuleInSUBag where
"applyAnywhereRuleInSUKItem allRules database subG
          (s, kl, t, con) (SUKItem l r ty) = (case getSUKLabelMeaning l of None \<Rightarrow> None
      | Some s' \<Rightarrow> (if isFunctionItem s' database then None else
    (case applyAnywhereRuleInSUKList allRules database subG
          (s, kl, t, con) r of None \<Rightarrow> None
    | Some r' \<Rightarrow> if r = r' then (if s = s' then 
         (case patternMacroingInSUKList kl r [] subG of None \<Rightarrow>
        Some [ItemFactor (SUKItem l r ty)] | Some acc \<Rightarrow>
      (case substitutionInSUKItem con acc of None \<Rightarrow> Some [ItemFactor (SUKItem l r ty)]
       | Some value \<Rightarrow> (if funEvaluationBool allRules database subG
       (Continue value) (Stop (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]))
        then (case substitutionInSUK t acc of None \<Rightarrow> Some [ItemFactor (SUKItem l r ty)]
          | Some t' \<Rightarrow> Some t') else Some [ItemFactor (SUKItem l r ty)])))
         else Some [ItemFactor (SUKItem l r ty)]) else Some [ItemFactor (SUKItem l r' ty)])))"
| "applyAnywhereRuleInSUKItem allRules database subG
          (s, kl, t, con) (SUIdKItem x ty) = None"
| "applyAnywhereRuleInSUKItem allRules database subG
          (s, kl, t, con) (SUHOLE ty) = Some [ItemFactor (SUHOLE ty)]"
| "applyAnywhereRuleInSUKList allRules database subG
          (s, kl, t, con) [] = Some []"
| "applyAnywhereRuleInSUKList allRules database subG
          (s, kl, t, con) (a#l) = (case a of IdKl x \<Rightarrow> None
         | ItemKl x \<Rightarrow> (case applyAnywhereRuleInSUBigKWithLabel allRules database subG
          (s, kl, t, con) x of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case applyAnywhereRuleInSUKList allRules database subG
          (s, kl, t, con) l of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some ((ItemKl x')#l'))))"
| "applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) (SUK a) = (case applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) a of None \<Rightarrow> None
        | Some a' \<Rightarrow> Some (SUK a')) "
| "applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) (SUList a) = (case applyAnywhereRuleInSUList allRules database subG
          (s, kl, t, con) a of None \<Rightarrow> None
        | Some a' \<Rightarrow> Some (SUList a')) "
| "applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) (SUSet a) = (case applyAnywhereRuleInSUSet allRules database subG
          (s, kl, t, con) a of None \<Rightarrow> None
        | Some a' \<Rightarrow> Some (SUSet a')) "
| "applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) (SUMap a) = (case applyAnywhereRuleInSUMap allRules database subG
          (s, kl, t, con) a of None \<Rightarrow> None
        | Some a' \<Rightarrow> Some (SUMap a'))"
| "applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) (SUBag a) = (case applyAnywhereRuleInSUBag allRules database subG
          (s, kl, t, con) a of None \<Rightarrow> None
        | Some a' \<Rightarrow> Some (SUBag a'))"
| "applyAnywhereRuleInSUBigKWithLabel allRules database subG
          (s, kl, t, con) (SUBigBag a) = (case applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) a of None \<Rightarrow> None
        | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "applyAnywhereRuleInSUBigKWithLabel allRules database subG
          (s, kl, t, con) (SUBigLabel a) = Some (SUBigLabel a)"
| "applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) [] = Some []"
| "applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) (a#l) = (case a of ItemFactor x \<Rightarrow>
        (case applyAnywhereRuleInSUKItem allRules database subG
          (s, kl, t, con) x of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) l of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some (x'@l')))
     | _ \<Rightarrow> None)"
| "applyAnywhereRuleInSUList allRules database subG
          (s, kl, t, con) [] = Some []"
| "applyAnywhereRuleInSUList allRules database subG
          (s, kl, t, con) (a#l) = (case a of ItemL x \<Rightarrow>
        (case applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) x of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case applyAnywhereRuleInSUList allRules database subG
          (s, kl, t, con) l of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some ((ItemL x')#l')))
     | _ \<Rightarrow> None)"
| "applyAnywhereRuleInSUSet allRules database subG
          (s, kl, t, con) [] = Some []"
| "applyAnywhereRuleInSUSet allRules database subG
          (s, kl, t, con) (a#l) = (case a of ItemS x \<Rightarrow>
        (case applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) x of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case applyAnywhereRuleInSUSet allRules database subG
          (s, kl, t, con) l of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some ((ItemS x')#l')))
     | _ \<Rightarrow> None)"
| "applyAnywhereRuleInSUMap allRules database subG
          (s, kl, t, con) [] = Some []"
| "applyAnywhereRuleInSUMap allRules database subG
          (s, kl, t, con) (a#l) = (case a of ItemM x y \<Rightarrow>
        (case applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) x of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) y of None \<Rightarrow> None
       | Some y' \<Rightarrow> (case applyAnywhereRuleInSUMap allRules database subG
          (s, kl, t, con) l of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some ((ItemM x' y')#l'))))
     | _ \<Rightarrow> None)"
| "applyAnywhereRuleInSUBag allRules database subG
          (s, kl, t, con) [] = Some []"
| "applyAnywhereRuleInSUBag allRules database subG
          (s, kl, t, con) (a#l) = (case a of ItemB x y z \<Rightarrow>
        (case applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) z of None \<Rightarrow> None
       | Some z' \<Rightarrow> (case applyAnywhereRuleInSUBag allRules database subG
          (s, kl, t, con) l of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some ((ItemB x y z')#l')))
     | _ \<Rightarrow> None)"
by pat_completeness auto

termination sorry

fun applyAnywhereRules :: "('m, 'n, 'o) rulePat list
     \<Rightarrow> ('m kSyntax.sort list \<times> 'm kSyntax.sort list list \<times> 'm label KItemSyntax \<times> 'p \<times> bool) list
        \<Rightarrow> ('m kSyntax.sort \<times> 'm kSyntax.sort list) list
           \<Rightarrow> ('m label \<times> ('m, 'n, 'o) irKList \<times> ('m, 'n, 'o) suKFactor list
     \<times> ('m, 'n, 'o) suKItem) list
            \<Rightarrow> ('m, 'n, 'o) suB list \<Rightarrow> ('m, 'n, 'o) suB list option" where
"applyAnywhereRules allRules database subG [] B = Some B"
| "applyAnywhereRules allRules database subG (f#fl) B =
    (case applyAnywhereRuleInSUBag allRules database subG f B
    of None \<Rightarrow> None | Some B' \<Rightarrow> 
       if B = B' then applyAnywhereRules allRules database subG fl B
      else Some B')"

inductive funAnywhere where
zeroStep : "\<lbrakk> funEvaluation allFunRules database subG (Continue B) (Stop B');
            applyAnywhereRules allFunRules database subG anywheres B' = Some B' \<rbrakk>
       \<Longrightarrow> funAnywhere allFunRules anywheres database subG (Continue B) (Stop B')"
| oneStep : "\<lbrakk> funEvaluation allFunRules database subG (Continue B) (Stop B');
            applyAnywhereRules allFunRules database subG anywheres B' = Some B'';
   B \<noteq> B'';  funAnywhere allFunRules anywheres database subG (Continue B'') (Stop B''') \<rbrakk>
       \<Longrightarrow> funAnywhere allFunRules anywheres database subG (Continue B) (Stop B''')"

(*
code_pred funAnywhere .
*)

(* define K cell rule and bag rule *)
fun getAllKCells and getAllKCellsAux where
"getAllKCells [] = Some []"
| "getAllKCells ((IdB x)#l) = None"
| "getAllKCells ((ItemB x y z)#l) = (if x = LittleK then (case z of SUK a \<Rightarrow>
                (case (getAllKCells l) of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some (a#l')) | _ \<Rightarrow> None)
                   else (case getAllKCellsAux z of None \<Rightarrow> None
           | Some z' \<Rightarrow> (case  getAllKCells l of None \<Rightarrow> None
                 | Some l' \<Rightarrow> Some (z'@l'))))"
| "getAllKCellsAux (SUBag a) = getAllKCells a"
| "getAllKCellsAux a = Some []"

fun replaceKCells
   and replaceKCellsAux where
"replaceKCells [] t r = Some []"
| "replaceKCells ((IdB x)#l) t r = None"
| "replaceKCells ((ItemB x y z)#l) t r = (if x = LittleK then (case z of SUK a \<Rightarrow>
                (case (replaceKCells l t r) of None \<Rightarrow> None
           | Some l' \<Rightarrow> if a = t then Some ((ItemB x y (SUK r))#l')
             else Some ((ItemB x y z)#l')) | _ \<Rightarrow> None)
                   else (case replaceKCellsAux z t r of None \<Rightarrow> None
           | Some z' \<Rightarrow> (case  replaceKCells l t r of None \<Rightarrow> None
                 | Some l' \<Rightarrow> Some ((ItemB x y z')#l'))))"
| "replaceKCellsAux (SUBag a) t r = (case replaceKCells a t r of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (SUBag a'))"
| "replaceKCellsAux a t r = Some a"

fun getAllKRules where
"getAllKRules [] = []"
| "getAllKRules ((KRulePat a b c d)#l) = (a,b,c,d)#(getAllKRules l)"
| "getAllKRules (x#l) = getAllKRules l"

fun getAllBagRules where
"getAllBagRules [] = []"
| "getAllBagRules ((BagRulePat a b c d)#l) = (a,b,c,d)#(getAllBagRules l)"
| "getAllBagRules (x#l) = getAllBagRules l"

inductive oneStepKRuleAux where
zeroStep : "oneStepKRuleAux allFunRules database subG [] (Continue C) (Stop C)"
| noPatRule : "\<lbrakk> patternMacroingInSUK p C [] subG = None;
      oneStepKRuleAux allFunRules database subG fl (Continue C) (Stop C') \<rbrakk>
    \<Longrightarrow> oneStepKRuleAux allFunRules database subG ((p,r,con,l)#fl) (Continue C) (Stop C')"
| falseRule : "\<lbrakk> patternMacroingInSUK p C [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst False));
      oneStepKRuleAux allFunRules database subG fl (Continue C) (Stop C') \<rbrakk>
    \<Longrightarrow> oneStepKRuleAux allFunRules database subG ((p,r,con,l)#fl) (Continue C) (Stop C')"
| trueRule : "\<lbrakk> patternMacroingInSUK p C [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst True));
   substitutionInSUK r acc = Some r' \<rbrakk>
    \<Longrightarrow> oneStepKRuleAux allFunRules database subG ((p,r,con,l)#fl) (Continue C) (Stop r')"

(*
code_pred oneStepKRuleAux .
*)

inductive oneStepKRule where
zeroStep : "oneStepKRule allFunRules database subG allKRule [] None"
| failStep : "\<lbrakk> oneStepKRuleAux allFunRules database subG allKRule (Continue C) (Stop C);
   oneStepKRule allFunRules database subG allKRule l S \<rbrakk>
     \<Longrightarrow> oneStepKRule allFunRules database subG allKRule (C#l) S"
| oneStep : "\<lbrakk> oneStepKRuleAux allFunRules database subG allKRule (Continue C) (Stop C');
      C \<noteq> C' \<rbrakk>
     \<Longrightarrow> oneStepKRule allFunRules database subG allKRule (C#l) (Some (C,C'))"

(*
code_pred oneStepKRule .
*)

inductive oneStepBagRule where
zeroStep : "oneStepBagRule allFunRules database subG [] (Continue B) (Stop B)"
| noPatRule : "\<lbrakk> patternMacroingInSUBag p B [] subG = None;
      oneStepBagRule allFunRules database subG fl (Continue B) (Stop B') \<rbrakk>
    \<Longrightarrow> oneStepBagRule allFunRules database subG ((p,r,con,l)#fl) (Continue B) (Stop B')"
| falseRule : "\<lbrakk> patternMacroingInSUBag p B [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst False));
      oneStepBagRule allFunRules database subG fl (Continue B) (Stop B') \<rbrakk>
    \<Longrightarrow> oneStepBagRule allFunRules database subG ((p,r,con,l)#fl) (Continue B) (Stop B')"
| trueRule : "\<lbrakk> patternMacroingInSUBag p B [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst True));
   substitutionInSUBag r acc = Some r' \<rbrakk>
    \<Longrightarrow> oneStepBagRule allFunRules database subG ((p,r,con,l)#fl) (Continue B) (Stop r')"

(*
code_pred oneStepBagRule .
*)

(* defining K compile: compilation and checking process of K theory 
definition kcompile :: "('upVar, 'var, 'acapvar, 'metaVar) kFile
   \<Rightarrow> (('upVar, 'var, 'acapvar, 'metaVar) kFile \<times>
           ('upVar kSyntax.sort list \<times> 'upVar kSyntax.sort list list \<times>
          'upVar label KItemSyntax \<times> synAttrib list \<times> bool) list
    \<times> ('upVar kSyntax.sort \<times> 'upVar kSyntax.sort list) list \<times> ('upVar, 'var, 'metaVar) suB list
    \<times> ('upVar, 'var, 'metaVar) rulePat list, char list) oneStep" where
"kcompile Theory = (case syntaxSetToKItemTest Theory of None \<Rightarrow> 
         Failure (''Not a valid K theory.'') | Some database \<Rightarrow>
    if invalidSortChecks Theory then (if uniqueKLabelSyntax Theory
       then (case subsortGraph Theory of subG \<Rightarrow>
     (if validSyntaxSort [] Theory database subG then
     (case configurationTest Theory database subG of None
               \<Rightarrow> Failure (''The configuration is not valid.'')
        | Some confi \<Rightarrow> (case typeCheckRules Theory database subG of None \<Rightarrow>
            Failure (''The theory has invalid rules.'')
    | Some allRules \<Rightarrow> (case strictRuleTest [] Theory subG of None \<Rightarrow>
            Failure (''The theory has invalid strict attributes.'')
        | Some stl \<Rightarrow>
            Success (Theory,database,subG,confi,allRules@stl))))
       else Failure (''K theory has invalid syntax or strict attributes failed.'')))
     else Failure (''kLabels are not uniquely defined in this K theory.''))
         else Failure (''K theory has invalid subsort.''))"
*)
(* defining K Run *)
inductive krunAux where
zeroStep : "funAnywhere allFunRules allAnywheres database subG (Continue B) (Stop B')
           \<Longrightarrow> krunAux database subG (0::nat)
                      allFunRules allAnywheres allKRules allBagRules B B'"
| noStep : "\<lbrakk> funAnywhere allFunRules allAnywheres database subG (Continue B) (Stop B');
    getAllKCells B' = Some cl; oneStepKRule allFunRules database subG allKRules cl None;
    oneStepBagRule allFunRules database subG allBagRules (Continue B') (Stop B') \<rbrakk>
    \<Longrightarrow> krunAux database subG n allFunRules allAnywheres allKRules allBagRules B B'"
| kStep : "\<lbrakk> funAnywhere allFunRules allAnywheres database subG (Continue B) (Stop B');
    getAllKCells B' = Some cl; oneStepKRule allFunRules database subG allKRules cl (Some (C,C'));
     replaceKCells B' C C' = Some B''; typeCheckProgramState B'' database subG = Some Ba; n > 0;
     krunAux database subG (n - 1) allFunRules allAnywheres allKRules allBagRules Ba Bb \<rbrakk>
    \<Longrightarrow> krunAux database subG n allFunRules allAnywheres allKRules allBagRules B Bb"
| bagStep : "\<lbrakk> funAnywhere allFunRules allAnywheres database subG (Continue B) (Stop B');
    getAllKCells B' = Some cl; oneStepKRule allFunRules database subG allKRules cl None; n > 0;
    oneStepBagRule allFunRules database subG allBagRules (Continue B') (Stop B''); B' \<noteq> B'';
     typeCheckProgramState B'' database subG = Some Ba;
     krunAux database subG (n - 1) allFunRules allAnywheres allKRules allBagRules Ba Bb \<rbrakk>
    \<Longrightarrow> krunAux database subG n allFunRules allAnywheres allKRules allBagRules B Bb"

(*
code_pred krunAux .
*)

inductive krun where
theoryFail : "kcompile Theory = Failure s \<Longrightarrow>
      krun Theory n l (Failure (''Bad result: ''@s))"
| programFail : "\<lbrakk> kcompile Theory = Success (Theory, database, subG, confi, allRules);
   realConfigurationTest l Theory database subG = None \<rbrakk>
   \<Longrightarrow> krun Theory n l (Failure ''Bad input program.'')"
| macroRuleFail : "\<lbrakk> kcompile Theory = Success (Theory, database, subG,confi, allRules);
   applyAllMacroRulesCheck l Theory database subG = None \<rbrakk>
   \<Longrightarrow> krun Theory n l (Failure ''Macro rules have a problem.'')"
| goodRun : "\<lbrakk> kcompile Theory = Success (Theory, database, subG,confi, allRules);
      applyAllMacroRulesCheck l Theory database subG = Some (noMacroRules, B);
    getFunRules noMacroRules = allFunRules; getAnywhereRules noMacroRules = allAnywheres;
    getAllKRules noMacroRules = allKRules; getAllBagRules noMacroRules = allBagRules;
     krunAux database subG n  allFunRules allAnywheres allKRules allBagRules B B' \<rbrakk>
\<Longrightarrow> krun Theory n l (Success B')"

(*
code_pred krun .
*)

(* defining K search *)
fun divideAllKRules where
"divideAllKRules [] = ([],[])"
| "divideAllKRules ((KRulePat a b c d)#l) = (case divideAllKRules l of (left, right) \<Rightarrow>
       if d then ((a,b,c,d)#left,right) else (left,(a,b,c,d)#right))"
| "divideAllKRules (x#l) = divideAllKRules l"

fun divideAllBagRules where
"divideAllBagRules [] = ([],[])"
| "divideAllBagRules ((BagRulePat a b c d)#l) = (case divideAllBagRules l
     of (left, right) \<Rightarrow>
       if d then ((a,b,c,d)#left,right) else (left,(a,b,c,d)#right))"
| "divideAllBagRules (x#l) = divideAllBagRules l"

(* one step k rule in k search becomes collecting a list of results *)
inductive oneTransKRuleAux where
zeroStep : "oneTransKRuleAux allFunRules database subG [] C []"
| noPatRule : "\<lbrakk> patternMacroingInSUK p C [] subG = None;
      oneTransKRuleAux allFunRules database subG fl C Cl \<rbrakk>
    \<Longrightarrow> oneTransKRuleAux allFunRules database subG
             ((p,r,con,l)#fl) C Cl"
| falseRule : "\<lbrakk> patternMacroingInSUK p C [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst False));
      oneTransKRuleAux allFunRules database subG fl C Cl \<rbrakk>
    \<Longrightarrow> oneTransKRuleAux allFunRules database subG
               ((p,r,con,l)#fl) C Cl"
| trueRule : "\<lbrakk> patternMacroingInSUK p C [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst True));
   substitutionInSUK r acc = Some r';
   oneTransKRuleAux allFunRules database subG fl C Cl \<rbrakk>
    \<Longrightarrow> oneTransKRuleAux allFunRules database subG
           ((p,r,con,l)#fl) C (List.insert (C,r') Cl)"

(*
code_pred oneTransKRuleAux .
*)

inductive oneTransKRule where
zeroStep : "oneTransKRule allFunRules database subG allKRule transKRule [] []"
| oneStep : "\<lbrakk> oneStepKRuleAux allFunRules database subG allKRule (Continue C) (Stop C');
    C \<noteq> C'; oneTransKRule allFunRules database subG allKRule transKRule l Cl \<rbrakk>
     \<Longrightarrow> oneTransKRule allFunRules database subG allKRule transKRule
            (C#l) (List.insert (C,C') Cl)"
| oneTrans : "\<lbrakk> oneStepKRuleAux allFunRules database subG allKRule (Continue C) (Stop C);
      oneTransKRuleAux allFunRules database subG transKRule C Cl;
       oneTransKRule allFunRules database subG allKRule transKRule l Cl' \<rbrakk>
     \<Longrightarrow> oneTransKRule allFunRules database subG allKRule transKRule
            (C#l) (insertAll Cl Cl')"

(*
code_pred oneTransKRule .
*)

inductive oneTransBagRule where
zeroStep : "oneTransBagRule allFunRules database subG [] B []"
| noPatRule : "\<lbrakk> patternMacroingInSUBag p B [] subG = None;
      oneTransBagRule allFunRules database subG fl B Bl \<rbrakk>
    \<Longrightarrow> oneTransBagRule allFunRules database subG ((p,r,con,l)#fl) B Bl"
| falseRule : "\<lbrakk> patternMacroingInSUBag p B [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst False));
      oneTransBagRule allFunRules database subG fl B Bl \<rbrakk>
    \<Longrightarrow> oneTransBagRule allFunRules database subG ((p,r,con,l)#fl) B Bl"
| trueRule : "\<lbrakk> patternMacroingInSUBag p B [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst True));
   substitutionInSUBag r acc = Some r';
   oneTransBagRule allFunRules database subG fl B Bl \<rbrakk>
    \<Longrightarrow> oneTransBagRule allFunRules database subG
      ((p,r,con,l)#fl) B (List.insert r' Bl)"

(*
code_pred oneTransBagRule .
*)

fun replaceKCellsInList where
"replaceKCellsInList B [] = []"
| "replaceKCellsInList B ((a,b)#l) = (case replaceKCells B a b of None
      \<Rightarrow> replaceKCellsInList B l
   | Some B' \<Rightarrow>  List.insert B' (replaceKCellsInList B l))"

inductive oneTransKSearch where
zeroStep : "oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules tranBagRules [] []"
| oneBagStep : "\<lbrakk> oneStepBagRule allFunRules database subG allBagRules (Continue B) (Stop B');
    B \<noteq> B'; oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules transBagRules l Cl \<rbrakk>
     \<Longrightarrow> oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules transBagRules (B#l) (List.insert B' Cl)"
| oneKTrans : "\<lbrakk> oneStepBagRule allFunRules database subG allBagRules (Continue B) (Stop B);
   getAllKCells B = Some cl; oneTransKRule allFunRules database subG allKRules transKRules cl acc;
  replaceKCellsInList B acc = Bl; oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules transBagRules l Bl' \<rbrakk>
     \<Longrightarrow> oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules transBagRules (B#l) (insertAll Bl Bl')"
| oneBagTrans : "\<lbrakk> oneStepBagRule allFunRules database subG allBagRules (Continue B) (Stop B);
   getAllKCells B = Some cl; oneTransKRule allFunRules database subG allKRules transKRules cl [];
  oneTransBagRule allFunRules database subG transBagRules B Bl;
  oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules transBagRules l Bl' \<rbrakk>
     \<Longrightarrow> oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules transBagRules (B#l) (insertAll Bl Bl')"

(*
code_pred oneTransKSearch .
*)

inductive allAllFunAnywhere where
zeroStep : "allAllFunAnywhere allFunRules allAnywheres database subG [] []"
| oneStep : "\<lbrakk> funAnywhere allFunRules allAnywheres database subG (Continue B) (Stop B');
      allAllFunAnywhere allFunRules allAnywheres database subG l Bl \<rbrakk>
    \<Longrightarrow> 
    allAllFunAnywhere allFunRules allAnywheres database subG (B#l) (B'#Bl)"

(*
code_pred allAllFunAnywhere .
*)

(* defining K search *)
inductive ksearchAux where
zeroStep : "allAllFunAnywhere allFunRules allAnywheres database subG Bl Bl'
           \<Longrightarrow> ksearchAux database subG (0::nat)
            allFunRules allAnywheres allKRules allBagRules transKRules transBagRules Bl Bl'"
| noStep : "\<lbrakk> allAllFunAnywhere allFunRules allAnywheres database subG Bl Bl';
    oneTransKSearch allFunRules database subG allKRules allBagRules
         transKRules transBagRules Bl' [] \<rbrakk>
    \<Longrightarrow> ksearchAux database subG n
            allFunRules allAnywheres allKRules allBagRules transKRules transBagRules Bl []"
| oneStep : "\<lbrakk> allAllFunAnywhere allFunRules allAnywheres database subG Bl Bl';
    oneTransKSearch allFunRules database subG allKRules allBagRules
         transKRules transBagRules Bl' Bl''; n > 0; length Bl'' > 0;
    ksearchAux database subG (n - 1) allFunRules
        allAnywheres allKRules allBagRules transKRules transBagRules Bl'' Bl''' \<rbrakk>
    \<Longrightarrow> ksearchAux database subG n allFunRules
        allAnywheres allKRules allBagRules transKRules transBagRules Bl Bl'''"

(*
code_pred ksearchAux .
*)

inductive ksearch where
theoryFail : "kcompile Theory = Failure s \<Longrightarrow>
      ksearch Theory n l (Failure (''Bad result: ''@s))"
| programFail : "\<lbrakk> kcompile Theory = Success (Theory, database, subG, confi, allRules);
   realConfigurationTest l Theory database subG = None \<rbrakk>
   \<Longrightarrow> ksearch Theory n l (Failure ''Bad input program.'')"
| macroRuleFail : "\<lbrakk> kcompile Theory = Success (Theory, database, subG,confi, allRules);
   applyAllMacroRulesCheck l Theory database subG = None \<rbrakk>
   \<Longrightarrow> ksearch Theory n l (Failure ''Macro rules have a problem.'')"
| goodRun : "\<lbrakk> kcompile Theory = Success (Theory, database, subG,confi, allRules);
      applyAllMacroRulesCheck l Theory database subG = Some (noMacroRules, B);
    getFunRules noMacroRules = allFunRules; getAnywhereRules noMacroRules = allAnywheres;
    divideAllKRules noMacroRules = (transKRules,allKRules);
     divideAllBagRules noMacroRules = (transBagRules,allBagRules);
     ksearchAux database subG n  allFunRules allAnywheres allKRules
                  allBagRules transKRules transBagRules [B] Bl \<rbrakk>
\<Longrightarrow> ksearch Theory n l (Success Bl)"

(*
code_pred ksearch .
*)

export_code Eps Continue Success FunTrans Single IntConst Bool Defined UnitLabel NonTerminal
    Strict Syntax Star Stdin Multiplicity KTerm KLabelC Heat TheSyntax IRKLabel IRKItem
       KLabelMatching KLabelFunPat SUKLabel KLabelSubs FunPat SingleTon OtherVar krun ksearch
    ARule Parsed AChar Suc Char Num.One Int.Pos Num.inc formGraph
   symbolsToKLabel syntaxToKItem syntaxSetToKItemTest getKLabelName subsort getNonTerminalInList
    getValueTerm in OCaml  module_name K file "k.ml"

end