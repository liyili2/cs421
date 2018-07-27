module K : sig
  type num = One | Bit0 of num | Bit1 of num
  type int = Zero_int | Pos of num | Neg of num
  type 'a equal = {equal : 'a -> 'a -> bool};;
  type nat = Zero_nat | Suc of nat
  type char = Zero_char | Char of num
  type 'a metaVar = Defined of 'a | Generated of nat | FunHole
  type real
  type theConstant = IntConst of int | FloatConst of real |
    StringConst of char list | BoolConst of bool | IdConst of char list
  type 'a sort = Bool | K | KItem | KLabel | KResult | KList | List | Seta | Map
    | Bag | OtherSort of 'a | Top | Int | Float | Id | String
  type 'a label = UnitLabel of 'a sort | ConstToLabel of theConstant | Sort |
    GetKLabel | IsKResult | AndBool | NotBool | OrBool | SetConLabel |
    SetItemLabel | ListConLabel | ListItemLabel | MapConLabel | MapItemLabel |
    MapUpdate | EqualK | NotEqualK | EqualKLabel | NotEqualKLabel |
    OtherLabel of char list | TokenLabel of char list | PlusInt | MinusInt |
    TimesInt | EqualSet | EqualMap
  type stdType = Stdin | Stdout
  type key = Star | Question
  type feature = Multiplicity of key | Stream of stdType | DotDotDot
  type 'a var = LittleK | OtherVar of 'a
  type ('a, 'b, 'c) suBigKWithBag = SUK of ('a, 'b, 'c) suKFactor list |
    SUList of ('a, 'b, 'c) suL list | SUSet of ('a, 'b, 'c) suS list |
    SUMap of ('a, 'b, 'c) suM list | SUBag of ('a, 'b, 'c) suB list
  and ('a, 'b, 'c) suB =
    ItemB of 'b var * feature list * ('a, 'b, 'c) suBigKWithBag |
    IdB of 'c metaVar
  and ('a, 'b, 'c) suBigKWithLabel = SUBigBag of ('a, 'b, 'c) suBigKWithBag |
    SUBigLabel of ('a, 'b, 'c) suKLabel
  and ('a, 'b, 'c) suKl = ItemKl of ('a, 'b, 'c) suBigKWithLabel |
    IdKl of 'c metaVar
  and ('a, 'b, 'c) suKLabel = SUKLabel of 'a label | SUIdKLabel of 'c metaVar |
    SUKLabelFun of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
  and ('a, 'b, 'c) suKItem =
    SUKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list * 'a sort list |
    SUIdKItem of 'c metaVar * 'a sort list | SUHOLE of 'a sort list
  and ('a, 'b, 'c) suKFactor = ItemFactor of ('a, 'b, 'c) suKItem |
    IdFactor of 'c metaVar |
    SUKKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list * 'a sort list
  and ('a, 'b, 'c) suL = ItemL of ('a, 'b, 'c) suKFactor list |
    IdL of 'c metaVar |
    SUListKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
  and ('a, 'b, 'c) suM =
    ItemM of ('a, 'b, 'c) suKFactor list * ('a, 'b, 'c) suKFactor list |
    IdM of 'c metaVar |
    SUMapKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
  and ('a, 'b, 'c) suS = ItemS of ('a, 'b, 'c) suKFactor list |
    IdS of 'c metaVar |
    SUSetKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
  type 'a state = Continue of 'a | Stop of 'a | Div of 'a
  type reg = Eps | Sym of char | Alt of reg * reg | TheSeq of reg * reg |
    Rep of reg
  type synAttrib = Strict of nat list | Seqstrict | Left | Right |
    Hook of char list | Function | Klabel of char list | Bracket | Tokena |
    Avoid | OnlyLabel | NotInRules | Regex of reg | NonAssoc |
    OtherSynAttr of char list
  type ('a, 'b) ruleAttrib = Attr of 'a | Heat | Cool | Transition | Anywhere |
    Structural | Owise | Macro | Result of 'b sort
  type ('a, 'b, 'c) subsFactor = KLabelSubs of ('a, 'b, 'c) suKLabel |
    KItemSubs of ('a, 'b, 'c) suKItem | KListSubs of ('a, 'b, 'c) suKl list |
    KSubs of ('a, 'b, 'c) suKFactor list | ListSubs of ('a, 'b, 'c) suL list |
    SetSubs of ('a, 'b, 'c) suS list | MapSubs of ('a, 'b, 'c) suM list |
    BagSubs of ('a, 'b, 'c) suB list
  type 'a rewrite = KTerm of 'a | KRewrite of 'a * 'a
  type ('a, 'b, 'c) k = Tilda of ('a, 'b, 'c) k rewrite * ('a, 'b, 'c) k rewrite
    | UnitK | IdK of 'c metaVar | SingleK of ('a, 'b, 'c) kItem rewrite |
    KFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
  and ('a, 'b, 'c) theList =
    ListCon of ('a, 'b, 'c) theList rewrite * ('a, 'b, 'c) theList rewrite |
    UnitList | IdList of 'c metaVar | ListItem of ('a, 'b, 'c) k rewrite |
    ListFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
  and ('a, 'b, 'c) bigK = TheK of ('a, 'b, 'c) k rewrite |
    TheList of ('a, 'b, 'c) theList rewrite |
    TheSet of ('a, 'b, 'c) theSet rewrite |
    TheMap of ('a, 'b, 'c) theMap rewrite
  and ('a, 'b, 'c) bag =
    BagCon of ('a, 'b, 'c) bag rewrite * ('a, 'b, 'c) bag rewrite | UnitBag |
    IdBag of 'c metaVar |
    Xml of 'b var * feature list * ('a, 'b, 'c) bag rewrite |
    SingleCell of 'b var * feature list * ('a, 'b, 'c) bigK
  and ('a, 'b, 'c) bigKWithBag = TheBigK of ('a, 'b, 'c) bigK |
    TheBigBag of ('a, 'b, 'c) bag rewrite |
    TheLabel of ('a, 'b, 'c) kLabel rewrite
  and ('a, 'b, 'c) kList =
    KListCon of ('a, 'b, 'c) kList rewrite * ('a, 'b, 'c) kList rewrite |
    UnitKList | KListItem of ('a, 'b, 'c) bigKWithBag | IdKList of 'c metaVar
  and ('a, 'b, 'c) kLabel = KLabelC of 'a label |
    KLabelFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite |
    IdKLabel of 'c metaVar
  and ('a, 'b, 'c) kItem =
    KItemC of ('a, 'b, 'c) kLabel rewrite * ('a, 'b, 'c) kList rewrite * 'a sort
    | Constant of theConstant * 'a sort | IdKItem of 'c metaVar * 'a sort |
    HOLE of 'a sort
  and ('a, 'b, 'c) theMap =
    MapCon of ('a, 'b, 'c) theMap rewrite * ('a, 'b, 'c) theMap rewrite |
    UnitMap | IdMap of 'c metaVar |
    MapItem of ('a, 'b, 'c) k rewrite * ('a, 'b, 'c) k rewrite |
    MapFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
  and ('a, 'b, 'c) theSet =
    SetCon of ('a, 'b, 'c) theSet rewrite * ('a, 'b, 'c) theSet rewrite |
    UnitSet | IdSet of 'c metaVar | SetItem of ('a, 'b, 'c) k rewrite |
    SetFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
  type ('a, 'b) irKLabel = IRKLabel of 'a label | IRIdKLabel of 'b metaVar
  type ('a, 'b, 'c) irK = KPat of ('a, 'b, 'c) irKItem list * 'c metaVar option
  and ('a, 'b, 'c) irMap =
    MapPat of (('a, 'b, 'c) irK * ('a, 'b, 'c) irK) list * 'c metaVar option
  and ('a, 'b, 'c) irSet = SetPat of ('a, 'b, 'c) irK list * 'c metaVar option
  and ('a, 'b, 'c) irList = ListPatNoVar of ('a, 'b, 'c) irK list |
    ListPat of ('a, 'b, 'c) irK list * 'c metaVar * ('a, 'b, 'c) irK list
  and ('a, 'b, 'c) irBigKWithBag = IRK of ('a, 'b, 'c) irK |
    IRList of ('a, 'b, 'c) irList | IRSet of ('a, 'b, 'c) irSet |
    IRMap of ('a, 'b, 'c) irMap | IRBag of ('a, 'b, 'c) irBag
  and ('a, 'b, 'c) irBag =
    BagPat of
      ('b var * (feature list * ('a, 'b, 'c) irBigKWithBag)) list *
        'c metaVar option
  and ('a, 'b, 'c) irBigKWithLabel = IRBigBag of ('a, 'b, 'c) irBigKWithBag |
    IRBigLabel of ('a, 'c) irKLabel
  and ('a, 'b, 'c) irKList = KListPatNoVar of ('a, 'b, 'c) irBigKWithLabel list
    | KListPat of
        ('a, 'b, 'c) irBigKWithLabel list * 'c metaVar *
          ('a, 'b, 'c) irBigKWithLabel list
  and ('a, 'b, 'c) irKItem =
    IRKItem of ('a, 'c) irKLabel * ('a, 'b, 'c) irKList * 'a sort list |
    IRIdKItem of 'c metaVar * 'a sort list | IRHOLE of 'a sort list
  type ('a, 'b, 'c) matchFactor = KLabelMatching of ('a, 'c) irKLabel |
    KItemMatching of ('a, 'b, 'c) irKItem |
    KListMatching of ('a, 'b, 'c) irKList | KMatching of ('a, 'b, 'c) irK |
    ListMatching of ('a, 'b, 'c) irList | SetMatching of ('a, 'b, 'c) irSet |
    MapMatching of ('a, 'b, 'c) irMap | BagMatching of ('a, 'b, 'c) irBag
  type ('a, 'b, 'c) pat = KLabelFunPat of 'a label * ('a, 'b, 'c) irKList |
    KFunPat of 'a label * ('a, 'b, 'c) irKList |
    KItemFunPat of 'a label * ('a, 'b, 'c) irKList |
    ListFunPat of 'a label * ('a, 'b, 'c) irKList |
    SetFunPat of 'a label * ('a, 'b, 'c) irKList |
    MapFunPat of 'a label * ('a, 'b, 'c) irKList |
    NormalPat of ('a, 'b, 'c) matchFactor
  type 'a seq
  type 'a pred
  type ('a, 'b, 'c) kRule
  type atoken = AChar of char | LBr | RBr | To | TheStar | Plus | OneOrMore
  type 'a nelist = Single of 'a | Con of 'a * 'a nelist
  type 'a symbol = NonTerminal of 'a sort | Terminal of char list
  type 'a kSyntax = Syntax of 'a sort * 'a symbol nelist * synAttrib list |
    Subsort of 'a sort * 'a sort | Token of 'a sort * reg * synAttrib list |
    ListSyntax of 'a sort * 'a sort * char list * synAttrib list
  type ('a, 'b) oneStep = Success of 'a | Failure of 'b
  type ('a, 'b, 'c) rulePat =
    FunPat of
      'a label *
        (('a, 'b, 'c) pat *
          (('a, 'b, 'c) subsFactor * ('a, 'b, 'c) suKItem)) list *
        (('a, 'b, 'c) pat *
          (('a, 'b, 'c) subsFactor * ('a, 'b, 'c) suKItem)) option
    | MacroPat of 'a label * ('a, 'b, 'c) irKList * ('a, 'b, 'c) suKFactor list
    | AnywherePat of
        'a label * ('a, 'b, 'c) irKList * ('a, 'b, 'c) suKFactor list *
          ('a, 'b, 'c) suKItem
    | KRulePat of
        ('a, 'b, 'c) irK * ('a, 'b, 'c) suKFactor list * ('a, 'b, 'c) suKItem *
          bool
    | BagRulePat of
        ('a, 'b, 'c) irBag * ('a, 'b, 'c) suB list * ('a, 'b, 'c) suKItem * bool
  type ('a, 'b, 'c) simpleK = SimId of 'c metaVar * 'a sort |
    SimTerm of 'a label * ('a, 'b, 'c) simpleK list | SimLabel of 'a label |
    SimEmpty of 'a sort |
    SimBagCon of ('a, 'b, 'c) simpleK * ('a, 'b, 'c) simpleK |
    SimBag of 'b var * feature list * ('a, 'b, 'c) simpleK
  type ruleLabel = FunTrans | AnywhereTrans | NormalTrans
  type 'a kItemSyntax = SingleTon of 'a | SetTon of ('a -> bool)
  type ('a, 'b, 'c, 'd) kModuleItem = TheSyntax of 'a kSyntax | Imports of 'c |
    TheConfiguration of ('a, 'b, 'd) bag | TheRule of ('a, 'b, 'd) kRule
  type ('a, 'b, 'c) theoryParsed =
    Parsed of
      ('a, 'b, 'c) simpleK option * ('a sort * ('a kSyntax list) list) list *
        (('a, 'b, 'c) simpleK *
          (('a, 'b, 'c) simpleK *
            (('a, 'b, 'c) simpleK * ('b, 'a) ruleAttrib list))) list
  val inc : num -> num
  val subsort : 'a equal -> 'a -> 'a -> ('a * 'a list) list -> bool
  val getValueTerm : 'a equal -> 'a -> ('a * 'b) list -> 'b option
  val irToSUInKLabel : ('a, 'b) irKLabel -> ('a, 'c, 'b) suKLabel
  val irToSUInKItem : 'a equal -> ('a, 'b, 'c) irKItem -> ('a, 'b, 'c) suKItem
  val isFunctionItem :
    'a equal -> 'a -> ('b * ('c * ('a kItemSyntax * ('d * bool)))) list -> bool
  val suToIRInKLabel :
    'a equal ->
      ('a, 'b, 'c) suKLabel ->
        ('d * ('e * ('a label kItemSyntax * ('f * bool)))) list ->
          ('a, 'b, 'c) pat option
  val getSort :
    'a equal ->
      'a -> ('b * ('c * ('a kItemSyntax * ('d * 'e)))) list -> 'b option
  val boolEvalFun :
    'a equal -> 'b equal -> 'c equal ->
      ('a, 'b, 'c) rulePat list ->
        ('a sort list *
          (('a sort list) list * ('a label kItemSyntax * ('d * bool)))) list ->
          ('a sort * 'a sort list) list ->
            ('a, 'b, 'c) suKItem -> ('a, 'b, 'c) suKItem state
  val irToSUInMatchFactor :
    'a equal -> ('a, 'b, 'c) matchFactor -> ('a, 'b, 'c) subsFactor
  val irToSUInPat :
    'a equal ->
      ('a, 'b, 'c) pat ->
        ('a sort list * ('d * ('a label kItemSyntax * ('e * 'f)))) list ->
          ('a, 'b, 'c) subsFactor
  val simpleKToIR :
    'a equal ->
      ('a, 'b, 'c) simpleK ->
        ('a sort list * ('d * ('a label kItemSyntax * ('e * bool)))) list ->
          ('a, 'b, 'c) pat option
  val simpleKToIRKList :
    'a equal ->
      ('a, 'b, 'c) simpleK list ->
        ('a sort list * ('d * ('a label kItemSyntax * ('e * bool)))) list ->
          ('a, 'b, 'c) irKList option
  val simpleKToSU :
    'a equal ->
      ('a, 'b, 'c) simpleK ->
        ('a sort list * ('d * ('a label kItemSyntax * ('e * bool)))) list ->
          ('a, 'b, 'c) subsFactor option
  val simpleKToSUKList :
    'a equal ->
      ('a, 'b, 'c) simpleK list ->
        ('a sort list * ('d * ('a label kItemSyntax * ('e * bool)))) list ->
          (('a, 'b, 'c) suKl list) option
  val formGraph : 'a equal -> 'a list -> ('a * 'a) list -> ('a * 'a list) list
  val funRuleEvalFun :
    'a equal -> 'b equal -> 'c equal ->
      ('a, 'b, 'c) rulePat list ->
        ('a sort list *
          (('a sort list) list * ('a label kItemSyntax * ('d * bool)))) list ->
          ('a sort * 'a sort list) list ->
            ('a, 'b, 'c) suB list -> (('a, 'b, 'c) suB list) state
  val tupleToRulePat :
    'a equal -> 'd equal -> 'e equal ->
      ('a, 'b, 'c) simpleK *
        (('a, 'b, 'c) simpleK *
          (('a, 'b, 'c) simpleK * ('d, 'e) ruleAttrib list)) ->
        ('a sort list * ('f * ('a label kItemSyntax * ('g * bool)))) list ->
          ('a, 'b, 'c) rulePat option
  val symbolsToKLabel : 'a symbol nelist -> 'b label
  val getKLabelName : synAttrib list -> 'a label option
  val syntaxToKItem :
    'a kSyntax ->
      (('a sort list *
         (('a sort list) list *
           ('a label kItemSyntax * (synAttrib list * bool)))) list) option
  val syntaxSetToKItemSetAux :
    'a kSyntax list ->
      'a kSyntax list ->
        (('a sort list *
           (('a sort list) list *
             ('a label kItemSyntax * (synAttrib list * bool)))) list) option
  val builtinConstTable :
    ('a sort list * ('b list * ('c label kItemSyntax * ('d list * bool)))) list
  val syntaxSetToKItems :
    'a kSyntax list ->
      (('a sort list *
         (('a sort list) list *
           ('a label kItemSyntax * (synAttrib list * bool)))) list) option
  val mergeList : ('a list) list -> 'a list
  val mergeTuples : ('a * ('b list) list) list -> 'b list
  val collectDatabase :
    ('a, 'b, 'c) theoryParsed ->
      (('a sort list *
         (('a sort list) list *
           ('a label kItemSyntax * (synAttrib list * bool)))) list) option
  val tupleToRulePats :
    'a equal -> 'd equal -> 'e equal ->
      (('a, 'b, 'c) simpleK *
        (('a, 'b, 'c) simpleK *
          (('a, 'b, 'c) simpleK * ('d, 'e) ruleAttrib list))) list ->
        ('a sort list * ('f * ('a label kItemSyntax * ('g * bool)))) list ->
          (('a, 'b, 'c) rulePat list) option
  val getAllSubsortInKFile :
    'a equal -> ('a, 'b, 'c) theoryParsed -> ('a sort * 'a sort) list
  val getKResultSubsorts :
    'a equal ->
      'a sort list -> ('a sort * 'a sort list) list -> ('b sort * 'a sort) list
  val getAllSorts : 'a equal -> 'a kSyntax list -> 'a sort list
  val preAllSubsorts :
    'a equal -> ('a, 'b, 'c) theoryParsed -> ('a sort * 'a sort) list
  val preSubsortGraph :
    'a equal -> ('a, 'b, 'c) theoryParsed -> ('a sort * 'a sort list) list
  val kResultSubsorts :
    'a equal -> ('a, 'b, 'c) theoryParsed -> ('d sort * 'a sort) list
  val allSubsorts :
    'a equal -> ('a, 'b, 'c) theoryParsed -> ('a sort * 'a sort) list
  val subsortGraph :
    'a equal -> ('a, 'b, 'c) theoryParsed -> ('a sort * 'a sort list) list
  val assignSortInRules :
    'a equal -> 'c equal ->
      (('a, 'b, 'c) simpleK *
        (('a, 'd, 'c) simpleK * (('a, 'e, 'c) simpleK * 'f))) list ->
        ((('a, 'b, 'c) simpleK *
           (('a, 'd, 'c) simpleK * (('a, 'e, 'c) simpleK * 'f))) list) option
  val suToIRInSubsFactor :
    'a equal ->
      ('a, 'b, 'c) subsFactor ->
        ('d * ('e * ('a label kItemSyntax * ('f * bool)))) list ->
          ('a, 'b, 'c) pat option
  val tupleToRuleInParsed :
    'a equal -> 'b equal -> 'c equal ->
      ('a, 'b, 'c) theoryParsed -> (('a, 'b, 'c) rulePat list) option
  val preSubsortTerms :
    'a equal -> 'd equal -> 'e equal ->
      ('a, 'b, 'c) theoryParsed ->
        ('a sort * ('a sort list * ('d * 'e))) list ->
          ('a sort * ('a sort list * ('d * 'e)) list) list
  val getNonTerminalInList : 'a symbol nelist -> 'a sort list
end = struct

type num = One | Bit0 of num | Bit1 of num;;

let rec equal_num x0 x1 = match x0, x1 with Bit0 x2, Bit1 x3 -> false
                    | Bit1 x3, Bit0 x2 -> false
                    | One, Bit1 x3 -> false
                    | Bit1 x3, One -> false
                    | One, Bit0 x2 -> false
                    | Bit0 x2, One -> false
                    | Bit1 x3, Bit1 y3 -> equal_num x3 y3
                    | Bit0 x2, Bit0 y2 -> equal_num x2 y2
                    | One, One -> true;;

type int = Zero_int | Pos of num | Neg of num;;

let rec equal_inta x0 x1 = match x0, x1 with Neg k, Neg l -> equal_num k l
                     | Neg k, Pos l -> false
                     | Neg k, Zero_int -> false
                     | Pos k, Neg l -> false
                     | Pos k, Pos l -> equal_num k l
                     | Pos k, Zero_int -> false
                     | Zero_int, Neg l -> false
                     | Zero_int, Pos l -> false
                     | Zero_int, Zero_int -> true;;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_int = ({equal = equal_inta} : int equal);;

type nat = Zero_nat | Suc of nat;;

let rec equal_nata x0 x1 = match x0, x1 with Zero_nat, Suc x2 -> false
                     | Suc x2, Zero_nat -> false
                     | Suc x2, Suc y2 -> equal_nata x2 y2
                     | Zero_nat, Zero_nat -> true;;

let equal_nat = ({equal = equal_nata} : nat equal);;

let one_nata : nat = Suc Zero_nat;;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_nat = ({one = one_nata} : nat one);;

let rec plus_nata x0 n = match x0, n with Suc m, n -> plus_nata m (Suc n)
                    | Zero_nat, n -> n;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

let plus_nat = ({plus = plus_nata} : nat plus);;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_nat = ({zero = Zero_nat} : nat zero);;

let rec eq _A a b = equal _A a b;;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({equal = equal_lista _A} : ('a list) equal);;

let rec snd (x1, x2) = x2;;

let rec minus_nat m n = match m, n with Suc m, Suc n -> minus_nat m n
                    | Zero_nat, n -> Zero_nat
                    | m, Zero_nat -> m;;

let rec less_nat m x1 = match m, x1 with m, Suc n -> less_eq_nat m n
                   | n, Zero_nat -> false
and less_eq_nat x0 n = match x0, n with Suc m, n -> less_nat m n
                  | Zero_nat, n -> true;;

let rec divmod_nat
  m n = (if equal_nata n Zero_nat || less_nat m n then (Zero_nat, m)
          else (let a = divmod_nat (minus_nat m n) n in
                let (q, aa) = a in
                 (Suc q, aa)));;

let rec modulo_nat m n = snd (divmod_nat m n);;

type char = Zero_char | Char of num;;

let rec nat_of_num
  = function Bit1 n -> (let m = nat_of_num n in Suc (plus_nata m m))
    | Bit0 n -> (let m = nat_of_num n in plus_nata m m)
    | One -> one_nata;;

let rec equal_chara
  x0 x1 = match x0, x1 with
    Char k, Zero_char ->
      equal_nata
        (modulo_nat (nat_of_num k)
          (nat_of_num
            (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))
        Zero_nat
    | Zero_char, Char k ->
        equal_nata
          (modulo_nat (nat_of_num k)
            (nat_of_num
              (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))
          Zero_nat
    | Char k, Char l ->
        equal_nata
          (modulo_nat (nat_of_num k)
            (nat_of_num
              (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))
          (modulo_nat (nat_of_num l)
            (nat_of_num
              (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))
    | Zero_char, Zero_char -> true;;

let equal_char = ({equal = equal_chara} : char equal);;

type 'a metaVar = Defined of 'a | Generated of nat | FunHole;;

type rat = Frct of (int * int);;

type real = Ratreal of rat;;

type theConstant = IntConst of int | FloatConst of real |
  StringConst of char list | BoolConst of bool | IdConst of char list;;

type 'a sort = Bool | K | KItem | KLabel | KResult | KList | List | Seta | Map |
  Bag | OtherSort of 'a | Top | Int | Float | Id | String;;

type 'a label = UnitLabel of 'a sort | ConstToLabel of theConstant | Sort |
  GetKLabel | IsKResult | AndBool | NotBool | OrBool | SetConLabel |
  SetItemLabel | ListConLabel | ListItemLabel | MapConLabel | MapItemLabel |
  MapUpdate | EqualK | NotEqualK | EqualKLabel | NotEqualKLabel |
  OtherLabel of char list | TokenLabel of char list | PlusInt | MinusInt |
  TimesInt | EqualSet | EqualMap;;

type stdType = Stdin | Stdout;;

type key = Star | Question;;

type feature = Multiplicity of key | Stream of stdType | DotDotDot;;

type 'a var = LittleK | OtherVar of 'a;;

type ('a, 'b, 'c) suBigKWithBag = SUK of ('a, 'b, 'c) suKFactor list |
  SUList of ('a, 'b, 'c) suL list | SUSet of ('a, 'b, 'c) suS list |
  SUMap of ('a, 'b, 'c) suM list | SUBag of ('a, 'b, 'c) suB list
and ('a, 'b, 'c) suB =
  ItemB of 'b var * feature list * ('a, 'b, 'c) suBigKWithBag |
  IdB of 'c metaVar
and ('a, 'b, 'c) suBigKWithLabel = SUBigBag of ('a, 'b, 'c) suBigKWithBag |
  SUBigLabel of ('a, 'b, 'c) suKLabel
and ('a, 'b, 'c) suKl = ItemKl of ('a, 'b, 'c) suBigKWithLabel |
  IdKl of 'c metaVar
and ('a, 'b, 'c) suKLabel = SUKLabel of 'a label | SUIdKLabel of 'c metaVar |
  SUKLabelFun of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
and ('a, 'b, 'c) suKItem =
  SUKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list * 'a sort list |
  SUIdKItem of 'c metaVar * 'a sort list | SUHOLE of 'a sort list
and ('a, 'b, 'c) suKFactor = ItemFactor of ('a, 'b, 'c) suKItem |
  IdFactor of 'c metaVar |
  SUKKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list * 'a sort list
and ('a, 'b, 'c) suL = ItemL of ('a, 'b, 'c) suKFactor list | IdL of 'c metaVar
  | SUListKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
and ('a, 'b, 'c) suM =
  ItemM of ('a, 'b, 'c) suKFactor list * ('a, 'b, 'c) suKFactor list |
  IdM of 'c metaVar |
  SUMapKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
and ('a, 'b, 'c) suS = ItemS of ('a, 'b, 'c) suKFactor list | IdS of 'c metaVar
  | SUSetKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list;;

let rec equal_metaVara _A
  x0 x1 = match x0, x1 with Generated x2, FunHole -> false
    | FunHole, Generated x2 -> false
    | Defined x1, FunHole -> false
    | FunHole, Defined x1 -> false
    | Defined x1, Generated x2 -> false
    | Generated x2, Defined x1 -> false
    | Generated x2, Generated y2 -> equal_nata x2 y2
    | Defined x1, Defined y1 -> eq _A x1 y1
    | FunHole, FunHole -> true;;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

let rec quotient_of (Frct x) = x;;

let rec equal_rat
  a b = equal_proda equal_int equal_int (quotient_of a) (quotient_of b);;

let rec equal_real (Ratreal x) (Ratreal y) = equal_rat x y;;

let rec equal_theConstant
  x0 x1 = match x0, x1 with BoolConst x4, IdConst x5 -> false
    | IdConst x5, BoolConst x4 -> false
    | StringConst x3, IdConst x5 -> false
    | IdConst x5, StringConst x3 -> false
    | StringConst x3, BoolConst x4 -> false
    | BoolConst x4, StringConst x3 -> false
    | FloatConst x2, IdConst x5 -> false
    | IdConst x5, FloatConst x2 -> false
    | FloatConst x2, BoolConst x4 -> false
    | BoolConst x4, FloatConst x2 -> false
    | FloatConst x2, StringConst x3 -> false
    | StringConst x3, FloatConst x2 -> false
    | IntConst x1, IdConst x5 -> false
    | IdConst x5, IntConst x1 -> false
    | IntConst x1, BoolConst x4 -> false
    | BoolConst x4, IntConst x1 -> false
    | IntConst x1, StringConst x3 -> false
    | StringConst x3, IntConst x1 -> false
    | IntConst x1, FloatConst x2 -> false
    | FloatConst x2, IntConst x1 -> false
    | IdConst x5, IdConst y5 -> equal_lista equal_char x5 y5
    | BoolConst x4, BoolConst y4 -> equal_bool x4 y4
    | StringConst x3, StringConst y3 -> equal_lista equal_char x3 y3
    | FloatConst x2, FloatConst y2 -> equal_real x2 y2
    | IntConst x1, IntConst y1 -> equal_inta x1 y1;;

let rec equal_sorta _A x0 x1 = match x0, x1 with Id, String -> false
                         | String, Id -> false
                         | Float, String -> false
                         | String, Float -> false
                         | Float, Id -> false
                         | Id, Float -> false
                         | Int, String -> false
                         | String, Int -> false
                         | Int, Id -> false
                         | Id, Int -> false
                         | Int, Float -> false
                         | Float, Int -> false
                         | Top, String -> false
                         | String, Top -> false
                         | Top, Id -> false
                         | Id, Top -> false
                         | Top, Float -> false
                         | Float, Top -> false
                         | Top, Int -> false
                         | Int, Top -> false
                         | OtherSort x11, String -> false
                         | String, OtherSort x11 -> false
                         | OtherSort x11, Id -> false
                         | Id, OtherSort x11 -> false
                         | OtherSort x11, Float -> false
                         | Float, OtherSort x11 -> false
                         | OtherSort x11, Int -> false
                         | Int, OtherSort x11 -> false
                         | OtherSort x11, Top -> false
                         | Top, OtherSort x11 -> false
                         | Bag, String -> false
                         | String, Bag -> false
                         | Bag, Id -> false
                         | Id, Bag -> false
                         | Bag, Float -> false
                         | Float, Bag -> false
                         | Bag, Int -> false
                         | Int, Bag -> false
                         | Bag, Top -> false
                         | Top, Bag -> false
                         | Bag, OtherSort x11 -> false
                         | OtherSort x11, Bag -> false
                         | Map, String -> false
                         | String, Map -> false
                         | Map, Id -> false
                         | Id, Map -> false
                         | Map, Float -> false
                         | Float, Map -> false
                         | Map, Int -> false
                         | Int, Map -> false
                         | Map, Top -> false
                         | Top, Map -> false
                         | Map, OtherSort x11 -> false
                         | OtherSort x11, Map -> false
                         | Map, Bag -> false
                         | Bag, Map -> false
                         | Seta, String -> false
                         | String, Seta -> false
                         | Seta, Id -> false
                         | Id, Seta -> false
                         | Seta, Float -> false
                         | Float, Seta -> false
                         | Seta, Int -> false
                         | Int, Seta -> false
                         | Seta, Top -> false
                         | Top, Seta -> false
                         | Seta, OtherSort x11 -> false
                         | OtherSort x11, Seta -> false
                         | Seta, Bag -> false
                         | Bag, Seta -> false
                         | Seta, Map -> false
                         | Map, Seta -> false
                         | List, String -> false
                         | String, List -> false
                         | List, Id -> false
                         | Id, List -> false
                         | List, Float -> false
                         | Float, List -> false
                         | List, Int -> false
                         | Int, List -> false
                         | List, Top -> false
                         | Top, List -> false
                         | List, OtherSort x11 -> false
                         | OtherSort x11, List -> false
                         | List, Bag -> false
                         | Bag, List -> false
                         | List, Map -> false
                         | Map, List -> false
                         | List, Seta -> false
                         | Seta, List -> false
                         | KList, String -> false
                         | String, KList -> false
                         | KList, Id -> false
                         | Id, KList -> false
                         | KList, Float -> false
                         | Float, KList -> false
                         | KList, Int -> false
                         | Int, KList -> false
                         | KList, Top -> false
                         | Top, KList -> false
                         | KList, OtherSort x11 -> false
                         | OtherSort x11, KList -> false
                         | KList, Bag -> false
                         | Bag, KList -> false
                         | KList, Map -> false
                         | Map, KList -> false
                         | KList, Seta -> false
                         | Seta, KList -> false
                         | KList, List -> false
                         | List, KList -> false
                         | KResult, String -> false
                         | String, KResult -> false
                         | KResult, Id -> false
                         | Id, KResult -> false
                         | KResult, Float -> false
                         | Float, KResult -> false
                         | KResult, Int -> false
                         | Int, KResult -> false
                         | KResult, Top -> false
                         | Top, KResult -> false
                         | KResult, OtherSort x11 -> false
                         | OtherSort x11, KResult -> false
                         | KResult, Bag -> false
                         | Bag, KResult -> false
                         | KResult, Map -> false
                         | Map, KResult -> false
                         | KResult, Seta -> false
                         | Seta, KResult -> false
                         | KResult, List -> false
                         | List, KResult -> false
                         | KResult, KList -> false
                         | KList, KResult -> false
                         | KLabel, String -> false
                         | String, KLabel -> false
                         | KLabel, Id -> false
                         | Id, KLabel -> false
                         | KLabel, Float -> false
                         | Float, KLabel -> false
                         | KLabel, Int -> false
                         | Int, KLabel -> false
                         | KLabel, Top -> false
                         | Top, KLabel -> false
                         | KLabel, OtherSort x11 -> false
                         | OtherSort x11, KLabel -> false
                         | KLabel, Bag -> false
                         | Bag, KLabel -> false
                         | KLabel, Map -> false
                         | Map, KLabel -> false
                         | KLabel, Seta -> false
                         | Seta, KLabel -> false
                         | KLabel, List -> false
                         | List, KLabel -> false
                         | KLabel, KList -> false
                         | KList, KLabel -> false
                         | KLabel, KResult -> false
                         | KResult, KLabel -> false
                         | KItem, String -> false
                         | String, KItem -> false
                         | KItem, Id -> false
                         | Id, KItem -> false
                         | KItem, Float -> false
                         | Float, KItem -> false
                         | KItem, Int -> false
                         | Int, KItem -> false
                         | KItem, Top -> false
                         | Top, KItem -> false
                         | KItem, OtherSort x11 -> false
                         | OtherSort x11, KItem -> false
                         | KItem, Bag -> false
                         | Bag, KItem -> false
                         | KItem, Map -> false
                         | Map, KItem -> false
                         | KItem, Seta -> false
                         | Seta, KItem -> false
                         | KItem, List -> false
                         | List, KItem -> false
                         | KItem, KList -> false
                         | KList, KItem -> false
                         | KItem, KResult -> false
                         | KResult, KItem -> false
                         | KItem, KLabel -> false
                         | KLabel, KItem -> false
                         | K, String -> false
                         | String, K -> false
                         | K, Id -> false
                         | Id, K -> false
                         | K, Float -> false
                         | Float, K -> false
                         | K, Int -> false
                         | Int, K -> false
                         | K, Top -> false
                         | Top, K -> false
                         | K, OtherSort x11 -> false
                         | OtherSort x11, K -> false
                         | K, Bag -> false
                         | Bag, K -> false
                         | K, Map -> false
                         | Map, K -> false
                         | K, Seta -> false
                         | Seta, K -> false
                         | K, List -> false
                         | List, K -> false
                         | K, KList -> false
                         | KList, K -> false
                         | K, KResult -> false
                         | KResult, K -> false
                         | K, KLabel -> false
                         | KLabel, K -> false
                         | K, KItem -> false
                         | KItem, K -> false
                         | Bool, String -> false
                         | String, Bool -> false
                         | Bool, Id -> false
                         | Id, Bool -> false
                         | Bool, Float -> false
                         | Float, Bool -> false
                         | Bool, Int -> false
                         | Int, Bool -> false
                         | Bool, Top -> false
                         | Top, Bool -> false
                         | Bool, OtherSort x11 -> false
                         | OtherSort x11, Bool -> false
                         | Bool, Bag -> false
                         | Bag, Bool -> false
                         | Bool, Map -> false
                         | Map, Bool -> false
                         | Bool, Seta -> false
                         | Seta, Bool -> false
                         | Bool, List -> false
                         | List, Bool -> false
                         | Bool, KList -> false
                         | KList, Bool -> false
                         | Bool, KResult -> false
                         | KResult, Bool -> false
                         | Bool, KLabel -> false
                         | KLabel, Bool -> false
                         | Bool, KItem -> false
                         | KItem, Bool -> false
                         | Bool, K -> false
                         | K, Bool -> false
                         | OtherSort x11, OtherSort y11 -> eq _A x11 y11
                         | String, String -> true
                         | Id, Id -> true
                         | Float, Float -> true
                         | Int, Int -> true
                         | Top, Top -> true
                         | Bag, Bag -> true
                         | Map, Map -> true
                         | Seta, Seta -> true
                         | List, List -> true
                         | KList, KList -> true
                         | KResult, KResult -> true
                         | KLabel, KLabel -> true
                         | KItem, KItem -> true
                         | K, K -> true
                         | Bool, Bool -> true;;

let rec equal_labela _A
  x0 x1 = match x0, x1 with EqualSet, EqualMap -> false
    | EqualMap, EqualSet -> false
    | TimesInt, EqualMap -> false
    | EqualMap, TimesInt -> false
    | TimesInt, EqualSet -> false
    | EqualSet, TimesInt -> false
    | MinusInt, EqualMap -> false
    | EqualMap, MinusInt -> false
    | MinusInt, EqualSet -> false
    | EqualSet, MinusInt -> false
    | MinusInt, TimesInt -> false
    | TimesInt, MinusInt -> false
    | PlusInt, EqualMap -> false
    | EqualMap, PlusInt -> false
    | PlusInt, EqualSet -> false
    | EqualSet, PlusInt -> false
    | PlusInt, TimesInt -> false
    | TimesInt, PlusInt -> false
    | PlusInt, MinusInt -> false
    | MinusInt, PlusInt -> false
    | TokenLabel x21, EqualMap -> false
    | EqualMap, TokenLabel x21 -> false
    | TokenLabel x21, EqualSet -> false
    | EqualSet, TokenLabel x21 -> false
    | TokenLabel x21, TimesInt -> false
    | TimesInt, TokenLabel x21 -> false
    | TokenLabel x21, MinusInt -> false
    | MinusInt, TokenLabel x21 -> false
    | TokenLabel x21, PlusInt -> false
    | PlusInt, TokenLabel x21 -> false
    | OtherLabel x20, EqualMap -> false
    | EqualMap, OtherLabel x20 -> false
    | OtherLabel x20, EqualSet -> false
    | EqualSet, OtherLabel x20 -> false
    | OtherLabel x20, TimesInt -> false
    | TimesInt, OtherLabel x20 -> false
    | OtherLabel x20, MinusInt -> false
    | MinusInt, OtherLabel x20 -> false
    | OtherLabel x20, PlusInt -> false
    | PlusInt, OtherLabel x20 -> false
    | OtherLabel x20, TokenLabel x21 -> false
    | TokenLabel x21, OtherLabel x20 -> false
    | NotEqualKLabel, EqualMap -> false
    | EqualMap, NotEqualKLabel -> false
    | NotEqualKLabel, EqualSet -> false
    | EqualSet, NotEqualKLabel -> false
    | NotEqualKLabel, TimesInt -> false
    | TimesInt, NotEqualKLabel -> false
    | NotEqualKLabel, MinusInt -> false
    | MinusInt, NotEqualKLabel -> false
    | NotEqualKLabel, PlusInt -> false
    | PlusInt, NotEqualKLabel -> false
    | NotEqualKLabel, TokenLabel x21 -> false
    | TokenLabel x21, NotEqualKLabel -> false
    | NotEqualKLabel, OtherLabel x20 -> false
    | OtherLabel x20, NotEqualKLabel -> false
    | EqualKLabel, EqualMap -> false
    | EqualMap, EqualKLabel -> false
    | EqualKLabel, EqualSet -> false
    | EqualSet, EqualKLabel -> false
    | EqualKLabel, TimesInt -> false
    | TimesInt, EqualKLabel -> false
    | EqualKLabel, MinusInt -> false
    | MinusInt, EqualKLabel -> false
    | EqualKLabel, PlusInt -> false
    | PlusInt, EqualKLabel -> false
    | EqualKLabel, TokenLabel x21 -> false
    | TokenLabel x21, EqualKLabel -> false
    | EqualKLabel, OtherLabel x20 -> false
    | OtherLabel x20, EqualKLabel -> false
    | EqualKLabel, NotEqualKLabel -> false
    | NotEqualKLabel, EqualKLabel -> false
    | NotEqualK, EqualMap -> false
    | EqualMap, NotEqualK -> false
    | NotEqualK, EqualSet -> false
    | EqualSet, NotEqualK -> false
    | NotEqualK, TimesInt -> false
    | TimesInt, NotEqualK -> false
    | NotEqualK, MinusInt -> false
    | MinusInt, NotEqualK -> false
    | NotEqualK, PlusInt -> false
    | PlusInt, NotEqualK -> false
    | NotEqualK, TokenLabel x21 -> false
    | TokenLabel x21, NotEqualK -> false
    | NotEqualK, OtherLabel x20 -> false
    | OtherLabel x20, NotEqualK -> false
    | NotEqualK, NotEqualKLabel -> false
    | NotEqualKLabel, NotEqualK -> false
    | NotEqualK, EqualKLabel -> false
    | EqualKLabel, NotEqualK -> false
    | EqualK, EqualMap -> false
    | EqualMap, EqualK -> false
    | EqualK, EqualSet -> false
    | EqualSet, EqualK -> false
    | EqualK, TimesInt -> false
    | TimesInt, EqualK -> false
    | EqualK, MinusInt -> false
    | MinusInt, EqualK -> false
    | EqualK, PlusInt -> false
    | PlusInt, EqualK -> false
    | EqualK, TokenLabel x21 -> false
    | TokenLabel x21, EqualK -> false
    | EqualK, OtherLabel x20 -> false
    | OtherLabel x20, EqualK -> false
    | EqualK, NotEqualKLabel -> false
    | NotEqualKLabel, EqualK -> false
    | EqualK, EqualKLabel -> false
    | EqualKLabel, EqualK -> false
    | EqualK, NotEqualK -> false
    | NotEqualK, EqualK -> false
    | MapUpdate, EqualMap -> false
    | EqualMap, MapUpdate -> false
    | MapUpdate, EqualSet -> false
    | EqualSet, MapUpdate -> false
    | MapUpdate, TimesInt -> false
    | TimesInt, MapUpdate -> false
    | MapUpdate, MinusInt -> false
    | MinusInt, MapUpdate -> false
    | MapUpdate, PlusInt -> false
    | PlusInt, MapUpdate -> false
    | MapUpdate, TokenLabel x21 -> false
    | TokenLabel x21, MapUpdate -> false
    | MapUpdate, OtherLabel x20 -> false
    | OtherLabel x20, MapUpdate -> false
    | MapUpdate, NotEqualKLabel -> false
    | NotEqualKLabel, MapUpdate -> false
    | MapUpdate, EqualKLabel -> false
    | EqualKLabel, MapUpdate -> false
    | MapUpdate, NotEqualK -> false
    | NotEqualK, MapUpdate -> false
    | MapUpdate, EqualK -> false
    | EqualK, MapUpdate -> false
    | MapItemLabel, EqualMap -> false
    | EqualMap, MapItemLabel -> false
    | MapItemLabel, EqualSet -> false
    | EqualSet, MapItemLabel -> false
    | MapItemLabel, TimesInt -> false
    | TimesInt, MapItemLabel -> false
    | MapItemLabel, MinusInt -> false
    | MinusInt, MapItemLabel -> false
    | MapItemLabel, PlusInt -> false
    | PlusInt, MapItemLabel -> false
    | MapItemLabel, TokenLabel x21 -> false
    | TokenLabel x21, MapItemLabel -> false
    | MapItemLabel, OtherLabel x20 -> false
    | OtherLabel x20, MapItemLabel -> false
    | MapItemLabel, NotEqualKLabel -> false
    | NotEqualKLabel, MapItemLabel -> false
    | MapItemLabel, EqualKLabel -> false
    | EqualKLabel, MapItemLabel -> false
    | MapItemLabel, NotEqualK -> false
    | NotEqualK, MapItemLabel -> false
    | MapItemLabel, EqualK -> false
    | EqualK, MapItemLabel -> false
    | MapItemLabel, MapUpdate -> false
    | MapUpdate, MapItemLabel -> false
    | MapConLabel, EqualMap -> false
    | EqualMap, MapConLabel -> false
    | MapConLabel, EqualSet -> false
    | EqualSet, MapConLabel -> false
    | MapConLabel, TimesInt -> false
    | TimesInt, MapConLabel -> false
    | MapConLabel, MinusInt -> false
    | MinusInt, MapConLabel -> false
    | MapConLabel, PlusInt -> false
    | PlusInt, MapConLabel -> false
    | MapConLabel, TokenLabel x21 -> false
    | TokenLabel x21, MapConLabel -> false
    | MapConLabel, OtherLabel x20 -> false
    | OtherLabel x20, MapConLabel -> false
    | MapConLabel, NotEqualKLabel -> false
    | NotEqualKLabel, MapConLabel -> false
    | MapConLabel, EqualKLabel -> false
    | EqualKLabel, MapConLabel -> false
    | MapConLabel, NotEqualK -> false
    | NotEqualK, MapConLabel -> false
    | MapConLabel, EqualK -> false
    | EqualK, MapConLabel -> false
    | MapConLabel, MapUpdate -> false
    | MapUpdate, MapConLabel -> false
    | MapConLabel, MapItemLabel -> false
    | MapItemLabel, MapConLabel -> false
    | ListItemLabel, EqualMap -> false
    | EqualMap, ListItemLabel -> false
    | ListItemLabel, EqualSet -> false
    | EqualSet, ListItemLabel -> false
    | ListItemLabel, TimesInt -> false
    | TimesInt, ListItemLabel -> false
    | ListItemLabel, MinusInt -> false
    | MinusInt, ListItemLabel -> false
    | ListItemLabel, PlusInt -> false
    | PlusInt, ListItemLabel -> false
    | ListItemLabel, TokenLabel x21 -> false
    | TokenLabel x21, ListItemLabel -> false
    | ListItemLabel, OtherLabel x20 -> false
    | OtherLabel x20, ListItemLabel -> false
    | ListItemLabel, NotEqualKLabel -> false
    | NotEqualKLabel, ListItemLabel -> false
    | ListItemLabel, EqualKLabel -> false
    | EqualKLabel, ListItemLabel -> false
    | ListItemLabel, NotEqualK -> false
    | NotEqualK, ListItemLabel -> false
    | ListItemLabel, EqualK -> false
    | EqualK, ListItemLabel -> false
    | ListItemLabel, MapUpdate -> false
    | MapUpdate, ListItemLabel -> false
    | ListItemLabel, MapItemLabel -> false
    | MapItemLabel, ListItemLabel -> false
    | ListItemLabel, MapConLabel -> false
    | MapConLabel, ListItemLabel -> false
    | ListConLabel, EqualMap -> false
    | EqualMap, ListConLabel -> false
    | ListConLabel, EqualSet -> false
    | EqualSet, ListConLabel -> false
    | ListConLabel, TimesInt -> false
    | TimesInt, ListConLabel -> false
    | ListConLabel, MinusInt -> false
    | MinusInt, ListConLabel -> false
    | ListConLabel, PlusInt -> false
    | PlusInt, ListConLabel -> false
    | ListConLabel, TokenLabel x21 -> false
    | TokenLabel x21, ListConLabel -> false
    | ListConLabel, OtherLabel x20 -> false
    | OtherLabel x20, ListConLabel -> false
    | ListConLabel, NotEqualKLabel -> false
    | NotEqualKLabel, ListConLabel -> false
    | ListConLabel, EqualKLabel -> false
    | EqualKLabel, ListConLabel -> false
    | ListConLabel, NotEqualK -> false
    | NotEqualK, ListConLabel -> false
    | ListConLabel, EqualK -> false
    | EqualK, ListConLabel -> false
    | ListConLabel, MapUpdate -> false
    | MapUpdate, ListConLabel -> false
    | ListConLabel, MapItemLabel -> false
    | MapItemLabel, ListConLabel -> false
    | ListConLabel, MapConLabel -> false
    | MapConLabel, ListConLabel -> false
    | ListConLabel, ListItemLabel -> false
    | ListItemLabel, ListConLabel -> false
    | SetItemLabel, EqualMap -> false
    | EqualMap, SetItemLabel -> false
    | SetItemLabel, EqualSet -> false
    | EqualSet, SetItemLabel -> false
    | SetItemLabel, TimesInt -> false
    | TimesInt, SetItemLabel -> false
    | SetItemLabel, MinusInt -> false
    | MinusInt, SetItemLabel -> false
    | SetItemLabel, PlusInt -> false
    | PlusInt, SetItemLabel -> false
    | SetItemLabel, TokenLabel x21 -> false
    | TokenLabel x21, SetItemLabel -> false
    | SetItemLabel, OtherLabel x20 -> false
    | OtherLabel x20, SetItemLabel -> false
    | SetItemLabel, NotEqualKLabel -> false
    | NotEqualKLabel, SetItemLabel -> false
    | SetItemLabel, EqualKLabel -> false
    | EqualKLabel, SetItemLabel -> false
    | SetItemLabel, NotEqualK -> false
    | NotEqualK, SetItemLabel -> false
    | SetItemLabel, EqualK -> false
    | EqualK, SetItemLabel -> false
    | SetItemLabel, MapUpdate -> false
    | MapUpdate, SetItemLabel -> false
    | SetItemLabel, MapItemLabel -> false
    | MapItemLabel, SetItemLabel -> false
    | SetItemLabel, MapConLabel -> false
    | MapConLabel, SetItemLabel -> false
    | SetItemLabel, ListItemLabel -> false
    | ListItemLabel, SetItemLabel -> false
    | SetItemLabel, ListConLabel -> false
    | ListConLabel, SetItemLabel -> false
    | SetConLabel, EqualMap -> false
    | EqualMap, SetConLabel -> false
    | SetConLabel, EqualSet -> false
    | EqualSet, SetConLabel -> false
    | SetConLabel, TimesInt -> false
    | TimesInt, SetConLabel -> false
    | SetConLabel, MinusInt -> false
    | MinusInt, SetConLabel -> false
    | SetConLabel, PlusInt -> false
    | PlusInt, SetConLabel -> false
    | SetConLabel, TokenLabel x21 -> false
    | TokenLabel x21, SetConLabel -> false
    | SetConLabel, OtherLabel x20 -> false
    | OtherLabel x20, SetConLabel -> false
    | SetConLabel, NotEqualKLabel -> false
    | NotEqualKLabel, SetConLabel -> false
    | SetConLabel, EqualKLabel -> false
    | EqualKLabel, SetConLabel -> false
    | SetConLabel, NotEqualK -> false
    | NotEqualK, SetConLabel -> false
    | SetConLabel, EqualK -> false
    | EqualK, SetConLabel -> false
    | SetConLabel, MapUpdate -> false
    | MapUpdate, SetConLabel -> false
    | SetConLabel, MapItemLabel -> false
    | MapItemLabel, SetConLabel -> false
    | SetConLabel, MapConLabel -> false
    | MapConLabel, SetConLabel -> false
    | SetConLabel, ListItemLabel -> false
    | ListItemLabel, SetConLabel -> false
    | SetConLabel, ListConLabel -> false
    | ListConLabel, SetConLabel -> false
    | SetConLabel, SetItemLabel -> false
    | SetItemLabel, SetConLabel -> false
    | OrBool, EqualMap -> false
    | EqualMap, OrBool -> false
    | OrBool, EqualSet -> false
    | EqualSet, OrBool -> false
    | OrBool, TimesInt -> false
    | TimesInt, OrBool -> false
    | OrBool, MinusInt -> false
    | MinusInt, OrBool -> false
    | OrBool, PlusInt -> false
    | PlusInt, OrBool -> false
    | OrBool, TokenLabel x21 -> false
    | TokenLabel x21, OrBool -> false
    | OrBool, OtherLabel x20 -> false
    | OtherLabel x20, OrBool -> false
    | OrBool, NotEqualKLabel -> false
    | NotEqualKLabel, OrBool -> false
    | OrBool, EqualKLabel -> false
    | EqualKLabel, OrBool -> false
    | OrBool, NotEqualK -> false
    | NotEqualK, OrBool -> false
    | OrBool, EqualK -> false
    | EqualK, OrBool -> false
    | OrBool, MapUpdate -> false
    | MapUpdate, OrBool -> false
    | OrBool, MapItemLabel -> false
    | MapItemLabel, OrBool -> false
    | OrBool, MapConLabel -> false
    | MapConLabel, OrBool -> false
    | OrBool, ListItemLabel -> false
    | ListItemLabel, OrBool -> false
    | OrBool, ListConLabel -> false
    | ListConLabel, OrBool -> false
    | OrBool, SetItemLabel -> false
    | SetItemLabel, OrBool -> false
    | OrBool, SetConLabel -> false
    | SetConLabel, OrBool -> false
    | NotBool, EqualMap -> false
    | EqualMap, NotBool -> false
    | NotBool, EqualSet -> false
    | EqualSet, NotBool -> false
    | NotBool, TimesInt -> false
    | TimesInt, NotBool -> false
    | NotBool, MinusInt -> false
    | MinusInt, NotBool -> false
    | NotBool, PlusInt -> false
    | PlusInt, NotBool -> false
    | NotBool, TokenLabel x21 -> false
    | TokenLabel x21, NotBool -> false
    | NotBool, OtherLabel x20 -> false
    | OtherLabel x20, NotBool -> false
    | NotBool, NotEqualKLabel -> false
    | NotEqualKLabel, NotBool -> false
    | NotBool, EqualKLabel -> false
    | EqualKLabel, NotBool -> false
    | NotBool, NotEqualK -> false
    | NotEqualK, NotBool -> false
    | NotBool, EqualK -> false
    | EqualK, NotBool -> false
    | NotBool, MapUpdate -> false
    | MapUpdate, NotBool -> false
    | NotBool, MapItemLabel -> false
    | MapItemLabel, NotBool -> false
    | NotBool, MapConLabel -> false
    | MapConLabel, NotBool -> false
    | NotBool, ListItemLabel -> false
    | ListItemLabel, NotBool -> false
    | NotBool, ListConLabel -> false
    | ListConLabel, NotBool -> false
    | NotBool, SetItemLabel -> false
    | SetItemLabel, NotBool -> false
    | NotBool, SetConLabel -> false
    | SetConLabel, NotBool -> false
    | NotBool, OrBool -> false
    | OrBool, NotBool -> false
    | AndBool, EqualMap -> false
    | EqualMap, AndBool -> false
    | AndBool, EqualSet -> false
    | EqualSet, AndBool -> false
    | AndBool, TimesInt -> false
    | TimesInt, AndBool -> false
    | AndBool, MinusInt -> false
    | MinusInt, AndBool -> false
    | AndBool, PlusInt -> false
    | PlusInt, AndBool -> false
    | AndBool, TokenLabel x21 -> false
    | TokenLabel x21, AndBool -> false
    | AndBool, OtherLabel x20 -> false
    | OtherLabel x20, AndBool -> false
    | AndBool, NotEqualKLabel -> false
    | NotEqualKLabel, AndBool -> false
    | AndBool, EqualKLabel -> false
    | EqualKLabel, AndBool -> false
    | AndBool, NotEqualK -> false
    | NotEqualK, AndBool -> false
    | AndBool, EqualK -> false
    | EqualK, AndBool -> false
    | AndBool, MapUpdate -> false
    | MapUpdate, AndBool -> false
    | AndBool, MapItemLabel -> false
    | MapItemLabel, AndBool -> false
    | AndBool, MapConLabel -> false
    | MapConLabel, AndBool -> false
    | AndBool, ListItemLabel -> false
    | ListItemLabel, AndBool -> false
    | AndBool, ListConLabel -> false
    | ListConLabel, AndBool -> false
    | AndBool, SetItemLabel -> false
    | SetItemLabel, AndBool -> false
    | AndBool, SetConLabel -> false
    | SetConLabel, AndBool -> false
    | AndBool, OrBool -> false
    | OrBool, AndBool -> false
    | AndBool, NotBool -> false
    | NotBool, AndBool -> false
    | IsKResult, EqualMap -> false
    | EqualMap, IsKResult -> false
    | IsKResult, EqualSet -> false
    | EqualSet, IsKResult -> false
    | IsKResult, TimesInt -> false
    | TimesInt, IsKResult -> false
    | IsKResult, MinusInt -> false
    | MinusInt, IsKResult -> false
    | IsKResult, PlusInt -> false
    | PlusInt, IsKResult -> false
    | IsKResult, TokenLabel x21 -> false
    | TokenLabel x21, IsKResult -> false
    | IsKResult, OtherLabel x20 -> false
    | OtherLabel x20, IsKResult -> false
    | IsKResult, NotEqualKLabel -> false
    | NotEqualKLabel, IsKResult -> false
    | IsKResult, EqualKLabel -> false
    | EqualKLabel, IsKResult -> false
    | IsKResult, NotEqualK -> false
    | NotEqualK, IsKResult -> false
    | IsKResult, EqualK -> false
    | EqualK, IsKResult -> false
    | IsKResult, MapUpdate -> false
    | MapUpdate, IsKResult -> false
    | IsKResult, MapItemLabel -> false
    | MapItemLabel, IsKResult -> false
    | IsKResult, MapConLabel -> false
    | MapConLabel, IsKResult -> false
    | IsKResult, ListItemLabel -> false
    | ListItemLabel, IsKResult -> false
    | IsKResult, ListConLabel -> false
    | ListConLabel, IsKResult -> false
    | IsKResult, SetItemLabel -> false
    | SetItemLabel, IsKResult -> false
    | IsKResult, SetConLabel -> false
    | SetConLabel, IsKResult -> false
    | IsKResult, OrBool -> false
    | OrBool, IsKResult -> false
    | IsKResult, NotBool -> false
    | NotBool, IsKResult -> false
    | IsKResult, AndBool -> false
    | AndBool, IsKResult -> false
    | GetKLabel, EqualMap -> false
    | EqualMap, GetKLabel -> false
    | GetKLabel, EqualSet -> false
    | EqualSet, GetKLabel -> false
    | GetKLabel, TimesInt -> false
    | TimesInt, GetKLabel -> false
    | GetKLabel, MinusInt -> false
    | MinusInt, GetKLabel -> false
    | GetKLabel, PlusInt -> false
    | PlusInt, GetKLabel -> false
    | GetKLabel, TokenLabel x21 -> false
    | TokenLabel x21, GetKLabel -> false
    | GetKLabel, OtherLabel x20 -> false
    | OtherLabel x20, GetKLabel -> false
    | GetKLabel, NotEqualKLabel -> false
    | NotEqualKLabel, GetKLabel -> false
    | GetKLabel, EqualKLabel -> false
    | EqualKLabel, GetKLabel -> false
    | GetKLabel, NotEqualK -> false
    | NotEqualK, GetKLabel -> false
    | GetKLabel, EqualK -> false
    | EqualK, GetKLabel -> false
    | GetKLabel, MapUpdate -> false
    | MapUpdate, GetKLabel -> false
    | GetKLabel, MapItemLabel -> false
    | MapItemLabel, GetKLabel -> false
    | GetKLabel, MapConLabel -> false
    | MapConLabel, GetKLabel -> false
    | GetKLabel, ListItemLabel -> false
    | ListItemLabel, GetKLabel -> false
    | GetKLabel, ListConLabel -> false
    | ListConLabel, GetKLabel -> false
    | GetKLabel, SetItemLabel -> false
    | SetItemLabel, GetKLabel -> false
    | GetKLabel, SetConLabel -> false
    | SetConLabel, GetKLabel -> false
    | GetKLabel, OrBool -> false
    | OrBool, GetKLabel -> false
    | GetKLabel, NotBool -> false
    | NotBool, GetKLabel -> false
    | GetKLabel, AndBool -> false
    | AndBool, GetKLabel -> false
    | GetKLabel, IsKResult -> false
    | IsKResult, GetKLabel -> false
    | Sort, EqualMap -> false
    | EqualMap, Sort -> false
    | Sort, EqualSet -> false
    | EqualSet, Sort -> false
    | Sort, TimesInt -> false
    | TimesInt, Sort -> false
    | Sort, MinusInt -> false
    | MinusInt, Sort -> false
    | Sort, PlusInt -> false
    | PlusInt, Sort -> false
    | Sort, TokenLabel x21 -> false
    | TokenLabel x21, Sort -> false
    | Sort, OtherLabel x20 -> false
    | OtherLabel x20, Sort -> false
    | Sort, NotEqualKLabel -> false
    | NotEqualKLabel, Sort -> false
    | Sort, EqualKLabel -> false
    | EqualKLabel, Sort -> false
    | Sort, NotEqualK -> false
    | NotEqualK, Sort -> false
    | Sort, EqualK -> false
    | EqualK, Sort -> false
    | Sort, MapUpdate -> false
    | MapUpdate, Sort -> false
    | Sort, MapItemLabel -> false
    | MapItemLabel, Sort -> false
    | Sort, MapConLabel -> false
    | MapConLabel, Sort -> false
    | Sort, ListItemLabel -> false
    | ListItemLabel, Sort -> false
    | Sort, ListConLabel -> false
    | ListConLabel, Sort -> false
    | Sort, SetItemLabel -> false
    | SetItemLabel, Sort -> false
    | Sort, SetConLabel -> false
    | SetConLabel, Sort -> false
    | Sort, OrBool -> false
    | OrBool, Sort -> false
    | Sort, NotBool -> false
    | NotBool, Sort -> false
    | Sort, AndBool -> false
    | AndBool, Sort -> false
    | Sort, IsKResult -> false
    | IsKResult, Sort -> false
    | Sort, GetKLabel -> false
    | GetKLabel, Sort -> false
    | ConstToLabel x2, EqualMap -> false
    | EqualMap, ConstToLabel x2 -> false
    | ConstToLabel x2, EqualSet -> false
    | EqualSet, ConstToLabel x2 -> false
    | ConstToLabel x2, TimesInt -> false
    | TimesInt, ConstToLabel x2 -> false
    | ConstToLabel x2, MinusInt -> false
    | MinusInt, ConstToLabel x2 -> false
    | ConstToLabel x2, PlusInt -> false
    | PlusInt, ConstToLabel x2 -> false
    | ConstToLabel x2, TokenLabel x21 -> false
    | TokenLabel x21, ConstToLabel x2 -> false
    | ConstToLabel x2, OtherLabel x20 -> false
    | OtherLabel x20, ConstToLabel x2 -> false
    | ConstToLabel x2, NotEqualKLabel -> false
    | NotEqualKLabel, ConstToLabel x2 -> false
    | ConstToLabel x2, EqualKLabel -> false
    | EqualKLabel, ConstToLabel x2 -> false
    | ConstToLabel x2, NotEqualK -> false
    | NotEqualK, ConstToLabel x2 -> false
    | ConstToLabel x2, EqualK -> false
    | EqualK, ConstToLabel x2 -> false
    | ConstToLabel x2, MapUpdate -> false
    | MapUpdate, ConstToLabel x2 -> false
    | ConstToLabel x2, MapItemLabel -> false
    | MapItemLabel, ConstToLabel x2 -> false
    | ConstToLabel x2, MapConLabel -> false
    | MapConLabel, ConstToLabel x2 -> false
    | ConstToLabel x2, ListItemLabel -> false
    | ListItemLabel, ConstToLabel x2 -> false
    | ConstToLabel x2, ListConLabel -> false
    | ListConLabel, ConstToLabel x2 -> false
    | ConstToLabel x2, SetItemLabel -> false
    | SetItemLabel, ConstToLabel x2 -> false
    | ConstToLabel x2, SetConLabel -> false
    | SetConLabel, ConstToLabel x2 -> false
    | ConstToLabel x2, OrBool -> false
    | OrBool, ConstToLabel x2 -> false
    | ConstToLabel x2, NotBool -> false
    | NotBool, ConstToLabel x2 -> false
    | ConstToLabel x2, AndBool -> false
    | AndBool, ConstToLabel x2 -> false
    | ConstToLabel x2, IsKResult -> false
    | IsKResult, ConstToLabel x2 -> false
    | ConstToLabel x2, GetKLabel -> false
    | GetKLabel, ConstToLabel x2 -> false
    | ConstToLabel x2, Sort -> false
    | Sort, ConstToLabel x2 -> false
    | UnitLabel x1, EqualMap -> false
    | EqualMap, UnitLabel x1 -> false
    | UnitLabel x1, EqualSet -> false
    | EqualSet, UnitLabel x1 -> false
    | UnitLabel x1, TimesInt -> false
    | TimesInt, UnitLabel x1 -> false
    | UnitLabel x1, MinusInt -> false
    | MinusInt, UnitLabel x1 -> false
    | UnitLabel x1, PlusInt -> false
    | PlusInt, UnitLabel x1 -> false
    | UnitLabel x1, TokenLabel x21 -> false
    | TokenLabel x21, UnitLabel x1 -> false
    | UnitLabel x1, OtherLabel x20 -> false
    | OtherLabel x20, UnitLabel x1 -> false
    | UnitLabel x1, NotEqualKLabel -> false
    | NotEqualKLabel, UnitLabel x1 -> false
    | UnitLabel x1, EqualKLabel -> false
    | EqualKLabel, UnitLabel x1 -> false
    | UnitLabel x1, NotEqualK -> false
    | NotEqualK, UnitLabel x1 -> false
    | UnitLabel x1, EqualK -> false
    | EqualK, UnitLabel x1 -> false
    | UnitLabel x1, MapUpdate -> false
    | MapUpdate, UnitLabel x1 -> false
    | UnitLabel x1, MapItemLabel -> false
    | MapItemLabel, UnitLabel x1 -> false
    | UnitLabel x1, MapConLabel -> false
    | MapConLabel, UnitLabel x1 -> false
    | UnitLabel x1, ListItemLabel -> false
    | ListItemLabel, UnitLabel x1 -> false
    | UnitLabel x1, ListConLabel -> false
    | ListConLabel, UnitLabel x1 -> false
    | UnitLabel x1, SetItemLabel -> false
    | SetItemLabel, UnitLabel x1 -> false
    | UnitLabel x1, SetConLabel -> false
    | SetConLabel, UnitLabel x1 -> false
    | UnitLabel x1, OrBool -> false
    | OrBool, UnitLabel x1 -> false
    | UnitLabel x1, NotBool -> false
    | NotBool, UnitLabel x1 -> false
    | UnitLabel x1, AndBool -> false
    | AndBool, UnitLabel x1 -> false
    | UnitLabel x1, IsKResult -> false
    | IsKResult, UnitLabel x1 -> false
    | UnitLabel x1, GetKLabel -> false
    | GetKLabel, UnitLabel x1 -> false
    | UnitLabel x1, Sort -> false
    | Sort, UnitLabel x1 -> false
    | UnitLabel x1, ConstToLabel x2 -> false
    | ConstToLabel x2, UnitLabel x1 -> false
    | TokenLabel x21, TokenLabel y21 -> equal_lista equal_char x21 y21
    | OtherLabel x20, OtherLabel y20 -> equal_lista equal_char x20 y20
    | ConstToLabel x2, ConstToLabel y2 -> equal_theConstant x2 y2
    | UnitLabel x1, UnitLabel y1 -> equal_sorta _A x1 y1
    | EqualMap, EqualMap -> true
    | EqualSet, EqualSet -> true
    | TimesInt, TimesInt -> true
    | MinusInt, MinusInt -> true
    | PlusInt, PlusInt -> true
    | NotEqualKLabel, NotEqualKLabel -> true
    | EqualKLabel, EqualKLabel -> true
    | NotEqualK, NotEqualK -> true
    | EqualK, EqualK -> true
    | MapUpdate, MapUpdate -> true
    | MapItemLabel, MapItemLabel -> true
    | MapConLabel, MapConLabel -> true
    | ListItemLabel, ListItemLabel -> true
    | ListConLabel, ListConLabel -> true
    | SetItemLabel, SetItemLabel -> true
    | SetConLabel, SetConLabel -> true
    | OrBool, OrBool -> true
    | NotBool, NotBool -> true
    | AndBool, AndBool -> true
    | IsKResult, IsKResult -> true
    | GetKLabel, GetKLabel -> true
    | Sort, Sort -> true;;

let rec equal_sort _A = ({equal = equal_sorta _A} : 'a sort equal);;

let rec equal_var _A x0 x1 = match x0, x1 with LittleK, OtherVar x2 -> false
                       | OtherVar x2, LittleK -> false
                       | OtherVar x2, OtherVar y2 -> eq _A x2 y2
                       | LittleK, LittleK -> true;;

let rec equal_stdType x0 x1 = match x0, x1 with Stdin, Stdout -> false
                        | Stdout, Stdin -> false
                        | Stdout, Stdout -> true
                        | Stdin, Stdin -> true;;

let rec equal_key x0 x1 = match x0, x1 with Star, Question -> false
                    | Question, Star -> false
                    | Question, Question -> true
                    | Star, Star -> true;;

let rec equal_featurea x0 x1 = match x0, x1 with Stream x2, DotDotDot -> false
                         | DotDotDot, Stream x2 -> false
                         | Multiplicity x1, DotDotDot -> false
                         | DotDotDot, Multiplicity x1 -> false
                         | Multiplicity x1, Stream x2 -> false
                         | Stream x2, Multiplicity x1 -> false
                         | Stream x2, Stream y2 -> equal_stdType x2 y2
                         | Multiplicity x1, Multiplicity y1 -> equal_key x1 y1
                         | DotDotDot, DotDotDot -> true;;

let equal_feature = ({equal = equal_featurea} : feature equal);;

let rec equal_suB _A _B _C =
  ({equal = equal_suBa _A _B _C} : ('a, 'b, 'c) suB equal)
and equal_suBigKWithBag _A _B _C
  x0 x1 = match x0, x1 with SUMap x4, SUBag x5 -> false
    | SUBag x5, SUMap x4 -> false
    | SUSet x3, SUBag x5 -> false
    | SUBag x5, SUSet x3 -> false
    | SUSet x3, SUMap x4 -> false
    | SUMap x4, SUSet x3 -> false
    | SUList x2, SUBag x5 -> false
    | SUBag x5, SUList x2 -> false
    | SUList x2, SUMap x4 -> false
    | SUMap x4, SUList x2 -> false
    | SUList x2, SUSet x3 -> false
    | SUSet x3, SUList x2 -> false
    | SUK x1, SUBag x5 -> false
    | SUBag x5, SUK x1 -> false
    | SUK x1, SUMap x4 -> false
    | SUMap x4, SUK x1 -> false
    | SUK x1, SUSet x3 -> false
    | SUSet x3, SUK x1 -> false
    | SUK x1, SUList x2 -> false
    | SUList x2, SUK x1 -> false
    | SUBag x5, SUBag y5 -> equal_lista (equal_suB _A _B _C) x5 y5
    | SUMap x4, SUMap y4 -> equal_lista (equal_suM _A _B _C) x4 y4
    | SUSet x3, SUSet y3 -> equal_lista (equal_suS _A _B _C) x3 y3
    | SUList x2, SUList y2 -> equal_lista (equal_suL _A _B _C) x2 y2
    | SUK x1, SUK y1 -> equal_lista (equal_suKFactor _A _B _C) x1 y1
and equal_suBa _A _B _C
  x0 x1 = match x0, x1 with ItemB (x11, x12, x13), IdB x2 -> false
    | IdB x2, ItemB (x11, x12, x13) -> false
    | IdB x2, IdB y2 -> equal_metaVara _C x2 y2
    | ItemB (x11, x12, x13), ItemB (y11, y12, y13) ->
        equal_var _B x11 y11 &&
          (equal_lista equal_feature x12 y12 &&
            equal_suBigKWithBag _A _B _C x13 y13)
and equal_suBigKWithLabel _A _B _C
  x0 x1 = match x0, x1 with SUBigBag x1, SUBigLabel x2 -> false
    | SUBigLabel x2, SUBigBag x1 -> false
    | SUBigLabel x2, SUBigLabel y2 -> equal_suKLabel _A _B _C x2 y2
    | SUBigBag x1, SUBigBag y1 -> equal_suBigKWithBag _A _B _C x1 y1
and equal_suKla _A _B _C
  x0 x1 = match x0, x1 with ItemKl x1, IdKl x2 -> false
    | IdKl x2, ItemKl x1 -> false
    | IdKl x2, IdKl y2 -> equal_metaVara _C x2 y2
    | ItemKl x1, ItemKl y1 -> equal_suBigKWithLabel _A _B _C x1 y1
and equal_suKl _A _B _C =
  ({equal = equal_suKla _A _B _C} : ('a, 'b, 'c) suKl equal)
and equal_suKLabel _A _B _C
  x0 x1 = match x0, x1 with SUIdKLabel x2, SUKLabelFun (x31, x32) -> false
    | SUKLabelFun (x31, x32), SUIdKLabel x2 -> false
    | SUKLabel x1, SUKLabelFun (x31, x32) -> false
    | SUKLabelFun (x31, x32), SUKLabel x1 -> false
    | SUKLabel x1, SUIdKLabel x2 -> false
    | SUIdKLabel x2, SUKLabel x1 -> false
    | SUKLabelFun (x31, x32), SUKLabelFun (y31, y32) ->
        equal_suKLabel _A _B _C x31 y31 &&
          equal_lista (equal_suKl _A _B _C) x32 y32
    | SUIdKLabel x2, SUIdKLabel y2 -> equal_metaVara _C x2 y2
    | SUKLabel x1, SUKLabel y1 -> equal_labela _A x1 y1
and equal_suKItema _A _B _C
  x0 x1 = match x0, x1 with SUIdKItem (x21, x22), SUHOLE x3 -> false
    | SUHOLE x3, SUIdKItem (x21, x22) -> false
    | SUKItem (x11, x12, x13), SUHOLE x3 -> false
    | SUHOLE x3, SUKItem (x11, x12, x13) -> false
    | SUKItem (x11, x12, x13), SUIdKItem (x21, x22) -> false
    | SUIdKItem (x21, x22), SUKItem (x11, x12, x13) -> false
    | SUHOLE x3, SUHOLE y3 -> equal_lista (equal_sort _A) x3 y3
    | SUIdKItem (x21, x22), SUIdKItem (y21, y22) ->
        equal_metaVara _C x21 y21 && equal_lista (equal_sort _A) x22 y22
    | SUKItem (x11, x12, x13), SUKItem (y11, y12, y13) ->
        equal_suKLabel _A _B _C x11 y11 &&
          (equal_lista (equal_suKl _A _B _C) x12 y12 &&
            equal_lista (equal_sort _A) x13 y13)
and equal_suKFactora _A _B _C
  x0 x1 = match x0, x1 with IdFactor x2, SUKKItem (x31, x32, x33) -> false
    | SUKKItem (x31, x32, x33), IdFactor x2 -> false
    | ItemFactor x1, SUKKItem (x31, x32, x33) -> false
    | SUKKItem (x31, x32, x33), ItemFactor x1 -> false
    | ItemFactor x1, IdFactor x2 -> false
    | IdFactor x2, ItemFactor x1 -> false
    | SUKKItem (x31, x32, x33), SUKKItem (y31, y32, y33) ->
        equal_suKLabel _A _B _C x31 y31 &&
          (equal_lista (equal_suKl _A _B _C) x32 y32 &&
            equal_lista (equal_sort _A) x33 y33)
    | IdFactor x2, IdFactor y2 -> equal_metaVara _C x2 y2
    | ItemFactor x1, ItemFactor y1 -> equal_suKItema _A _B _C x1 y1
and equal_suKFactor _A _B _C =
  ({equal = equal_suKFactora _A _B _C} : ('a, 'b, 'c) suKFactor equal)
and equal_suLa _A _B _C
  x0 x1 = match x0, x1 with IdL x2, SUListKItem (x31, x32) -> false
    | SUListKItem (x31, x32), IdL x2 -> false
    | ItemL x1, SUListKItem (x31, x32) -> false
    | SUListKItem (x31, x32), ItemL x1 -> false
    | ItemL x1, IdL x2 -> false
    | IdL x2, ItemL x1 -> false
    | SUListKItem (x31, x32), SUListKItem (y31, y32) ->
        equal_suKLabel _A _B _C x31 y31 &&
          equal_lista (equal_suKl _A _B _C) x32 y32
    | IdL x2, IdL y2 -> equal_metaVara _C x2 y2
    | ItemL x1, ItemL y1 -> equal_lista (equal_suKFactor _A _B _C) x1 y1
and equal_suL _A _B _C =
  ({equal = equal_suLa _A _B _C} : ('a, 'b, 'c) suL equal)
and equal_suMa _A _B _C
  x0 x1 = match x0, x1 with IdM x2, SUMapKItem (x31, x32) -> false
    | SUMapKItem (x31, x32), IdM x2 -> false
    | ItemM (x11, x12), SUMapKItem (x31, x32) -> false
    | SUMapKItem (x31, x32), ItemM (x11, x12) -> false
    | ItemM (x11, x12), IdM x2 -> false
    | IdM x2, ItemM (x11, x12) -> false
    | SUMapKItem (x31, x32), SUMapKItem (y31, y32) ->
        equal_suKLabel _A _B _C x31 y31 &&
          equal_lista (equal_suKl _A _B _C) x32 y32
    | IdM x2, IdM y2 -> equal_metaVara _C x2 y2
    | ItemM (x11, x12), ItemM (y11, y12) ->
        equal_lista (equal_suKFactor _A _B _C) x11 y11 &&
          equal_lista (equal_suKFactor _A _B _C) x12 y12
and equal_suM _A _B _C =
  ({equal = equal_suMa _A _B _C} : ('a, 'b, 'c) suM equal)
and equal_suSa _A _B _C
  x0 x1 = match x0, x1 with IdS x2, SUSetKItem (x31, x32) -> false
    | SUSetKItem (x31, x32), IdS x2 -> false
    | ItemS x1, SUSetKItem (x31, x32) -> false
    | SUSetKItem (x31, x32), ItemS x1 -> false
    | ItemS x1, IdS x2 -> false
    | IdS x2, ItemS x1 -> false
    | SUSetKItem (x31, x32), SUSetKItem (y31, y32) ->
        equal_suKLabel _A _B _C x31 y31 &&
          equal_lista (equal_suKl _A _B _C) x32 y32
    | IdS x2, IdS y2 -> equal_metaVara _C x2 y2
    | ItemS x1, ItemS y1 -> equal_lista (equal_suKFactor _A _B _C) x1 y1
and equal_suS _A _B _C =
  ({equal = equal_suSa _A _B _C} : ('a, 'b, 'c) suS equal);;

let rec equal_optiona _A x0 x1 = match x0, x1 with None, Some x2 -> false
                           | Some x2, None -> false
                           | Some x2, Some y2 -> eq _A x2 y2
                           | None, None -> true;;

let rec equal_option _A = ({equal = equal_optiona _A} : ('a option) equal);;

let rec equal_label _A = ({equal = equal_labela _A} : 'a label equal);;

type 'a state = Continue of 'a | Stop of 'a | Div of 'a;;

let rec equal_statea _A x0 x1 = match x0, x1 with Stop x2, Div x3 -> false
                          | Div x3, Stop x2 -> false
                          | Continue x1, Div x3 -> false
                          | Div x3, Continue x1 -> false
                          | Continue x1, Stop x2 -> false
                          | Stop x2, Continue x1 -> false
                          | Div x3, Div y3 -> eq _A x3 y3
                          | Stop x2, Stop y2 -> eq _A x2 y2
                          | Continue x1, Continue y1 -> eq _A x1 y1;;

let rec equal_state _A = ({equal = equal_statea _A} : 'a state equal);;

let rec equal_metaVar _A = ({equal = equal_metaVara _A} : 'a metaVar equal);;

let rec equal_suKItem _A _B _C =
  ({equal = equal_suKItema _A _B _C} : ('a, 'b, 'c) suKItem equal);;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

type reg = Eps | Sym of char | Alt of reg * reg | TheSeq of reg * reg |
  Rep of reg;;

let rec equal_reg
  x0 x1 = match x0, x1 with TheSeq (x41, x42), Rep x5 -> false
    | Rep x5, TheSeq (x41, x42) -> false
    | Alt (x31, x32), Rep x5 -> false
    | Rep x5, Alt (x31, x32) -> false
    | Alt (x31, x32), TheSeq (x41, x42) -> false
    | TheSeq (x41, x42), Alt (x31, x32) -> false
    | Sym x2, Rep x5 -> false
    | Rep x5, Sym x2 -> false
    | Sym x2, TheSeq (x41, x42) -> false
    | TheSeq (x41, x42), Sym x2 -> false
    | Sym x2, Alt (x31, x32) -> false
    | Alt (x31, x32), Sym x2 -> false
    | Eps, Rep x5 -> false
    | Rep x5, Eps -> false
    | Eps, TheSeq (x41, x42) -> false
    | TheSeq (x41, x42), Eps -> false
    | Eps, Alt (x31, x32) -> false
    | Alt (x31, x32), Eps -> false
    | Eps, Sym x2 -> false
    | Sym x2, Eps -> false
    | Rep x5, Rep y5 -> equal_reg x5 y5
    | TheSeq (x41, x42), TheSeq (y41, y42) ->
        equal_reg x41 y41 && equal_reg x42 y42
    | Alt (x31, x32), Alt (y31, y32) -> equal_reg x31 y31 && equal_reg x32 y32
    | Sym x2, Sym y2 -> equal_chara x2 y2
    | Eps, Eps -> true;;

type synAttrib = Strict of nat list | Seqstrict | Left | Right |
  Hook of char list | Function | Klabel of char list | Bracket | Tokena | Avoid
  | OnlyLabel | NotInRules | Regex of reg | NonAssoc |
  OtherSynAttr of char list;;

let rec equal_synAttriba
  x0 x1 = match x0, x1 with NonAssoc, OtherSynAttr x15 -> false
    | OtherSynAttr x15, NonAssoc -> false
    | Regex x13, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Regex x13 -> false
    | Regex x13, NonAssoc -> false
    | NonAssoc, Regex x13 -> false
    | NotInRules, OtherSynAttr x15 -> false
    | OtherSynAttr x15, NotInRules -> false
    | NotInRules, NonAssoc -> false
    | NonAssoc, NotInRules -> false
    | NotInRules, Regex x13 -> false
    | Regex x13, NotInRules -> false
    | OnlyLabel, OtherSynAttr x15 -> false
    | OtherSynAttr x15, OnlyLabel -> false
    | OnlyLabel, NonAssoc -> false
    | NonAssoc, OnlyLabel -> false
    | OnlyLabel, Regex x13 -> false
    | Regex x13, OnlyLabel -> false
    | OnlyLabel, NotInRules -> false
    | NotInRules, OnlyLabel -> false
    | Avoid, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Avoid -> false
    | Avoid, NonAssoc -> false
    | NonAssoc, Avoid -> false
    | Avoid, Regex x13 -> false
    | Regex x13, Avoid -> false
    | Avoid, NotInRules -> false
    | NotInRules, Avoid -> false
    | Avoid, OnlyLabel -> false
    | OnlyLabel, Avoid -> false
    | Tokena, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Tokena -> false
    | Tokena, NonAssoc -> false
    | NonAssoc, Tokena -> false
    | Tokena, Regex x13 -> false
    | Regex x13, Tokena -> false
    | Tokena, NotInRules -> false
    | NotInRules, Tokena -> false
    | Tokena, OnlyLabel -> false
    | OnlyLabel, Tokena -> false
    | Tokena, Avoid -> false
    | Avoid, Tokena -> false
    | Bracket, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Bracket -> false
    | Bracket, NonAssoc -> false
    | NonAssoc, Bracket -> false
    | Bracket, Regex x13 -> false
    | Regex x13, Bracket -> false
    | Bracket, NotInRules -> false
    | NotInRules, Bracket -> false
    | Bracket, OnlyLabel -> false
    | OnlyLabel, Bracket -> false
    | Bracket, Avoid -> false
    | Avoid, Bracket -> false
    | Bracket, Tokena -> false
    | Tokena, Bracket -> false
    | Klabel x7, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Klabel x7 -> false
    | Klabel x7, NonAssoc -> false
    | NonAssoc, Klabel x7 -> false
    | Klabel x7, Regex x13 -> false
    | Regex x13, Klabel x7 -> false
    | Klabel x7, NotInRules -> false
    | NotInRules, Klabel x7 -> false
    | Klabel x7, OnlyLabel -> false
    | OnlyLabel, Klabel x7 -> false
    | Klabel x7, Avoid -> false
    | Avoid, Klabel x7 -> false
    | Klabel x7, Tokena -> false
    | Tokena, Klabel x7 -> false
    | Klabel x7, Bracket -> false
    | Bracket, Klabel x7 -> false
    | Function, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Function -> false
    | Function, NonAssoc -> false
    | NonAssoc, Function -> false
    | Function, Regex x13 -> false
    | Regex x13, Function -> false
    | Function, NotInRules -> false
    | NotInRules, Function -> false
    | Function, OnlyLabel -> false
    | OnlyLabel, Function -> false
    | Function, Avoid -> false
    | Avoid, Function -> false
    | Function, Tokena -> false
    | Tokena, Function -> false
    | Function, Bracket -> false
    | Bracket, Function -> false
    | Function, Klabel x7 -> false
    | Klabel x7, Function -> false
    | Hook x5, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Hook x5 -> false
    | Hook x5, NonAssoc -> false
    | NonAssoc, Hook x5 -> false
    | Hook x5, Regex x13 -> false
    | Regex x13, Hook x5 -> false
    | Hook x5, NotInRules -> false
    | NotInRules, Hook x5 -> false
    | Hook x5, OnlyLabel -> false
    | OnlyLabel, Hook x5 -> false
    | Hook x5, Avoid -> false
    | Avoid, Hook x5 -> false
    | Hook x5, Tokena -> false
    | Tokena, Hook x5 -> false
    | Hook x5, Bracket -> false
    | Bracket, Hook x5 -> false
    | Hook x5, Klabel x7 -> false
    | Klabel x7, Hook x5 -> false
    | Hook x5, Function -> false
    | Function, Hook x5 -> false
    | Right, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Right -> false
    | Right, NonAssoc -> false
    | NonAssoc, Right -> false
    | Right, Regex x13 -> false
    | Regex x13, Right -> false
    | Right, NotInRules -> false
    | NotInRules, Right -> false
    | Right, OnlyLabel -> false
    | OnlyLabel, Right -> false
    | Right, Avoid -> false
    | Avoid, Right -> false
    | Right, Tokena -> false
    | Tokena, Right -> false
    | Right, Bracket -> false
    | Bracket, Right -> false
    | Right, Klabel x7 -> false
    | Klabel x7, Right -> false
    | Right, Function -> false
    | Function, Right -> false
    | Right, Hook x5 -> false
    | Hook x5, Right -> false
    | Left, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Left -> false
    | Left, NonAssoc -> false
    | NonAssoc, Left -> false
    | Left, Regex x13 -> false
    | Regex x13, Left -> false
    | Left, NotInRules -> false
    | NotInRules, Left -> false
    | Left, OnlyLabel -> false
    | OnlyLabel, Left -> false
    | Left, Avoid -> false
    | Avoid, Left -> false
    | Left, Tokena -> false
    | Tokena, Left -> false
    | Left, Bracket -> false
    | Bracket, Left -> false
    | Left, Klabel x7 -> false
    | Klabel x7, Left -> false
    | Left, Function -> false
    | Function, Left -> false
    | Left, Hook x5 -> false
    | Hook x5, Left -> false
    | Left, Right -> false
    | Right, Left -> false
    | Seqstrict, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Seqstrict -> false
    | Seqstrict, NonAssoc -> false
    | NonAssoc, Seqstrict -> false
    | Seqstrict, Regex x13 -> false
    | Regex x13, Seqstrict -> false
    | Seqstrict, NotInRules -> false
    | NotInRules, Seqstrict -> false
    | Seqstrict, OnlyLabel -> false
    | OnlyLabel, Seqstrict -> false
    | Seqstrict, Avoid -> false
    | Avoid, Seqstrict -> false
    | Seqstrict, Tokena -> false
    | Tokena, Seqstrict -> false
    | Seqstrict, Bracket -> false
    | Bracket, Seqstrict -> false
    | Seqstrict, Klabel x7 -> false
    | Klabel x7, Seqstrict -> false
    | Seqstrict, Function -> false
    | Function, Seqstrict -> false
    | Seqstrict, Hook x5 -> false
    | Hook x5, Seqstrict -> false
    | Seqstrict, Right -> false
    | Right, Seqstrict -> false
    | Seqstrict, Left -> false
    | Left, Seqstrict -> false
    | Strict x1, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Strict x1 -> false
    | Strict x1, NonAssoc -> false
    | NonAssoc, Strict x1 -> false
    | Strict x1, Regex x13 -> false
    | Regex x13, Strict x1 -> false
    | Strict x1, NotInRules -> false
    | NotInRules, Strict x1 -> false
    | Strict x1, OnlyLabel -> false
    | OnlyLabel, Strict x1 -> false
    | Strict x1, Avoid -> false
    | Avoid, Strict x1 -> false
    | Strict x1, Tokena -> false
    | Tokena, Strict x1 -> false
    | Strict x1, Bracket -> false
    | Bracket, Strict x1 -> false
    | Strict x1, Klabel x7 -> false
    | Klabel x7, Strict x1 -> false
    | Strict x1, Function -> false
    | Function, Strict x1 -> false
    | Strict x1, Hook x5 -> false
    | Hook x5, Strict x1 -> false
    | Strict x1, Right -> false
    | Right, Strict x1 -> false
    | Strict x1, Left -> false
    | Left, Strict x1 -> false
    | Strict x1, Seqstrict -> false
    | Seqstrict, Strict x1 -> false
    | OtherSynAttr x15, OtherSynAttr y15 -> equal_lista equal_char x15 y15
    | Regex x13, Regex y13 -> equal_reg x13 y13
    | Klabel x7, Klabel y7 -> equal_lista equal_char x7 y7
    | Hook x5, Hook y5 -> equal_lista equal_char x5 y5
    | Strict x1, Strict y1 -> equal_lista equal_nat x1 y1
    | NonAssoc, NonAssoc -> true
    | NotInRules, NotInRules -> true
    | OnlyLabel, OnlyLabel -> true
    | Avoid, Avoid -> true
    | Tokena, Tokena -> true
    | Bracket, Bracket -> true
    | Function, Function -> true
    | Right, Right -> true
    | Left, Left -> true
    | Seqstrict, Seqstrict -> true;;

let equal_synAttrib = ({equal = equal_synAttriba} : synAttrib equal);;

type ('a, 'b) ruleAttrib = Attr of 'a | Heat | Cool | Transition | Anywhere |
  Structural | Owise | Macro | Result of 'b sort;;

let rec equal_ruleAttriba _A _B
  x0 x1 = match x0, x1 with Macro, Result x9 -> false
    | Result x9, Macro -> false
    | Owise, Result x9 -> false
    | Result x9, Owise -> false
    | Owise, Macro -> false
    | Macro, Owise -> false
    | Structural, Result x9 -> false
    | Result x9, Structural -> false
    | Structural, Macro -> false
    | Macro, Structural -> false
    | Structural, Owise -> false
    | Owise, Structural -> false
    | Anywhere, Result x9 -> false
    | Result x9, Anywhere -> false
    | Anywhere, Macro -> false
    | Macro, Anywhere -> false
    | Anywhere, Owise -> false
    | Owise, Anywhere -> false
    | Anywhere, Structural -> false
    | Structural, Anywhere -> false
    | Transition, Result x9 -> false
    | Result x9, Transition -> false
    | Transition, Macro -> false
    | Macro, Transition -> false
    | Transition, Owise -> false
    | Owise, Transition -> false
    | Transition, Structural -> false
    | Structural, Transition -> false
    | Transition, Anywhere -> false
    | Anywhere, Transition -> false
    | Cool, Result x9 -> false
    | Result x9, Cool -> false
    | Cool, Macro -> false
    | Macro, Cool -> false
    | Cool, Owise -> false
    | Owise, Cool -> false
    | Cool, Structural -> false
    | Structural, Cool -> false
    | Cool, Anywhere -> false
    | Anywhere, Cool -> false
    | Cool, Transition -> false
    | Transition, Cool -> false
    | Heat, Result x9 -> false
    | Result x9, Heat -> false
    | Heat, Macro -> false
    | Macro, Heat -> false
    | Heat, Owise -> false
    | Owise, Heat -> false
    | Heat, Structural -> false
    | Structural, Heat -> false
    | Heat, Anywhere -> false
    | Anywhere, Heat -> false
    | Heat, Transition -> false
    | Transition, Heat -> false
    | Heat, Cool -> false
    | Cool, Heat -> false
    | Attr x1, Result x9 -> false
    | Result x9, Attr x1 -> false
    | Attr x1, Macro -> false
    | Macro, Attr x1 -> false
    | Attr x1, Owise -> false
    | Owise, Attr x1 -> false
    | Attr x1, Structural -> false
    | Structural, Attr x1 -> false
    | Attr x1, Anywhere -> false
    | Anywhere, Attr x1 -> false
    | Attr x1, Transition -> false
    | Transition, Attr x1 -> false
    | Attr x1, Cool -> false
    | Cool, Attr x1 -> false
    | Attr x1, Heat -> false
    | Heat, Attr x1 -> false
    | Result x9, Result y9 -> equal_sorta _B x9 y9
    | Attr x1, Attr y1 -> eq _A x1 y1
    | Macro, Macro -> true
    | Owise, Owise -> true
    | Structural, Structural -> true
    | Anywhere, Anywhere -> true
    | Transition, Transition -> true
    | Cool, Cool -> true
    | Heat, Heat -> true;;

let rec equal_ruleAttrib _A _B =
  ({equal = equal_ruleAttriba _A _B} : ('a, 'b) ruleAttrib equal);;

type ('a, 'b, 'c) subsFactor = KLabelSubs of ('a, 'b, 'c) suKLabel |
  KItemSubs of ('a, 'b, 'c) suKItem | KListSubs of ('a, 'b, 'c) suKl list |
  KSubs of ('a, 'b, 'c) suKFactor list | ListSubs of ('a, 'b, 'c) suL list |
  SetSubs of ('a, 'b, 'c) suS list | MapSubs of ('a, 'b, 'c) suM list |
  BagSubs of ('a, 'b, 'c) suB list;;

let rec equal_subsFactora _A _B _C
  x0 x1 = match x0, x1 with MapSubs x7, BagSubs x8 -> false
    | BagSubs x8, MapSubs x7 -> false
    | SetSubs x6, BagSubs x8 -> false
    | BagSubs x8, SetSubs x6 -> false
    | SetSubs x6, MapSubs x7 -> false
    | MapSubs x7, SetSubs x6 -> false
    | ListSubs x5, BagSubs x8 -> false
    | BagSubs x8, ListSubs x5 -> false
    | ListSubs x5, MapSubs x7 -> false
    | MapSubs x7, ListSubs x5 -> false
    | ListSubs x5, SetSubs x6 -> false
    | SetSubs x6, ListSubs x5 -> false
    | KSubs x4, BagSubs x8 -> false
    | BagSubs x8, KSubs x4 -> false
    | KSubs x4, MapSubs x7 -> false
    | MapSubs x7, KSubs x4 -> false
    | KSubs x4, SetSubs x6 -> false
    | SetSubs x6, KSubs x4 -> false
    | KSubs x4, ListSubs x5 -> false
    | ListSubs x5, KSubs x4 -> false
    | KListSubs x3, BagSubs x8 -> false
    | BagSubs x8, KListSubs x3 -> false
    | KListSubs x3, MapSubs x7 -> false
    | MapSubs x7, KListSubs x3 -> false
    | KListSubs x3, SetSubs x6 -> false
    | SetSubs x6, KListSubs x3 -> false
    | KListSubs x3, ListSubs x5 -> false
    | ListSubs x5, KListSubs x3 -> false
    | KListSubs x3, KSubs x4 -> false
    | KSubs x4, KListSubs x3 -> false
    | KItemSubs x2, BagSubs x8 -> false
    | BagSubs x8, KItemSubs x2 -> false
    | KItemSubs x2, MapSubs x7 -> false
    | MapSubs x7, KItemSubs x2 -> false
    | KItemSubs x2, SetSubs x6 -> false
    | SetSubs x6, KItemSubs x2 -> false
    | KItemSubs x2, ListSubs x5 -> false
    | ListSubs x5, KItemSubs x2 -> false
    | KItemSubs x2, KSubs x4 -> false
    | KSubs x4, KItemSubs x2 -> false
    | KItemSubs x2, KListSubs x3 -> false
    | KListSubs x3, KItemSubs x2 -> false
    | KLabelSubs x1, BagSubs x8 -> false
    | BagSubs x8, KLabelSubs x1 -> false
    | KLabelSubs x1, MapSubs x7 -> false
    | MapSubs x7, KLabelSubs x1 -> false
    | KLabelSubs x1, SetSubs x6 -> false
    | SetSubs x6, KLabelSubs x1 -> false
    | KLabelSubs x1, ListSubs x5 -> false
    | ListSubs x5, KLabelSubs x1 -> false
    | KLabelSubs x1, KSubs x4 -> false
    | KSubs x4, KLabelSubs x1 -> false
    | KLabelSubs x1, KListSubs x3 -> false
    | KListSubs x3, KLabelSubs x1 -> false
    | KLabelSubs x1, KItemSubs x2 -> false
    | KItemSubs x2, KLabelSubs x1 -> false
    | BagSubs x8, BagSubs y8 -> equal_lista (equal_suB _A _B _C) x8 y8
    | MapSubs x7, MapSubs y7 -> equal_lista (equal_suM _A _B _C) x7 y7
    | SetSubs x6, SetSubs y6 -> equal_lista (equal_suS _A _B _C) x6 y6
    | ListSubs x5, ListSubs y5 -> equal_lista (equal_suL _A _B _C) x5 y5
    | KSubs x4, KSubs y4 -> equal_lista (equal_suKFactor _A _B _C) x4 y4
    | KListSubs x3, KListSubs y3 -> equal_lista (equal_suKl _A _B _C) x3 y3
    | KItemSubs x2, KItemSubs y2 -> equal_suKItema _A _B _C x2 y2
    | KLabelSubs x1, KLabelSubs y1 -> equal_suKLabel _A _B _C x1 y1;;

let rec equal_subsFactor _A _B _C =
  ({equal = equal_subsFactora _A _B _C} : ('a, 'b, 'c) subsFactor equal);;

type 'a set = Set of 'a list | Coset of 'a list;;

type 'a rewrite = KTerm of 'a | KRewrite of 'a * 'a;;

type ('a, 'b, 'c) k = Tilda of ('a, 'b, 'c) k rewrite * ('a, 'b, 'c) k rewrite |
  UnitK | IdK of 'c metaVar | SingleK of ('a, 'b, 'c) kItem rewrite |
  KFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
and ('a, 'b, 'c) theList =
  ListCon of ('a, 'b, 'c) theList rewrite * ('a, 'b, 'c) theList rewrite |
  UnitList | IdList of 'c metaVar | ListItem of ('a, 'b, 'c) k rewrite |
  ListFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
and ('a, 'b, 'c) bigK = TheK of ('a, 'b, 'c) k rewrite |
  TheList of ('a, 'b, 'c) theList rewrite |
  TheSet of ('a, 'b, 'c) theSet rewrite | TheMap of ('a, 'b, 'c) theMap rewrite
and ('a, 'b, 'c) bag =
  BagCon of ('a, 'b, 'c) bag rewrite * ('a, 'b, 'c) bag rewrite | UnitBag |
  IdBag of 'c metaVar | Xml of 'b var * feature list * ('a, 'b, 'c) bag rewrite
  | SingleCell of 'b var * feature list * ('a, 'b, 'c) bigK
and ('a, 'b, 'c) bigKWithBag = TheBigK of ('a, 'b, 'c) bigK |
  TheBigBag of ('a, 'b, 'c) bag rewrite |
  TheLabel of ('a, 'b, 'c) kLabel rewrite
and ('a, 'b, 'c) kList =
  KListCon of ('a, 'b, 'c) kList rewrite * ('a, 'b, 'c) kList rewrite |
  UnitKList | KListItem of ('a, 'b, 'c) bigKWithBag | IdKList of 'c metaVar
and ('a, 'b, 'c) kLabel = KLabelC of 'a label |
  KLabelFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite |
  IdKLabel of 'c metaVar
and ('a, 'b, 'c) kItem =
  KItemC of ('a, 'b, 'c) kLabel rewrite * ('a, 'b, 'c) kList rewrite * 'a sort |
  Constant of theConstant * 'a sort | IdKItem of 'c metaVar * 'a sort |
  HOLE of 'a sort
and ('a, 'b, 'c) theMap =
  MapCon of ('a, 'b, 'c) theMap rewrite * ('a, 'b, 'c) theMap rewrite | UnitMap
  | IdMap of 'c metaVar |
  MapItem of ('a, 'b, 'c) k rewrite * ('a, 'b, 'c) k rewrite |
  MapFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
and ('a, 'b, 'c) theSet =
  SetCon of ('a, 'b, 'c) theSet rewrite * ('a, 'b, 'c) theSet rewrite | UnitSet
  | IdSet of 'c metaVar | SetItem of ('a, 'b, 'c) k rewrite |
  SetFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite;;

type ('a, 'b) irKLabel = IRKLabel of 'a label | IRIdKLabel of 'b metaVar;;

type ('a, 'b, 'c) irK = KPat of ('a, 'b, 'c) irKItem list * 'c metaVar option
and ('a, 'b, 'c) irMap =
  MapPat of (('a, 'b, 'c) irK * ('a, 'b, 'c) irK) list * 'c metaVar option
and ('a, 'b, 'c) irSet = SetPat of ('a, 'b, 'c) irK list * 'c metaVar option
and ('a, 'b, 'c) irList = ListPatNoVar of ('a, 'b, 'c) irK list |
  ListPat of ('a, 'b, 'c) irK list * 'c metaVar * ('a, 'b, 'c) irK list
and ('a, 'b, 'c) irBigKWithBag = IRK of ('a, 'b, 'c) irK |
  IRList of ('a, 'b, 'c) irList | IRSet of ('a, 'b, 'c) irSet |
  IRMap of ('a, 'b, 'c) irMap | IRBag of ('a, 'b, 'c) irBag
and ('a, 'b, 'c) irBag =
  BagPat of
    ('b var * (feature list * ('a, 'b, 'c) irBigKWithBag)) list *
      'c metaVar option
and ('a, 'b, 'c) irBigKWithLabel = IRBigBag of ('a, 'b, 'c) irBigKWithBag |
  IRBigLabel of ('a, 'c) irKLabel
and ('a, 'b, 'c) irKList = KListPatNoVar of ('a, 'b, 'c) irBigKWithLabel list |
  KListPat of
    ('a, 'b, 'c) irBigKWithLabel list * 'c metaVar *
      ('a, 'b, 'c) irBigKWithLabel list
and ('a, 'b, 'c) irKItem =
  IRKItem of ('a, 'c) irKLabel * ('a, 'b, 'c) irKList * 'a sort list |
  IRIdKItem of 'c metaVar * 'a sort list | IRHOLE of 'a sort list;;

type ('a, 'b, 'c) matchFactor = KLabelMatching of ('a, 'c) irKLabel |
  KItemMatching of ('a, 'b, 'c) irKItem | KListMatching of ('a, 'b, 'c) irKList
  | KMatching of ('a, 'b, 'c) irK | ListMatching of ('a, 'b, 'c) irList |
  SetMatching of ('a, 'b, 'c) irSet | MapMatching of ('a, 'b, 'c) irMap |
  BagMatching of ('a, 'b, 'c) irBag;;

type ('a, 'b, 'c) pat = KLabelFunPat of 'a label * ('a, 'b, 'c) irKList |
  KFunPat of 'a label * ('a, 'b, 'c) irKList |
  KItemFunPat of 'a label * ('a, 'b, 'c) irKList |
  ListFunPat of 'a label * ('a, 'b, 'c) irKList |
  SetFunPat of 'a label * ('a, 'b, 'c) irKList |
  MapFunPat of 'a label * ('a, 'b, 'c) irKList |
  NormalPat of ('a, 'b, 'c) matchFactor;;

type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
and 'a pred = Seq of (unit -> 'a seq);;

type ('a, 'b, 'c) kRule =
  Context of ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list |
  ContextWithCon of
    ('a, 'b, 'c) kItem * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | KRule of ('a, 'b, 'c) k rewrite * ('b, 'a) ruleAttrib list |
  KRuleWithCon of
    ('a, 'b, 'c) k rewrite * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | KItemRule of ('a, 'b, 'c) kItem rewrite * ('b, 'a) ruleAttrib list |
  KItemRuleWithCon of
    ('a, 'b, 'c) kItem rewrite * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | KLabelRule of ('a, 'b, 'c) kLabel rewrite * ('b, 'a) ruleAttrib list |
  KLabelRuleWithCon of
    ('a, 'b, 'c) kLabel rewrite * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | BagRule of ('a, 'b, 'c) bag rewrite * ('b, 'a) ruleAttrib list |
  BagRuleWithCon of
    ('a, 'b, 'c) bag rewrite * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | ListRule of ('a, 'b, 'c) theList rewrite * ('b, 'a) ruleAttrib list |
  ListRuleWithCon of
    ('a, 'b, 'c) theList rewrite * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | SetRule of ('a, 'b, 'c) theSet rewrite * ('b, 'a) ruleAttrib list |
  SetRuleWithCon of
    ('a, 'b, 'c) theSet rewrite * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | MapRule of ('a, 'b, 'c) theMap rewrite * ('b, 'a) ruleAttrib list |
  MapRuleWithCon of
    ('a, 'b, 'c) theMap rewrite * ('a, 'b, 'c) kItem *
      ('b, 'a) ruleAttrib list;;

type atoken = AChar of char | LBr | RBr | To | TheStar | Plus | OneOrMore;;

type 'a nelist = Single of 'a | Con of 'a * 'a nelist;;

type 'a symbol = NonTerminal of 'a sort | Terminal of char list;;

type 'a kSyntax = Syntax of 'a sort * 'a symbol nelist * synAttrib list |
  Subsort of 'a sort * 'a sort | Token of 'a sort * reg * synAttrib list |
  ListSyntax of 'a sort * 'a sort * char list * synAttrib list;;

type ('a, 'b) oneStep = Success of 'a | Failure of 'b;;

type ('a, 'b, 'c) rulePat =
  FunPat of
    'a label *
      (('a, 'b, 'c) pat *
        (('a, 'b, 'c) subsFactor * ('a, 'b, 'c) suKItem)) list *
      (('a, 'b, 'c) pat *
        (('a, 'b, 'c) subsFactor * ('a, 'b, 'c) suKItem)) option
  | MacroPat of 'a label * ('a, 'b, 'c) irKList * ('a, 'b, 'c) suKFactor list |
  AnywherePat of
    'a label * ('a, 'b, 'c) irKList * ('a, 'b, 'c) suKFactor list *
      ('a, 'b, 'c) suKItem
  | KRulePat of
      ('a, 'b, 'c) irK * ('a, 'b, 'c) suKFactor list * ('a, 'b, 'c) suKItem *
        bool
  | BagRulePat of
      ('a, 'b, 'c) irBag * ('a, 'b, 'c) suB list * ('a, 'b, 'c) suKItem * bool;;

type ('a, 'b, 'c) simpleK = SimId of 'c metaVar * 'a sort |
  SimTerm of 'a label * ('a, 'b, 'c) simpleK list | SimLabel of 'a label |
  SimEmpty of 'a sort | SimBagCon of ('a, 'b, 'c) simpleK * ('a, 'b, 'c) simpleK
  | SimBag of 'b var * feature list * ('a, 'b, 'c) simpleK;;

type ruleLabel = FunTrans | AnywhereTrans | NormalTrans;;

type 'a kItemSyntax = SingleTon of 'a | SetTon of ('a -> bool);;

type ('a, 'b, 'c, 'd) kModuleItem = TheSyntax of 'a kSyntax | Imports of 'c |
  TheConfiguration of ('a, 'b, 'd) bag | TheRule of ('a, 'b, 'd) kRule;;

type ('a, 'b, 'c) theoryParsed =
  Parsed of
    ('a, 'b, 'c) simpleK option * ('a sort * ('a kSyntax list) list) list *
      (('a, 'b, 'c) simpleK *
        (('a, 'b, 'c) simpleK *
          (('a, 'b, 'c) simpleK * ('b, 'a) ruleAttrib list))) list;;

let rec dup = function Neg n -> Neg (Bit0 n)
              | Pos n -> Pos (Bit0 n)
              | Zero_int -> Zero_int;;

let rec uminus_int = function Neg m -> Pos m
                     | Pos m -> Neg m
                     | Zero_int -> Zero_int;;

let rec plus_num
  x0 x1 = match x0, x1 with Bit1 m, Bit1 n -> Bit0 (plus_num (plus_num m n) One)
    | Bit1 m, Bit0 n -> Bit1 (plus_num m n)
    | Bit1 m, One -> Bit0 (plus_num m One)
    | Bit0 m, Bit1 n -> Bit1 (plus_num m n)
    | Bit0 m, Bit0 n -> Bit0 (plus_num m n)
    | Bit0 m, One -> Bit1 m
    | One, Bit1 n -> Bit0 (plus_num n One)
    | One, Bit0 n -> Bit1 n
    | One, One -> Bit0 One;;

let one_int : int = Pos One;;

let rec bitM = function One -> One
               | Bit0 n -> Bit1 (bitM n)
               | Bit1 n -> Bit1 (Bit0 n);;

let rec sub
  x0 x1 = match x0, x1 with Bit0 m, Bit1 n -> minus_int (dup (sub m n)) one_int
    | Bit1 m, Bit0 n -> plus_int (dup (sub m n)) one_int
    | Bit1 m, Bit1 n -> dup (sub m n)
    | Bit0 m, Bit0 n -> dup (sub m n)
    | One, Bit1 n -> Neg (Bit0 n)
    | One, Bit0 n -> Neg (bitM n)
    | Bit1 m, One -> Pos (Bit0 m)
    | Bit0 m, One -> Pos (bitM m)
    | One, One -> Zero_int
and plus_int k l = match k, l with Neg m, Neg n -> Neg (plus_num m n)
               | Neg m, Pos n -> sub n m
               | Pos m, Neg n -> sub m n
               | Pos m, Pos n -> Pos (plus_num m n)
               | Zero_int, l -> l
               | k, Zero_int -> k
and minus_int k l = match k, l with Neg m, Neg n -> sub n m
                | Neg m, Pos n -> Neg (plus_num m n)
                | Pos m, Neg n -> Pos (plus_num m n)
                | Pos m, Pos n -> sub m n
                | Zero_int, l -> uminus_int l
                | k, Zero_int -> k;;

let rec inc = function One -> Bit0 One
              | Bit0 x -> Bit1 x
              | Bit1 x -> Bit0 (inc x);;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let bot_pred : 'a pred = Seq (fun _ -> Empty);;

let rec single x = Seq (fun _ -> Insert (x, bot_pred));;

let rec bind (Seq g) f = Seq (fun _ -> apply f (g ()))
and apply f x1 = match f, x1 with f, Empty -> Empty
            | f, Insert (x, p) -> Join (f x, Join (bind p f, Empty))
            | f, Join (p, xq) -> Join (bind p f, apply f xq);;

let rec eq_i_i _A
  xa xb =
    bind (single (xa, xb))
      (fun (x, xaa) -> (if eq _A x xaa then single () else bot_pred));;

let rec eq_i_o xa = bind (single xa) single;;

let rec lookup _A
  x xa1 = match x, xa1 with x, [] -> None
    | x, (a, b) :: xl -> (if eq _A a x then Some b else lookup _A x xl);;

let rec update _A
  x y xa2 = match x, y, xa2 with x, y, [] -> [(x, y)]
    | x, y, (a, b) :: xl ->
        (if eq _A a x then (a, y) :: xl else (a, b) :: update _A x y xl);;

let rec null = function [] -> true
               | x :: xs -> false;;

let bot_set : 'a set = Set [];;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec inserta _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec insert _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (removeAll _A x xs)
    | x, Set xs -> Set (inserta _A x xs);;

let rec turnMap _A _B _C
  = function [] -> bot_set
    | ItemM (a, b) :: l ->
        insert
          (equal_prod (equal_list (equal_suKFactor _A _B _C))
            (equal_list (equal_suKFactor _A _B _C)))
          (a, b) (turnMap _A _B _C l)
    | IdM v :: l -> turnMap _A _B _C l
    | SUMapKItem (v, va) :: l -> turnMap _A _B _C l;;

let rec turnSet _A _B _C
  = function [] -> bot_set
    | ItemS s :: l ->
        insert (equal_list (equal_suKFactor _A _B _C)) s (turnSet _A _B _C l)
    | IdS v :: l -> turnSet _A _B _C l
    | SUSetKItem (v, va) :: l -> turnSet _A _B _C l;;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
    | x, Set xs -> membera _A xs x;;

let rec existKey _A
  x xa1 = match x, xa1 with x, [] -> false
    | x, (a, b) :: xl -> (if eq _A x a then true else existKey _A x xl);;

let rec searchDataBaseByKey _A
  xa0 x = match xa0, x with [], x -> None
    | (x, y) :: l, a ->
        (if eq _A x a then Some y else searchDataBaseByKey _A l a);;

let rec deleteDataBaseByKey _A
  xa0 x = match xa0, x with [], x -> []
    | (x, y) :: l, a ->
        (if eq _A x a then l else (x, y) :: deleteDataBaseByKey _A l a);;

let rec subsortAux _A
  a b s = match a, b, s with a, b, [] -> false
    | a, b, s ->
        (match searchDataBaseByKey _A s b with None -> false
          | Some l ->
            (if membera _A l a then true
              else subsortInList _A a l (deleteDataBaseByKey _A s b)))
and subsortInList _A
  a x1 s = match a, x1, s with a, [], s -> false
    | a, b :: l, s -> subsortAux _A a b s || subsortInList _A a l s;;

let rec subsort _A
  a b subG = (if eq _A a b then true else subsortAux _A a b subG);;

let rec insertSortInList _A
  a x1 subG = match a, x1, subG with a, [], subG -> [a]
    | a, b :: l, subG ->
        (if subsort _A a b subG then b :: l
          else (if subsort _A b a subG then insertSortInList _A a l subG
                 else b :: insertSortInList _A a l subG));;

let rec insertAllSortsInList _A
  x0 l subG = match x0, l, subG with [], l, subG -> l
    | x :: l, s, subG ->
        insertAllSortsInList _A l (insertSortInList _A x s subG) subG;;

let rec getValueTerm _A
  a x1 = match a, x1 with a, [] -> None
    | aa, (a, b) :: l -> (if eq _A aa a then Some b else getValueTerm _A aa l);;

let rec getMaxSorts _A
  a x1 subG checked acc = match a, x1, subG, checked, acc with
    a, [], subG, checked, acc -> acc
    | a, c :: l, subG, checked, acc ->
        (if subsort _A c a subG
          then getMaxSorts _A a l subG (c :: checked)
                 (insertSortInList _A c acc subG)
          else (if membera _A checked c then getMaxSorts _A a l subG checked acc
                 else (match getValueTerm _A c subG
                        with None -> getMaxSorts _A a l subG (c :: checked) acc
                        | Some newl ->
                          getMaxSorts _A a l subG (c :: checked)
                            (getMaxSorts _A a newl subG (c :: checked) acc))));;

let rec meetAux _A
  a x1 subG = match a, x1, subG with a, [], subG -> []
    | a, x :: l, subG ->
        (if subsort _A a x subG
          then insertSortInList _A a (meetAux _A a l subG) subG
          else (if subsort _A x a subG
                 then insertSortInList _A x (meetAux _A a l subG) subG
                 else (match getValueTerm _A x subG
                        with None -> meetAux _A a l subG
                        | Some newl ->
                          insertAllSortsInList _A
                            (getMaxSorts _A a newl subG [x] [])
                            (meetAux _A a l subG) subG)));;

let rec meet _A
  x0 b subG = match x0, b, subG with [], b, subG -> []
    | x :: l, b, subG ->
        insertAllSortsInList _A (meetAux _A x b subG) (meet _A l b subG) subG;;

let rec irToSUInKLabel = function IRKLabel a -> SUKLabel a
                         | IRIdKLabel n -> SUIdKLabel n;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec irToSUInK _A
  (KPat (l, a)) =
    (match a
      with None ->
        map (fun x ->
              (match x with IRKItem (_, _, _) -> ItemFactor (irToSUInKItem _A x)
                | IRIdKItem (u, v) ->
                  (if equal_lista (equal_sort _A) v [K] then IdFactor u
                    else ItemFactor (irToSUInKItem _A x))
                | IRHOLE _ -> ItemFactor (irToSUInKItem _A x)))
          l
      | Some aa ->
        map (fun x ->
              (match x with IRKItem (_, _, _) -> ItemFactor (irToSUInKItem _A x)
                | IRIdKItem (u, v) ->
                  (if equal_lista (equal_sort _A) v [K] then IdFactor u
                    else ItemFactor (irToSUInKItem _A x))
                | IRHOLE _ -> ItemFactor (irToSUInKItem _A x)))
          l @
          [IdFactor aa])
and irToSUInMap _A
  (MapPat (l, a)) =
    (match a
      with None -> map (fun (x, y) -> ItemM (irToSUInK _A x, irToSUInK _A y)) l
      | Some aa ->
        map (fun (x, y) -> ItemM (irToSUInK _A x, irToSUInK _A y)) l @ [IdM aa])
and irToSUInSet _A
  (SetPat (l, a)) =
    (match a with None -> map (fun x -> ItemS (irToSUInK _A x)) l
      | Some aa -> map (fun x -> ItemS (irToSUInK _A x)) l @ [IdS aa])
and irToSUInList _A
  = function ListPatNoVar l -> map (fun x -> ItemL (irToSUInK _A x)) l
    | ListPat (l, a, r) ->
        map (fun x -> ItemL (irToSUInK _A x)) l @
          [IdL a] @ map (fun x -> ItemL (irToSUInK _A x)) r
and irToSUInBigKWithBag _A = function IRK a -> SUK (irToSUInK _A a)
                             | IRList a -> SUList (irToSUInList _A a)
                             | IRSet a -> SUSet (irToSUInSet _A a)
                             | IRMap a -> SUMap (irToSUInMap _A a)
                             | IRBag a -> SUBag (irToSUInBag _A a)
and irToSUInBag _A
  (BagPat (l, a)) =
    (match a
      with None ->
        map (fun (aa, b) ->
              (let (ba, c) = b in ItemB (aa, ba, irToSUInBigKWithBag _A c)))
          l
      | Some aa ->
        map (fun (ab, b) ->
              (let (ba, c) = b in ItemB (ab, ba, irToSUInBigKWithBag _A c)))
          l @
          [IdB aa])
and irToSUInBigKWithLabel _A
  = function IRBigBag a -> SUBigBag (irToSUInBigKWithBag _A a)
    | IRBigLabel a -> SUBigLabel (irToSUInKLabel a)
and irToSUInKList _A
  = function
    KListPatNoVar l -> map (fun x -> ItemKl (irToSUInBigKWithLabel _A x)) l
    | KListPat (l, a, r) ->
        map (fun x -> ItemKl (irToSUInBigKWithLabel _A x)) l @
          [IdKl a] @ map (fun x -> ItemKl (irToSUInBigKWithLabel _A x)) r
and irToSUInKItem _A
  = function
    IRKItem (l, r, ty) -> SUKItem (irToSUInKLabel l, irToSUInKList _A r, ty)
    | IRIdKItem (a, b) -> SUIdKItem (a, b)
    | IRHOLE a -> SUHOLE a;;

let rec eliminateEntry _A
  a x1 = match a, x1 with a, [] -> []
    | a, (b, c) :: l ->
        (if eq _A a b then l else (b, c) :: eliminateEntry _A a l);;

let rec eliminateEntryList _A
  a x1 = match a, x1 with a, [] -> []
    | a, (b, c) :: l ->
        (b, eliminateEntry _A a c) :: eliminateEntryList _A a l;;

let rec eliminateEntryMap _B
  x0 s = match x0, s with [], s -> Some s
    | (a, (b, c)) :: l, s ->
        eliminateEntryMap _B l (eliminateEntryList _B b s);;

let rec searchOneAux
  = function [] -> ([], [])
    | (a, b) :: l ->
        (let (have, noHave) = searchOneAux l in
          (match b with [] -> (have, (a, b) :: noHave)
            | [ba] -> ((a, ba) :: have, noHave)
            | _ :: _ :: _ -> (have, (a, b) :: noHave)));;

let rec searchZero
  = function [] -> ([], [])
    | (a, b) :: l ->
        (let (have, noHave) = searchZero l in
          (if null b then ((a, b) :: have, noHave)
            else (have, (a, b) :: noHave)));;

let rec searchOne _B
  l acc =
    (let (x, y) = searchZero l in
      (if null x
        then (let (u, v) = searchOneAux y in
               (if null u then Some (acc, v)
                 else (match eliminateEntryMap _B u v with None -> None
                        | Some va -> searchOne _B va (u @ acc))))
        else None));;

let rec getSUKLabelMeaning
  x = (match x with SUKLabel a -> Some a | SUIdKLabel _ -> None
        | SUKLabelFun (_, _) -> None);;

let rec isFunctionItemAux _C
  x0 s = match x0, s with [], s -> false
    | (a, (b, (SingleTon t, (nl, true)))) :: l, s ->
        (if eq _C t s then true else isFunctionItemAux _C l s)
    | (a, (b, (SetTon t, (nl, true)))) :: l, s ->
        (if t s then true else isFunctionItemAux _C l s)
    | (a, (b, (t, (nl, false)))) :: l, s -> isFunctionItemAux _C l s;;

let rec isFunctionItem _A s database = isFunctionItemAux _A database s;;

let rec suToIRInK _A
  x0 database = match x0, database with
    [], database -> Some (NormalPat (KMatching (KPat ([], None))))
    | b :: l, database ->
        (match suToIRInK _A l database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching (KPat (t, None)))) ->
            (match b
              with ItemFactor x ->
                (if null t
                  then (match x
                         with SUKItem (_, _, _) ->
                           (let Some (NormalPat (KItemMatching xa)) =
                              suToIRInKItem _A x database in
                             Some (NormalPat (KMatching (KPat ([xa], None)))))
                         | SUIdKItem (xa, xty) ->
                           (if equal_lista (equal_sort _A) xty [K]
                             then Some (NormalPat
 (KMatching (KPat ([], Some xa))))
                             else Some (NormalPat
 (KMatching (KPat ([IRIdKItem (xa, xty)], None)))))
                         | SUHOLE _ ->
                           (let Some (NormalPat (KItemMatching xa)) =
                              suToIRInKItem _A x database in
                             Some (NormalPat (KMatching (KPat ([xa], None))))))
                  else (match suToIRInKItem _A x database with None -> None
                         | Some (KLabelFunPat (_, _)) -> None
                         | Some (KFunPat (_, _)) -> None
                         | Some (KItemFunPat (_, _)) -> None
                         | Some (ListFunPat (_, _)) -> None
                         | Some (SetFunPat (_, _)) -> None
                         | Some (MapFunPat (_, _)) -> None
                         | Some (NormalPat (KLabelMatching _)) -> None
                         | Some (NormalPat (KItemMatching xa)) ->
                           Some (NormalPat (KMatching (KPat (xa :: t, None))))
                         | Some (NormalPat (KListMatching _)) -> None
                         | Some (NormalPat (KMatching _)) -> None
                         | Some (NormalPat (ListMatching _)) -> None
                         | Some (NormalPat (SetMatching _)) -> None
                         | Some (NormalPat (MapMatching _)) -> None
                         | Some (NormalPat (BagMatching _)) -> None))
              | IdFactor x ->
                (if null t then Some (NormalPat (KMatching (KPat ([], Some x))))
                  else Some (NormalPat
                              (KMatching
                                (KPat (IRIdKItem (x, [K]) :: t, None)))))
              | SUKKItem (u, v, _) ->
                (if null t
                  then (match getSUKLabelMeaning u with None -> None
                         | Some s ->
                           (if isFunctionItem (equal_label _A) s database
                             then (match suToIRInKList _A v database
                                    with None -> None
                                    | Some va -> Some (KFunPat (s, va)))
                             else None))
                  else None))
          | Some (NormalPat (KMatching (KPat (t, Some v)))) ->
            (match b
              with ItemFactor x ->
                (match suToIRInKItem _A x database with None -> None
                  | Some (KLabelFunPat (_, _)) -> None
                  | Some (KFunPat (_, _)) -> None
                  | Some (KItemFunPat (_, _)) -> None
                  | Some (ListFunPat (_, _)) -> None
                  | Some (SetFunPat (_, _)) -> None
                  | Some (MapFunPat (_, _)) -> None
                  | Some (NormalPat (KLabelMatching _)) -> None
                  | Some (NormalPat (KItemMatching xa)) ->
                    Some (NormalPat (KMatching (KPat (xa :: t, None))))
                  | Some (NormalPat (KListMatching _)) -> None
                  | Some (NormalPat (KMatching _)) -> None
                  | Some (NormalPat (ListMatching _)) -> None
                  | Some (NormalPat (SetMatching _)) -> None
                  | Some (NormalPat (MapMatching _)) -> None
                  | Some (NormalPat (BagMatching _)) -> None)
              | IdFactor x ->
                Some (NormalPat
                       (KMatching (KPat (IRIdKItem (x, [K]) :: t, Some v))))
              | SUKKItem (_, _, _) -> None)
          | Some (NormalPat (ListMatching _)) -> None
          | Some (NormalPat (SetMatching _)) -> None
          | Some (NormalPat (MapMatching _)) -> None
          | Some (NormalPat (BagMatching _)) -> None)
and suToIRInBigKWithBag _A
  x0 database = match x0, database with
    SUK a, database ->
      (match suToIRInK _A a database with None -> None
        | Some aa ->
          (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
            | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
            | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
            | NormalPat ab ->
              (match ab with KLabelMatching _ -> None | KItemMatching _ -> None
                | KListMatching _ -> None | KMatching ac -> Some (IRK ac)
                | ListMatching _ -> None | SetMatching _ -> None
                | MapMatching _ -> None | BagMatching _ -> None)))
    | SUList a, database ->
        (match suToIRInList _A a database with None -> None
          | Some aa ->
            (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
              | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
              | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
              | NormalPat ab ->
                (match ab with KLabelMatching _ -> None
                  | KItemMatching _ -> None | KListMatching _ -> None
                  | KMatching _ -> None | ListMatching ac -> Some (IRList ac)
                  | SetMatching _ -> None | MapMatching _ -> None
                  | BagMatching _ -> None)))
    | SUSet a, database ->
        (match suToIRInSet _A a database with None -> None
          | Some aa ->
            (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
              | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
              | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
              | NormalPat ab ->
                (match ab with KLabelMatching _ -> None
                  | KItemMatching _ -> None | KListMatching _ -> None
                  | KMatching _ -> None | ListMatching _ -> None
                  | SetMatching ac -> Some (IRSet ac) | MapMatching _ -> None
                  | BagMatching _ -> None)))
    | SUMap a, database ->
        (match suToIRInMap _A a database with None -> None
          | Some aa ->
            (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
              | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
              | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
              | NormalPat ab ->
                (match ab with KLabelMatching _ -> None
                  | KItemMatching _ -> None | KListMatching _ -> None
                  | KMatching _ -> None | ListMatching _ -> None
                  | SetMatching _ -> None | MapMatching ac -> Some (IRMap ac)
                  | BagMatching _ -> None)))
    | SUBag a, database ->
        (match suToIRInBag _A a database with None -> None
          | Some aa -> Some (IRBag aa))
and suToIRInBag _A
  x0 database = match x0, database with [], database -> Some (BagPat ([], None))
    | b :: l, database ->
        (match suToIRInBag _A l database with None -> None
          | Some (BagPat (t, None)) ->
            (match b
              with ItemB (a, ba, c) ->
                (match suToIRInBigKWithBag _A c database with None -> None
                  | Some ca -> Some (BagPat ((a, (ba, ca)) :: t, None)))
              | IdB x -> Some (BagPat (t, Some x)))
          | Some (BagPat (t, Some v)) ->
            (match b
              with ItemB (a, ba, c) ->
                (match suToIRInBigKWithBag _A c database with None -> None
                  | Some ca -> Some (BagPat ((a, (ba, ca)) :: t, Some v)))
              | IdB _ -> None))
and suToIRInBigKWithLabel _A
  x0 database = match x0, database with
    SUBigBag a, database ->
      (match suToIRInBigKWithBag _A a database with None -> None
        | Some aa -> Some (IRBigBag aa))
    | SUBigLabel a, database ->
        (match suToIRInKLabel _A a database with None -> None
          | Some aa ->
            (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
              | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
              | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
              | NormalPat ab ->
                (match ab with KLabelMatching ac -> Some (IRBigLabel ac)
                  | KItemMatching _ -> None | KListMatching _ -> None
                  | KMatching _ -> None | ListMatching _ -> None
                  | SetMatching _ -> None | MapMatching _ -> None
                  | BagMatching _ -> None)))
and suToIRInKList _A
  x0 database = match x0, database with [], database -> Some (KListPatNoVar [])
    | b :: l, database ->
        (match suToIRInKList _A l database with None -> None
          | Some (KListPatNoVar la) ->
            (match b
              with ItemKl x ->
                (match suToIRInBigKWithLabel _A x database with None -> None
                  | Some xa -> Some (KListPatNoVar (xa :: la)))
              | IdKl x -> Some (KListPat ([], x, la)))
          | Some (KListPat (la, x, ra)) ->
            (match b
              with ItemKl u ->
                (match suToIRInBigKWithLabel _A u database with None -> None
                  | Some ua -> Some (KListPat (ua :: la, x, ra)))
              | IdKl _ -> None))
and suToIRInMap _A
  x0 database = match x0, database with
    [], database -> Some (NormalPat (MapMatching (MapPat ([], None))))
    | b :: l, database ->
        (match suToIRInMap _A l database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching _)) -> None
          | Some (NormalPat (ListMatching _)) -> None
          | Some (NormalPat (SetMatching _)) -> None
          | Some (NormalPat (MapMatching (MapPat (t, None)))) ->
            (match b
              with ItemM (x, y) ->
                (match (suToIRInK _A x database, suToIRInK _A y database)
                  with (None, _) -> None
                  | (Some (KLabelFunPat (_, _)), _) -> None
                  | (Some (KFunPat (_, _)), _) -> None
                  | (Some (KItemFunPat (_, _)), _) -> None
                  | (Some (ListFunPat (_, _)), _) -> None
                  | (Some (SetFunPat (_, _)), _) -> None
                  | (Some (MapFunPat (_, _)), _) -> None
                  | (Some (NormalPat (KLabelMatching _)), _) -> None
                  | (Some (NormalPat (KItemMatching _)), _) -> None
                  | (Some (NormalPat (KListMatching _)), _) -> None
                  | (Some (NormalPat (KMatching _)), None) -> None
                  | (Some (NormalPat (KMatching _)), Some (KLabelFunPat (_, _)))
                    -> None
                  | (Some (NormalPat (KMatching _)), Some (KFunPat (_, _))) ->
                    None
                  | (Some (NormalPat (KMatching _)), Some (KItemFunPat (_, _)))
                    -> None
                  | (Some (NormalPat (KMatching _)), Some (ListFunPat (_, _)))
                    -> None
                  | (Some (NormalPat (KMatching _)), Some (SetFunPat (_, _))) ->
                    None
                  | (Some (NormalPat (KMatching _)), Some (MapFunPat (_, _))) ->
                    None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (KLabelMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (KItemMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (KListMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching xa)),
                      Some (NormalPat (KMatching ya)))
                    -> Some (NormalPat
                              (MapMatching (MapPat ((xa, ya) :: t, None))))
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (ListMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (SetMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (MapMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (BagMatching _)))
                    -> None
                  | (Some (NormalPat (ListMatching _)), _) -> None
                  | (Some (NormalPat (SetMatching _)), _) -> None
                  | (Some (NormalPat (MapMatching _)), _) -> None
                  | (Some (NormalPat (BagMatching _)), _) -> None)
              | IdM x -> Some (NormalPat (MapMatching (MapPat (t, Some x))))
              | SUMapKItem (u, v) ->
                (if null t
                  then (match getSUKLabelMeaning u with None -> None
                         | Some ua ->
                           (if isFunctionItem (equal_label _A) ua database
                             then (match suToIRInKList _A v database
                                    with None -> None
                                    | Some va -> Some (MapFunPat (ua, va)))
                             else None))
                  else None))
          | Some (NormalPat (MapMatching (MapPat (t, Some v)))) ->
            (match b
              with ItemM (x, y) ->
                (match (suToIRInK _A x database, suToIRInK _A y database)
                  with (None, _) -> None
                  | (Some (KLabelFunPat (_, _)), _) -> None
                  | (Some (KFunPat (_, _)), _) -> None
                  | (Some (KItemFunPat (_, _)), _) -> None
                  | (Some (ListFunPat (_, _)), _) -> None
                  | (Some (SetFunPat (_, _)), _) -> None
                  | (Some (MapFunPat (_, _)), _) -> None
                  | (Some (NormalPat (KLabelMatching _)), _) -> None
                  | (Some (NormalPat (KItemMatching _)), _) -> None
                  | (Some (NormalPat (KListMatching _)), _) -> None
                  | (Some (NormalPat (KMatching _)), None) -> None
                  | (Some (NormalPat (KMatching _)), Some (KLabelFunPat (_, _)))
                    -> None
                  | (Some (NormalPat (KMatching _)), Some (KFunPat (_, _))) ->
                    None
                  | (Some (NormalPat (KMatching _)), Some (KItemFunPat (_, _)))
                    -> None
                  | (Some (NormalPat (KMatching _)), Some (ListFunPat (_, _)))
                    -> None
                  | (Some (NormalPat (KMatching _)), Some (SetFunPat (_, _))) ->
                    None
                  | (Some (NormalPat (KMatching _)), Some (MapFunPat (_, _))) ->
                    None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (KLabelMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (KItemMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (KListMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching xa)),
                      Some (NormalPat (KMatching ya)))
                    -> Some (NormalPat
                              (MapMatching (MapPat ((xa, ya) :: t, Some v))))
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (ListMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (SetMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (MapMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (BagMatching _)))
                    -> None
                  | (Some (NormalPat (ListMatching _)), _) -> None
                  | (Some (NormalPat (SetMatching _)), _) -> None
                  | (Some (NormalPat (MapMatching _)), _) -> None
                  | (Some (NormalPat (BagMatching _)), _) -> None)
              | IdM _ -> None | SUMapKItem (_, _) -> None)
          | Some (NormalPat (BagMatching _)) -> None)
and suToIRInSet _A
  x0 database = match x0, database with
    [], database -> Some (NormalPat (SetMatching (SetPat ([], None))))
    | b :: l, database ->
        (match suToIRInSet _A l database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching _)) -> None
          | Some (NormalPat (ListMatching _)) -> None
          | Some (NormalPat (SetMatching (SetPat (t, None)))) ->
            (match b
              with ItemS x ->
                (match suToIRInK _A x database with None -> None
                  | Some (KLabelFunPat (_, _)) -> None
                  | Some (KFunPat (_, _)) -> None
                  | Some (KItemFunPat (_, _)) -> None
                  | Some (ListFunPat (_, _)) -> None
                  | Some (SetFunPat (_, _)) -> None
                  | Some (MapFunPat (_, _)) -> None
                  | Some (NormalPat (KLabelMatching _)) -> None
                  | Some (NormalPat (KItemMatching _)) -> None
                  | Some (NormalPat (KListMatching _)) -> None
                  | Some (NormalPat (KMatching xa)) ->
                    Some (NormalPat (SetMatching (SetPat (xa :: t, None))))
                  | Some (NormalPat (ListMatching _)) -> None
                  | Some (NormalPat (SetMatching _)) -> None
                  | Some (NormalPat (MapMatching _)) -> None
                  | Some (NormalPat (BagMatching _)) -> None)
              | IdS x -> Some (NormalPat (SetMatching (SetPat (t, Some x))))
              | SUSetKItem (u, v) ->
                (if null t
                  then (match getSUKLabelMeaning u with None -> None
                         | Some ua ->
                           (if isFunctionItem (equal_label _A) ua database
                             then (match suToIRInKList _A v database
                                    with None -> None
                                    | Some va -> Some (SetFunPat (ua, va)))
                             else None))
                  else None))
          | Some (NormalPat (SetMatching (SetPat (t, Some v)))) ->
            (match b
              with ItemS x ->
                (match suToIRInK _A x database with None -> None
                  | Some (KLabelFunPat (_, _)) -> None
                  | Some (KFunPat (_, _)) -> None
                  | Some (KItemFunPat (_, _)) -> None
                  | Some (ListFunPat (_, _)) -> None
                  | Some (SetFunPat (_, _)) -> None
                  | Some (MapFunPat (_, _)) -> None
                  | Some (NormalPat (KLabelMatching _)) -> None
                  | Some (NormalPat (KItemMatching _)) -> None
                  | Some (NormalPat (KListMatching _)) -> None
                  | Some (NormalPat (KMatching xa)) ->
                    Some (NormalPat (SetMatching (SetPat (xa :: t, Some v))))
                  | Some (NormalPat (ListMatching _)) -> None
                  | Some (NormalPat (SetMatching _)) -> None
                  | Some (NormalPat (MapMatching _)) -> None
                  | Some (NormalPat (BagMatching _)) -> None)
              | IdS _ -> None | SUSetKItem (_, _) -> None)
          | Some (NormalPat (MapMatching _)) -> None
          | Some (NormalPat (BagMatching _)) -> None)
and suToIRInList _A
  x0 database = match x0, database with
    [], database -> Some (NormalPat (ListMatching (ListPatNoVar [])))
    | b :: l, database ->
        (match suToIRInList _A l database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching _)) -> None
          | Some (NormalPat (ListMatching (ListPatNoVar la))) ->
            (match b
              with ItemL x ->
                (match suToIRInK _A x database with None -> None
                  | Some (KLabelFunPat (_, _)) -> None
                  | Some (KFunPat (_, _)) -> None
                  | Some (KItemFunPat (_, _)) -> None
                  | Some (ListFunPat (_, _)) -> None
                  | Some (SetFunPat (_, _)) -> None
                  | Some (MapFunPat (_, _)) -> None
                  | Some (NormalPat (KLabelMatching _)) -> None
                  | Some (NormalPat (KItemMatching _)) -> None
                  | Some (NormalPat (KListMatching _)) -> None
                  | Some (NormalPat (KMatching xa)) ->
                    Some (NormalPat (ListMatching (ListPatNoVar (xa :: la))))
                  | Some (NormalPat (ListMatching _)) -> None
                  | Some (NormalPat (SetMatching _)) -> None
                  | Some (NormalPat (MapMatching _)) -> None
                  | Some (NormalPat (BagMatching _)) -> None)
              | IdL x -> Some (NormalPat (ListMatching (ListPat ([], x, la))))
              | SUListKItem (u, v) ->
                (if null la
                  then (match getSUKLabelMeaning u with None -> None
                         | Some s ->
                           (if isFunctionItem (equal_label _A) s database
                             then (match suToIRInKList _A v database
                                    with None -> None
                                    | Some va -> Some (ListFunPat (s, va)))
                             else None))
                  else None))
          | Some (NormalPat (ListMatching (ListPat (la, x, ra)))) ->
            (match b
              with ItemL u ->
                (match suToIRInK _A u database with None -> None
                  | Some (KLabelFunPat (_, _)) -> None
                  | Some (KFunPat (_, _)) -> None
                  | Some (KItemFunPat (_, _)) -> None
                  | Some (ListFunPat (_, _)) -> None
                  | Some (SetFunPat (_, _)) -> None
                  | Some (MapFunPat (_, _)) -> None
                  | Some (NormalPat (KLabelMatching _)) -> None
                  | Some (NormalPat (KItemMatching _)) -> None
                  | Some (NormalPat (KListMatching _)) -> None
                  | Some (NormalPat (KMatching ua)) ->
                    Some (NormalPat (ListMatching (ListPat (ua :: la, x, ra))))
                  | Some (NormalPat (ListMatching _)) -> None
                  | Some (NormalPat (SetMatching _)) -> None
                  | Some (NormalPat (MapMatching _)) -> None
                  | Some (NormalPat (BagMatching _)) -> None)
              | IdL _ -> None | SUListKItem (_, _) -> None)
          | Some (NormalPat (SetMatching _)) -> None
          | Some (NormalPat (MapMatching _)) -> None
          | Some (NormalPat (BagMatching _)) -> None)
and suToIRInKLabel _A
  x0 database = match x0, database with
    SUKLabel a, database -> Some (NormalPat (KLabelMatching (IRKLabel a)))
    | SUKLabelFun (a, b), database ->
        (match getSUKLabelMeaning a with None -> None
          | Some s ->
            (match suToIRInKList _A b database with None -> None
              | Some ba -> Some (KLabelFunPat (s, ba))))
    | SUIdKLabel n, database -> Some (NormalPat (KLabelMatching (IRIdKLabel n)))
and suToIRInKItem _A
  x0 database = match x0, database with
    SUKItem (l, r, ty), database ->
      (match getSUKLabelMeaning l
        with None ->
          (match (suToIRInKLabel _A l database, suToIRInKList _A r database)
            with (None, _) -> None | (Some (KLabelFunPat (_, _)), _) -> None
            | (Some (KFunPat (_, _)), _) -> None
            | (Some (KItemFunPat (_, _)), _) -> None
            | (Some (ListFunPat (_, _)), _) -> None
            | (Some (SetFunPat (_, _)), _) -> None
            | (Some (MapFunPat (_, _)), _) -> None
            | (Some (NormalPat (KLabelMatching _)), None) -> None
            | (Some (NormalPat (KLabelMatching la)), Some ra) ->
              Some (NormalPat (KItemMatching (IRKItem (la, ra, ty))))
            | (Some (NormalPat (KItemMatching _)), _) -> None
            | (Some (NormalPat (KListMatching _)), _) -> None
            | (Some (NormalPat (KMatching _)), _) -> None
            | (Some (NormalPat (ListMatching _)), _) -> None
            | (Some (NormalPat (SetMatching _)), _) -> None
            | (Some (NormalPat (MapMatching _)), _) -> None
            | (Some (NormalPat (BagMatching _)), _) -> None)
        | Some s ->
          (if isFunctionItem (equal_label _A) s database
            then (match suToIRInKList _A r database with None -> None
                   | Some ra -> Some (KFunPat (s, ra)))
            else (match
                   (suToIRInKLabel _A l database, suToIRInKList _A r database)
                   with (None, _) -> None
                   | (Some (KLabelFunPat (_, _)), _) -> None
                   | (Some (KFunPat (_, _)), _) -> None
                   | (Some (KItemFunPat (_, _)), _) -> None
                   | (Some (ListFunPat (_, _)), _) -> None
                   | (Some (SetFunPat (_, _)), _) -> None
                   | (Some (MapFunPat (_, _)), _) -> None
                   | (Some (NormalPat (KLabelMatching _)), None) -> None
                   | (Some (NormalPat (KLabelMatching la)), Some ra) ->
                     Some (NormalPat (KItemMatching (IRKItem (la, ra, ty))))
                   | (Some (NormalPat (KItemMatching _)), _) -> None
                   | (Some (NormalPat (KListMatching _)), _) -> None
                   | (Some (NormalPat (KMatching _)), _) -> None
                   | (Some (NormalPat (ListMatching _)), _) -> None
                   | (Some (NormalPat (SetMatching _)), _) -> None
                   | (Some (NormalPat (MapMatching _)), _) -> None
                   | (Some (NormalPat (BagMatching _)), _) -> None)))
    | SUIdKItem (a, b), database ->
        Some (NormalPat (KItemMatching (IRIdKItem (a, b))))
    | SUHOLE a, database -> Some (NormalPat (KItemMatching (IRHOLE a)));;

let rec updateMap _A _B
  a b x2 subG = match a, b, x2, subG with a, b, [], subG -> Some [(a, b)]
    | a, b, x :: l, subG ->
        (let (aa, ba) = x in
          (if eq _A a aa
            then (match meet _B b ba subG with [] -> None
                   | ty :: tyl -> Some ((a, ty :: tyl) :: l))
            else (match updateMap _A _B a b l subG with None -> None
                   | Some la -> Some (x :: la))));;

let rec assignSort _A _C
  x0 acc = match x0, acc with
    SimId (a, b), acc ->
      (if equal_sorta _A b Top
        then (match lookup (equal_metaVar _C) a acc with None -> None
               | Some t -> Some (SimId (a, t)))
        else Some (SimId (a, b)))
    | SimTerm (a, bl), acc ->
        (match assignSorts _A _C bl acc with None -> None
          | Some bla -> Some (SimTerm (a, bla)))
    | SimLabel a, acc -> Some (SimLabel a)
    | SimEmpty a, acc -> Some (SimEmpty a)
    | SimBagCon (a, b), acc ->
        (match assignSort _A _C a acc with None -> None
          | Some aa ->
            (match assignSort _A _C b acc with None -> None
              | Some ba -> Some (SimBagCon (aa, ba))))
    | SimBag (x, y, b), acc ->
        (match assignSort _A _C b acc with None -> None
          | Some ba -> Some (SimBag (x, y, ba)))
and assignSorts _A _C
  x0 acc = match x0, acc with [], acc -> Some []
    | x :: xl, acc ->
        (match assignSort _A _C x acc with None -> None
          | Some xa ->
            (match assignSorts _A _C xl acc with None -> None
              | Some xla -> Some (xa :: xla)));;

let rec flattenMapVar = function None -> []
                        | Some v -> [MapPat ([], Some v)];;

let rec flattenMapAux = function [] -> []
                        | x :: xl -> MapPat ([x], None) :: flattenMapAux xl;;

let rec flattenMap
  = function [] -> Some []
    | x :: xl ->
        (match flattenMap xl with None -> None
          | Some xla ->
            (match x with IRBigBag (IRK _) -> None | IRBigBag (IRList _) -> None
              | IRBigBag (IRSet _) -> None
              | IRBigBag (IRMap (MapPat (sl, sv))) ->
                Some (flattenMapAux sl @ flattenMapVar sv @ xla)
              | IRBigBag (IRBag _) -> None | IRBigLabel _ -> None));;

let rec flattenSetVar = function None -> []
                        | Some v -> [SetPat ([], Some v)];;

let rec flattenSetAux = function [] -> []
                        | x :: xl -> SetPat ([x], None) :: flattenSetAux xl;;

let rec flattenSet
  = function [] -> Some []
    | x :: xl ->
        (match flattenSet xl with None -> None
          | Some xla ->
            (match x with IRBigBag (IRK _) -> None | IRBigBag (IRList _) -> None
              | IRBigBag (IRSet (SetPat (sl, sv))) ->
                Some (flattenSetAux sl @ flattenSetVar sv @ xla)
              | IRBigBag (IRMap _) -> None | IRBigBag (IRBag _) -> None
              | IRBigLabel _ -> None));;

let rec getRidOfLabel
  = function [] -> Some []
    | (KLabelFunPat (s, kl), (b, c)) :: l ->
        (match getRidOfLabel l with None -> None
          | Some la -> Some ((kl, (b, c)) :: la))
    | (KFunPat (s, kl), (b, c)) :: l ->
        (match getRidOfLabel l with None -> None
          | Some la -> Some ((kl, (b, c)) :: la))
    | (KItemFunPat (s, kl), (b, c)) :: l ->
        (match getRidOfLabel l with None -> None
          | Some la -> Some ((kl, (b, c)) :: la))
    | (ListFunPat (s, kl), (b, c)) :: l ->
        (match getRidOfLabel l with None -> None
          | Some la -> Some ((kl, (b, c)) :: la))
    | (SetFunPat (s, kl), (b, c)) :: l ->
        (match getRidOfLabel l with None -> None
          | Some la -> Some ((kl, (b, c)) :: la))
    | (MapFunPat (s, kl), (b, c)) :: l ->
        (match getRidOfLabel l with None -> None
          | Some la -> Some ((kl, (b, c)) :: la))
    | (NormalPat a, (b, c)) :: l -> None;;

let rec getFunRule _A
  s x1 = match s, x1 with s, [] -> None
    | sa, FunPat (s, fl, f) :: l ->
        (if equal_labela _A sa s
          then (match f with None -> getRidOfLabel fl
                 | Some fa -> getRidOfLabel (fl @ [fa]))
          else getFunRule _A sa l)
    | s, MacroPat (v, va, vb) :: l -> getFunRule _A s l
    | s, AnywherePat (v, va, vb, vc) :: l -> getFunRule _A s l
    | s, KRulePat (v, va, vb, vc) :: l -> getFunRule _A s l
    | s, BagRulePat (v, va, vb, vc) :: l -> getFunRule _A s l;;

let rec updateBeta _A _B
  a b x2 subG = match a, b, x2, subG with a, b, [], subG -> Some []
    | a, b, x :: l, subG ->
        (let (aa, ba) = x in
          (if eq _A a aa
            then (match meet _B b ba subG with [] -> None
                   | ty :: tyl -> Some ((a, ty :: tyl) :: l))
            else (match updateBeta _A _B a b l subG with None -> None
                   | Some la -> Some (x :: la))));;

let rec is_empty (Seq f) = nulla (f ())
and nulla = function Empty -> true
            | Insert (x, p) -> false
            | Join (p, xq) -> is_empty p && nulla xq;;

let rec singleton _A
  default (Seq f) =
    (match f () with Empty -> default ()
      | Insert (x, p) ->
        (if is_empty p then x
          else (let y = singleton _A default p in
                 (if eq _A x y then x else default ())))
      | Join (p, xq) ->
        (if is_empty p then the_only _A default xq
          else (if nulla xq then singleton _A default p
                 else (let x = singleton _A default p in
                       let y = the_only _A default xq in
                        (if eq _A x y then x else default ())))))
and the_only _A
  default x1 = match default, x1 with default, Empty -> default ()
    | default, Insert (x, p) ->
        (if is_empty p then x
          else (let y = singleton _A default p in
                 (if eq _A x y then x else default ())))
    | default, Join (p, xq) ->
        (if is_empty p then the_only _A default xq
          else (if nulla xq then singleton _A default p
                 else (let x = singleton _A default p in
                       let y = the_only _A default xq in
                        (if eq _A x y then x else default ()))));;

let rec the _A
  a = singleton _A (fun _ -> failwith "not_unique" (fun _ -> the _A a)) a;;

let rec sup_pred
  (Seq f) (Seq g) =
    Seq (fun _ ->
          (match f () with Empty -> g ()
            | Insert (x, p) -> Insert (x, sup_pred p (Seq g))
            | Join (p, xq) -> adjunct (Seq g) (Join (p, xq))))
and adjunct p x1 = match p, x1 with p, Empty -> Join (p, Empty)
              | p, Insert (x, q) -> Insert (x, sup_pred q p)
              | p, Join (q, xq) -> Join (q, adjunct p xq);;

let rec getValueInMatchingMap _A
  a x1 = match a, x1 with a, [] -> None
    | a, b :: l ->
        (let (x, y) = b in
          (if eq _A a x then Some y else getValueInMatchingMap _A a l));;

let rec substitutionInSUKLabel _C
  x0 acc = match x0, acc with SUKLabel a, acc -> Some (SUKLabel a)
    | SUIdKLabel a, acc ->
        (match getValueInMatchingMap (equal_metaVar _C) a acc with None -> None
          | Some aa ->
            (match aa with KLabelSubs ab -> Some ab | KItemSubs _ -> None
              | KListSubs _ -> None | KSubs _ -> None | ListSubs _ -> None
              | SetSubs _ -> None | MapSubs _ -> None | BagSubs _ -> None))
    | SUKLabelFun (a, b), acc ->
        (match (substitutionInSUKLabel _C a acc, substitutionInSUKList _C b acc)
          with (None, _) -> None | (Some _, None) -> None
          | (Some x, Some y) -> Some (SUKLabelFun (x, y)))
and substitutionInSUBigKWithLabel _C
  x0 acc = match x0, acc with
    SUBigBag a, acc ->
      (match substitutionInSUBigKWithBag _C a acc with None -> None
        | Some aa -> Some (SUBigBag aa))
    | SUBigLabel a, acc ->
        (match substitutionInSUKLabel _C a acc with None -> None
          | Some aa -> Some (SUBigLabel aa))
and substitutionInSUKList _C
  x0 acc = match x0, acc with [], acc -> Some []
    | b :: l, acc ->
        (match b
          with ItemKl x ->
            (match substitutionInSUBigKWithLabel _C x acc with None -> None
              | Some xa ->
                (match substitutionInSUKList _C l acc with None -> None
                  | Some la -> Some (ItemKl xa :: la)))
          | IdKl x ->
            (match getValueInMatchingMap (equal_metaVar _C) x acc
              with None -> None | Some (KLabelSubs _) -> None
              | Some (KItemSubs _) -> None
              | Some (KListSubs xa) ->
                (match substitutionInSUKList _C l acc with None -> None
                  | Some la -> Some (xa @ la))
              | Some (KSubs _) -> None | Some (ListSubs _) -> None
              | Some (SetSubs _) -> None | Some (MapSubs _) -> None
              | Some (BagSubs _) -> None))
and substitutionInSUKItem _C
  x0 acc = match x0, acc with
    SUKItem (l, r, ty), acc ->
      (match (substitutionInSUKLabel _C l acc, substitutionInSUKList _C r acc)
        with (None, _) -> None | (Some _, None) -> None
        | (Some x, Some y) -> Some (SUKItem (x, y, ty)))
    | SUHOLE a, acc -> Some (SUHOLE a)
    | SUIdKItem (a, b), acc ->
        (match getValueInMatchingMap (equal_metaVar _C) a acc with None -> None
          | Some aa ->
            (match aa with KLabelSubs _ -> None | KItemSubs ab -> Some ab
              | KListSubs _ -> None | KSubs _ -> None | ListSubs _ -> None
              | SetSubs _ -> None | MapSubs _ -> None | BagSubs _ -> None))
and substitutionInSUK _C
  x0 acc = match x0, acc with [], acc -> Some []
    | b :: l, acc ->
        (match b
          with ItemFactor x ->
            (match substitutionInSUKItem _C x acc with None -> None
              | Some xa ->
                (match substitutionInSUK _C l acc with None -> None
                  | Some la -> Some (ItemFactor xa :: la)))
          | IdFactor x ->
            (match getValueInMatchingMap (equal_metaVar _C) x acc
              with None -> None | Some (KLabelSubs _) -> None
              | Some (KItemSubs _) -> None | Some (KListSubs _) -> None
              | Some (KSubs xa) ->
                (match substitutionInSUK _C l acc with None -> None
                  | Some la -> Some (xa @ la))
              | Some (ListSubs _) -> None | Some (SetSubs _) -> None
              | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
          | SUKKItem (x, y, ty) ->
            (match
              (substitutionInSUKLabel _C x acc,
                (substitutionInSUKList _C y acc, substitutionInSUK _C l acc))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) ->
                Some (SUKKItem (xa, ya, ty) :: la)))
and substitutionInSUMap _C
  x0 acc = match x0, acc with [], acc -> Some []
    | b :: l, acc ->
        (match b
          with ItemM (x, y) ->
            (match
              (substitutionInSUK _C x acc,
                (substitutionInSUK _C y acc, substitutionInSUMap _C l acc))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) -> Some (ItemM (xa, ya) :: la))
          | IdM x ->
            (match getValueInMatchingMap (equal_metaVar _C) x acc
              with None -> None | Some (KLabelSubs _) -> None
              | Some (KItemSubs _) -> None | Some (KListSubs _) -> None
              | Some (KSubs _) -> None | Some (ListSubs _) -> None
              | Some (SetSubs _) -> None
              | Some (MapSubs xa) ->
                (match substitutionInSUMap _C l acc with None -> None
                  | Some la -> Some (xa @ la))
              | Some (BagSubs _) -> None)
          | SUMapKItem (x, y) ->
            (match
              (substitutionInSUKLabel _C x acc,
                (substitutionInSUKList _C y acc, substitutionInSUMap _C l acc))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) ->
                Some (SUMapKItem (xa, ya) :: la)))
and substitutionInSUSet _C
  x0 acc = match x0, acc with [], acc -> Some []
    | b :: l, acc ->
        (match b
          with ItemS x ->
            (match substitutionInSUK _C x acc with None -> None
              | Some xa ->
                (match substitutionInSUSet _C l acc with None -> None
                  | Some la -> Some (ItemS xa :: la)))
          | IdS x ->
            (match getValueInMatchingMap (equal_metaVar _C) x acc
              with None -> None | Some (KLabelSubs _) -> None
              | Some (KItemSubs _) -> None | Some (KListSubs _) -> None
              | Some (KSubs _) -> None | Some (ListSubs _) -> None
              | Some (SetSubs xa) ->
                (match substitutionInSUSet _C l acc with None -> None
                  | Some la -> Some (xa @ la))
              | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
          | SUSetKItem (x, y) ->
            (match
              (substitutionInSUKLabel _C x acc,
                (substitutionInSUKList _C y acc, substitutionInSUSet _C l acc))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) ->
                Some (SUSetKItem (xa, ya) :: la)))
and substitutionInSUList _C
  x0 acc = match x0, acc with [], acc -> Some []
    | b :: l, acc ->
        (match b
          with ItemL x ->
            (match substitutionInSUK _C x acc with None -> None
              | Some xa ->
                (match substitutionInSUList _C l acc with None -> None
                  | Some la -> Some (ItemL xa :: la)))
          | IdL x ->
            (match getValueInMatchingMap (equal_metaVar _C) x acc
              with None -> None | Some (KLabelSubs _) -> None
              | Some (KItemSubs _) -> None | Some (KListSubs _) -> None
              | Some (KSubs _) -> None
              | Some (ListSubs xa) ->
                (match substitutionInSUList _C l acc with None -> None
                  | Some la -> Some (xa @ la))
              | Some (SetSubs _) -> None | Some (MapSubs _) -> None
              | Some (BagSubs _) -> None)
          | SUListKItem (x, y) ->
            (match
              (substitutionInSUKLabel _C x acc,
                (substitutionInSUKList _C y acc, substitutionInSUList _C l acc))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) ->
                Some (SUListKItem (xa, ya) :: la)))
and substitutionInSUBigKWithBag _C
  x0 acc = match x0, acc with
    SUK a, acc ->
      (match substitutionInSUK _C a acc with None -> None
        | Some aa -> Some (SUK aa))
    | SUList a, acc ->
        (match substitutionInSUList _C a acc with None -> None
          | Some aa -> Some (SUList aa))
    | SUSet a, acc ->
        (match substitutionInSUSet _C a acc with None -> None
          | Some aa -> Some (SUSet aa))
    | SUMap a, acc ->
        (match substitutionInSUMap _C a acc with None -> None
          | Some aa -> Some (SUMap aa))
    | SUBag a, acc ->
        (match substitutionInSUBag _C a acc with None -> None
          | Some aa -> Some (SUBag aa))
and substitutionInSUBag _C
  x0 acc = match x0, acc with [], acc -> Some []
    | b :: l, acc ->
        (match b
          with ItemB (x, y, z) ->
            (match substitutionInSUBigKWithBag _C z acc with None -> None
              | Some za ->
                (match substitutionInSUBag _C l acc with None -> None
                  | Some la -> Some (ItemB (x, y, za) :: la)))
          | IdB x ->
            (match getValueInMatchingMap (equal_metaVar _C) x acc
              with None -> None | Some (KLabelSubs _) -> None
              | Some (KItemSubs _) -> None | Some (KListSubs _) -> None
              | Some (KSubs _) -> None | Some (ListSubs _) -> None
              | Some (SetSubs _) -> None | Some (MapSubs _) -> None
              | Some (BagSubs xa) ->
                (match substitutionInSUBag _C l acc with None -> None
                  | Some la -> Some (xa @ la))));;

let rec substitutionInSubsFactor _C
  x0 acc = match x0, acc with
    KLabelSubs a, acc ->
      (match substitutionInSUKLabel _C a acc with None -> None
        | Some aa -> Some (KLabelSubs aa))
    | KItemSubs a, acc ->
        (match substitutionInSUKItem _C a acc with None -> None
          | Some aa -> Some (KItemSubs aa))
    | KListSubs a, acc ->
        (match substitutionInSUKList _C a acc with None -> None
          | Some aa -> Some (KListSubs aa))
    | KSubs a, acc ->
        (match substitutionInSUK _C a acc with None -> None
          | Some aa -> Some (KSubs aa))
    | ListSubs a, acc ->
        (match substitutionInSUList _C a acc with None -> None
          | Some aa -> Some (ListSubs aa))
    | SetSubs a, acc ->
        (match substitutionInSUSet _C a acc with None -> None
          | Some aa -> Some (SetSubs aa))
    | MapSubs a, acc ->
        (match substitutionInSUMap _C a acc with None -> None
          | Some aa -> Some (MapSubs aa))
    | BagSubs a, acc ->
        (match substitutionInSUBag _C a acc with None -> None
          | Some aa -> Some (BagSubs aa));;

let rec syntacticMonoidInSUKLabel _A _B _C
  x0 s subG = match x0, s, subG with
    SUKLabel a, s, subG ->
      (match s
        with SUKLabel aa ->
          (if equal_labela _A a aa then Some (SUKLabel a) else None)
        | SUIdKLabel _ -> None | SUKLabelFun (_, _) -> None)
    | SUIdKLabel a, b, subG ->
        (match b with SUKLabel _ -> None
          | SUIdKLabel aa ->
            (if equal_metaVara _C a aa then Some (SUIdKLabel a) else None)
          | SUKLabelFun (_, _) -> None)
    | SUKLabelFun (a, ba), b, subG ->
        (match b with SUKLabel _ -> None | SUIdKLabel _ -> None
          | SUKLabelFun (aa, bb) ->
            (match syntacticMonoidInSUKLabel _A _B _C a aa subG
              with None -> None
              | Some a1 ->
                (match syntacticMonoidInSUKList _A _B _C ba bb subG
                  with None -> None
                  | Some baa -> Some (SUKLabelFun (a1, baa)))))
and syntacticMonoidInSUBigKWithLabel _A _B _C
  x0 b subG = match x0, b, subG with
    SUBigBag a, b, subG ->
      (match b
        with SUBigBag aa ->
          (match syntacticMonoidInSUBigKWithBag _A _B _C a aa subG
            with None -> None | Some aaa -> Some (SUBigBag aaa))
        | SUBigLabel _ -> None)
    | SUBigLabel a, b, subG ->
        (match b with SUBigBag _ -> None
          | SUBigLabel aa ->
            (match syntacticMonoidInSUKLabel _A _B _C a aa subG
              with None -> None | Some aaa -> Some (SUBigLabel aaa)))
and syntacticMonoidInSUKList _A _B _C
  x0 s subG = match x0, s, subG with
    [], s, subG -> (match s with [] -> Some [] | _ :: _ -> None)
    | b :: l, s, subG ->
        (match s with [] -> None
          | ba :: la ->
            (match (b, ba)
              with (ItemKl bs, ItemKl bsa) ->
                (match syntacticMonoidInSUBigKWithLabel _A _B _C bs bsa subG
                  with None -> None
                  | Some bsaa ->
                    (match syntacticMonoidInSUKList _A _B _C l la subG
                      with None -> None
                      | Some laa -> Some (ItemKl bsaa :: laa)))
              | (ItemKl _, IdKl _) -> None | (IdKl _, ItemKl _) -> None
              | (IdKl x, IdKl xa) ->
                (if equal_metaVara _C x xa
                  then (match syntacticMonoidInSUKList _A _B _C l la subG
                         with None -> None | Some laa -> Some (IdKl x :: laa))
                  else None)))
and syntacticMonoidInSUKItem _A _B _C
  x0 s subG = match x0, s, subG with
    SUKItem (l, r, ty), s, subG ->
      (match s
        with SUKItem (la, ra, tya) ->
          (match
            (syntacticMonoidInSUKLabel _A _B _C l la subG,
              syntacticMonoidInSUKList _A _B _C r ra subG)
            with (None, _) -> None | (Some _, None) -> None
            | (Some laa, Some raa) ->
              (match meet (equal_sort _A) ty tya subG with [] -> None
                | x :: xl -> Some (SUKItem (laa, raa, x :: xl))))
        | SUIdKItem (_, _) -> None | SUHOLE _ -> None)
    | SUHOLE a, s, subG ->
        (match s with SUKItem (_, _, _) -> None | SUIdKItem (_, _) -> None
          | SUHOLE aa ->
            (match meet (equal_sort _A) a aa subG with [] -> None
              | x :: xl -> Some (SUHOLE (x :: xl))))
    | SUIdKItem (a, ba), b, subG ->
        (match b with SUKItem (_, _, _) -> None
          | SUIdKItem (aa, bb) ->
            (if equal_metaVara _C a aa
              then (match meet (equal_sort _A) ba bb subG with [] -> None
                     | x :: xl -> Some (SUIdKItem (a, x :: xl)))
              else None)
          | SUHOLE _ -> None)
and syntacticMonoidInSUK _A _B _C
  x0 s subG = match x0, s, subG with
    [], s, subG -> (match s with [] -> Some [] | _ :: _ -> None)
    | b :: l, s, subG ->
        (match s with [] -> None
          | ba :: la ->
            (match (b, ba)
              with (ItemFactor (SUKItem (suKLabel, list1, list2)), ItemFactor x)
                -> (match
                     (syntacticMonoidInSUKItem _A _B _C
                        (SUKItem (suKLabel, list1, list2)) x subG,
                       syntacticMonoidInSUK _A _B _C l la subG)
                     with (None, _) -> None | (Some _, None) -> None
                     | (Some xa, Some laa) -> Some (ItemFactor xa :: laa))
              | (ItemFactor (SUKItem (_, _, _)), IdFactor _) -> None
              | (ItemFactor (SUKItem (_, _, _)), SUKKItem (_, _, _)) -> None
              | (ItemFactor (SUIdKItem (metaVar, lista)), ItemFactor x) ->
                (match
                  (syntacticMonoidInSUKItem _A _B _C
                     (SUIdKItem (metaVar, lista)) x subG,
                    syntacticMonoidInSUK _A _B _C l la subG)
                  with (None, _) -> None | (Some _, None) -> None
                  | (Some xa, Some laa) -> Some (ItemFactor xa :: laa))
              | (ItemFactor (SUIdKItem (metaVar, lista)), IdFactor x) ->
                (if equal_metaVara _C metaVar x
                  then (match syntacticMonoidInSUK _A _B _C l la subG
                         with None -> None
                         | Some laa ->
                           Some (ItemFactor (SUIdKItem (metaVar, lista)) ::
                                  laa))
                  else None)
              | (ItemFactor (SUIdKItem (_, _)), SUKKItem (_, _, _)) -> None
              | (ItemFactor (SUHOLE lista), ItemFactor x) ->
                (match
                  (syntacticMonoidInSUKItem _A _B _C (SUHOLE lista) x subG,
                    syntacticMonoidInSUK _A _B _C l la subG)
                  with (None, _) -> None | (Some _, None) -> None
                  | (Some xa, Some laa) -> Some (ItemFactor xa :: laa))
              | (ItemFactor (SUHOLE _), IdFactor _) -> None
              | (ItemFactor (SUHOLE _), SUKKItem (_, _, _)) -> None
              | (IdFactor _, ItemFactor (SUKItem (_, _, _))) -> None
              | (IdFactor x, ItemFactor (SUIdKItem (xa, ty))) ->
                (if equal_metaVara _C x xa
                  then (match syntacticMonoidInSUK _A _B _C l la subG
                         with None -> None
                         | Some laa ->
                           Some (ItemFactor (SUIdKItem (xa, ty)) :: laa))
                  else None)
              | (IdFactor _, ItemFactor (SUHOLE _)) -> None
              | (IdFactor x, IdFactor xa) ->
                (if equal_metaVara _C x xa
                  then (match syntacticMonoidInSUK _A _B _C l la subG
                         with None -> None
                         | Some laa -> Some (IdFactor x :: laa))
                  else None)
              | (IdFactor _, SUKKItem (_, _, _)) -> None
              | (SUKKItem (_, _, _), ItemFactor _) -> None
              | (SUKKItem (_, _, _), IdFactor _) -> None
              | (SUKKItem (x, y, ty), SUKKItem (xa, ya, tya)) ->
                (match
                  (syntacticMonoidInSUKLabel _A _B _C x xa subG,
                    (syntacticMonoidInSUKList _A _B _C y ya subG,
                      syntacticMonoidInSUK _A _B _C l la subG))
                  with (None, _) -> None | (Some _, (None, _)) -> None
                  | (Some _, (Some _, None)) -> None
                  | (Some xaa, (Some yaa, Some laa)) ->
                    (match meet (equal_sort _A) ty tya subG with [] -> None
                      | newTy :: newTyl ->
                        Some (SUKKItem (xaa, yaa, newTy :: newTyl) :: laa)))))
and syntacticMonoidInSUList _A _B _C
  x0 s subG = match x0, s, subG with
    [], s, subG -> (match s with [] -> Some [] | _ :: _ -> None)
    | b :: l, s, subG ->
        (match s with [] -> None
          | ba :: la ->
            (match (b, ba)
              with (ItemL x, ItemL xa) ->
                (match
                  (syntacticMonoidInSUK _A _B _C x xa subG,
                    syntacticMonoidInSUList _A _B _C l la subG)
                  with (None, _) -> None | (Some _, None) -> None
                  | (Some xaa, Some laa) -> Some (ItemL xaa :: laa))
              | (ItemL _, IdL _) -> None | (ItemL _, SUListKItem (_, _)) -> None
              | (IdL _, ItemL _) -> None
              | (IdL x, IdL xa) ->
                (if equal_metaVara _C x xa
                  then (match syntacticMonoidInSUList _A _B _C l la subG
                         with None -> None | Some laa -> Some (IdL x :: laa))
                  else None)
              | (IdL _, SUListKItem (_, _)) -> None
              | (SUListKItem (_, _), ItemL _) -> None
              | (SUListKItem (_, _), IdL _) -> None
              | (SUListKItem (x, y), SUListKItem (xa, ya)) ->
                (match
                  (syntacticMonoidInSUKLabel _A _B _C x xa subG,
                    (syntacticMonoidInSUKList _A _B _C y ya subG,
                      syntacticMonoidInSUList _A _B _C l la subG))
                  with (None, _) -> None | (Some _, (None, _)) -> None
                  | (Some _, (Some _, None)) -> None
                  | (Some xaa, (Some yaa, Some laa)) ->
                    Some (SUListKItem (xaa, yaa) :: laa))))
and syntacticMonoidInSUMember _A _B _C
  b x1 subG = match b, x1, subG with b, [], subG -> None
    | ba, b :: l, subG ->
        (match (ba, b)
          with (ItemS x, ItemS xa) ->
            (match syntacticMonoidInSUK _A _B _C xa x subG
              with None -> syntacticMonoidInSUMember _A _B _C ba l subG
              | Some xaa -> Some (ItemS xaa))
          | (ItemS _, IdS _) -> None | (ItemS _, SUSetKItem (_, _)) -> None
          | (IdS _, ItemS _) -> None
          | (IdS x, IdS xa) ->
            (if equal_metaVara _C x xa then Some (IdS x)
              else syntacticMonoidInSUMember _A _B _C ba l subG)
          | (IdS _, SUSetKItem (_, _)) -> None
          | (SUSetKItem (_, _), ItemS _) -> None
          | (SUSetKItem (_, _), IdS _) -> None
          | (SUSetKItem (x, y), SUSetKItem (xa, ya)) ->
            (match
              (syntacticMonoidInSUKLabel _A _B _C xa x subG,
                syntacticMonoidInSUKList _A _B _C ya y subG)
              with (None, _) -> syntacticMonoidInSUMember _A _B _C ba l subG
              | (Some _, None) -> syntacticMonoidInSUMember _A _B _C ba l subG
              | (Some xaa, Some yaa) -> Some (SUSetKItem (xaa, yaa))))
and syntacticMonoidInSUSubSet _A _B _C
  x0 t subG = match x0, t, subG with [], t, subG -> Some []
    | b :: l, t, subG ->
        (match syntacticMonoidInSUMember _A _B _C b t subG with None -> None
          | Some ba ->
            (match syntacticMonoidInSUSubSet _A _B _C l t subG with None -> None
              | Some la -> Some (ba :: la)))
and syntacticMonoidInSUSet _A _B _C
  x0 s t subG = match x0, s, t, subG with
    [], s, t, subG -> syntacticMonoidInSUSubSet _A _B _C s t subG
    | b :: l, s, t, subG ->
        (match syntacticMonoidInSUMember _A _B _C b s subG with None -> None
          | Some _ -> syntacticMonoidInSUSet _A _B _C l s t subG)
and syntacticMonoidInSUMapMember _A _B _C
  b x1 subG = match b, x1, subG with b, [], subG -> None
    | ba, b :: l, subG ->
        (match (ba, b)
          with (ItemM (x, y), ItemM (xa, ya)) ->
            (match syntacticMonoidInSUK _A _B _C xa x subG
              with None -> syntacticMonoidInSUMapMember _A _B _C ba l subG
              | Some xaa ->
                (match syntacticMonoidInSUK _A _B _C ya y subG with None -> None
                  | Some yaa -> Some (ItemM (xaa, yaa))))
          | (ItemM (_, _), IdM _) -> None
          | (ItemM (_, _), SUMapKItem (_, _)) -> None
          | (IdM _, ItemM (_, _)) -> None
          | (IdM x, IdM xa) ->
            (if equal_metaVara _C x xa then Some (IdM x)
              else syntacticMonoidInSUMapMember _A _B _C ba l subG)
          | (IdM _, SUMapKItem (_, _)) -> None
          | (SUMapKItem (_, _), ItemM (_, _)) -> None
          | (SUMapKItem (_, _), IdM _) -> None
          | (SUMapKItem (x, y), SUMapKItem (xa, ya)) ->
            (match
              (syntacticMonoidInSUKLabel _A _B _C xa x subG,
                syntacticMonoidInSUKList _A _B _C ya y subG)
              with (None, _) -> syntacticMonoidInSUMapMember _A _B _C ba l subG
              | (Some _, None) ->
                syntacticMonoidInSUMapMember _A _B _C ba l subG
              | (Some xaa, Some yaa) -> Some (SUMapKItem (xaa, yaa))))
and syntacticMonoidInSUSubMap _A _B _C
  x0 t subG = match x0, t, subG with [], t, subG -> Some []
    | b :: l, t, subG ->
        (match syntacticMonoidInSUMapMember _A _B _C b t subG with None -> None
          | Some ba ->
            (match syntacticMonoidInSUSubMap _A _B _C l t subG with None -> None
              | Some la -> Some (ba :: la)))
and syntacticMonoidInSUMap _A _B _C
  x0 s t subG = match x0, s, t, subG with
    [], s, t, subG -> syntacticMonoidInSUSubMap _A _B _C s t subG
    | b :: l, s, t, subG ->
        (match syntacticMonoidInSUMapMember _A _B _C b s subG with None -> None
          | Some _ -> syntacticMonoidInSUMap _A _B _C l s t subG)
and syntacticMonoidInSUBigKWithBag _A _B _C
  x0 b subG = match x0, b, subG with
    SUK a, b, subG ->
      (match b
        with SUK aa ->
          (match syntacticMonoidInSUK _A _B _C a aa subG with None -> None
            | Some aaa -> Some (SUK aaa))
        | SUList _ -> None | SUSet _ -> None | SUMap _ -> None
        | SUBag _ -> None)
    | SUList a, b, subG ->
        (match b with SUK _ -> None
          | SUList aa ->
            (match syntacticMonoidInSUList _A _B _C a aa subG with None -> None
              | Some aaa -> Some (SUList aaa))
          | SUSet _ -> None | SUMap _ -> None | SUBag _ -> None)
    | SUSet a, b, subG ->
        (match b with SUK _ -> None | SUList _ -> None
          | SUSet aa ->
            (match syntacticMonoidInSUSet _A _B _C a aa a subG with None -> None
              | Some aaa -> Some (SUSet aaa))
          | SUMap _ -> None | SUBag _ -> None)
    | SUMap a, b, subG ->
        (match b with SUK _ -> None | SUList _ -> None | SUSet _ -> None
          | SUMap aa ->
            (match syntacticMonoidInSUMap _A _B _C a aa a subG with None -> None
              | Some aaa -> Some (SUMap aaa))
          | SUBag _ -> None)
    | SUBag a, b, subG ->
        (match b with SUK _ -> None | SUList _ -> None | SUSet _ -> None
          | SUMap _ -> None
          | SUBag aa ->
            (match syntacticMonoidInSUBag _A _B _C a aa subG with None -> None
              | Some aaa -> Some (SUBag aaa)))
and syntacticMonoidInSUBagMember _A _B _C
  b x1 subG = match b, x1, subG with b, [], subG -> None
    | ba, b :: l, subG ->
        (match (ba, b)
          with (ItemB (x, y, z), ItemB (xa, _, za)) ->
            (if equal_var _B x xa
              then (match syntacticMonoidInSUBigKWithBag _A _B _C za z subG
                     with None -> None
                     | Some zaa -> Some (ItemB (x, y, zaa), l))
              else (match syntacticMonoidInSUBagMember _A _B _C ba l subG
                     with None -> None | Some (baa, la) -> Some (baa, b :: la)))
          | (ItemB (_, _, _), IdB _) ->
            (match syntacticMonoidInSUBagMember _A _B _C ba l subG
              with None -> None | Some (baa, la) -> Some (baa, b :: la))
          | (IdB _, ItemB (_, _, _)) ->
            (match syntacticMonoidInSUBagMember _A _B _C ba l subG
              with None -> None | Some (baa, la) -> Some (baa, b :: la))
          | (IdB x, IdB xa) ->
            (if equal_metaVara _C x xa then Some (IdB x, l)
              else (match syntacticMonoidInSUBagMember _A _B _C ba l subG
                     with None -> None
                     | Some (baa, la) -> Some (baa, IdB xa :: la))))
and syntacticMonoidInSUBag _A _B _C
  x0 s subG = match x0, s, subG with
    [], s, subG -> (match s with [] -> Some [] | _ :: _ -> None)
    | b :: l, s, subG ->
        (match syntacticMonoidInSUBagMember _A _B _C b s subG with None -> None
          | Some (ba, sa) ->
            (match syntacticMonoidInSUBag _A _B _C l sa subG with None -> None
              | Some la -> Some (ba :: la)));;

let rec macroEquality _A _B _C
  x0 x1 subG = match x0, x1, subG with
    KLabelSubs a, KLabelSubs b, subG ->
      (match syntacticMonoidInSUKLabel _A _B _C a b subG with None -> None
        | Some aa -> Some (KLabelSubs aa))
    | KItemSubs a, KItemSubs b, subG ->
        (match syntacticMonoidInSUKItem _A _B _C a b subG with None -> None
          | Some aa -> Some (KItemSubs aa))
    | KListSubs a, KListSubs b, subG ->
        (match syntacticMonoidInSUKList _A _B _C a b subG with None -> None
          | Some aa -> Some (KListSubs aa))
    | KSubs a, KSubs b, subG ->
        (match syntacticMonoidInSUK _A _B _C a b subG with None -> None
          | Some aa -> Some (KSubs aa))
    | ListSubs a, ListSubs b, subG ->
        (match syntacticMonoidInSUList _A _B _C a b subG with None -> None
          | Some aa -> Some (ListSubs aa))
    | SetSubs a, SetSubs b, subG ->
        (match syntacticMonoidInSUSet _A _B _C a b a subG with None -> None
          | Some aa -> Some (SetSubs aa))
    | MapSubs a, MapSubs b, subG ->
        (match syntacticMonoidInSUMap _A _B _C a b a subG with None -> None
          | Some aa -> Some (MapSubs aa))
    | BagSubs a, BagSubs b, subG ->
        (match syntacticMonoidInSUBag _A _B _C a b subG with None -> None
          | Some aa -> Some (BagSubs aa))
    | KItemSubs v, KLabelSubs va, subG -> None
    | KItemSubs v, KListSubs va, subG -> None
    | KItemSubs v, KSubs va, subG -> None
    | KItemSubs v, ListSubs va, subG -> None
    | KItemSubs v, SetSubs va, subG -> None
    | KItemSubs v, MapSubs va, subG -> None
    | KItemSubs v, BagSubs va, subG -> None
    | KListSubs v, KLabelSubs va, subG -> None
    | KListSubs v, KItemSubs va, subG -> None
    | KListSubs v, KSubs va, subG -> None
    | KListSubs v, ListSubs va, subG -> None
    | KListSubs v, SetSubs va, subG -> None
    | KListSubs v, MapSubs va, subG -> None
    | KListSubs v, BagSubs va, subG -> None
    | KSubs v, KLabelSubs va, subG -> None
    | KSubs v, KItemSubs va, subG -> None
    | KSubs v, KListSubs va, subG -> None
    | KSubs v, ListSubs va, subG -> None
    | KSubs v, SetSubs va, subG -> None
    | KSubs v, MapSubs va, subG -> None
    | KSubs v, BagSubs va, subG -> None
    | ListSubs v, KLabelSubs va, subG -> None
    | ListSubs v, KItemSubs va, subG -> None
    | ListSubs v, KListSubs va, subG -> None
    | ListSubs v, KSubs va, subG -> None
    | ListSubs v, SetSubs va, subG -> None
    | ListSubs v, MapSubs va, subG -> None
    | ListSubs v, BagSubs va, subG -> None
    | SetSubs v, KLabelSubs va, subG -> None
    | SetSubs v, KItemSubs va, subG -> None
    | SetSubs v, KListSubs va, subG -> None
    | SetSubs v, KSubs va, subG -> None
    | SetSubs v, ListSubs va, subG -> None
    | SetSubs v, MapSubs va, subG -> None
    | SetSubs v, BagSubs va, subG -> None
    | MapSubs v, KLabelSubs va, subG -> None
    | MapSubs v, KItemSubs va, subG -> None
    | MapSubs v, KListSubs va, subG -> None
    | MapSubs v, KSubs va, subG -> None
    | MapSubs v, ListSubs va, subG -> None
    | MapSubs v, SetSubs va, subG -> None
    | MapSubs v, BagSubs va, subG -> None
    | BagSubs v, KLabelSubs va, subG -> None
    | BagSubs v, KItemSubs va, subG -> None
    | BagSubs v, KListSubs va, subG -> None
    | BagSubs v, KSubs va, subG -> None
    | BagSubs v, ListSubs va, subG -> None
    | BagSubs v, SetSubs va, subG -> None
    | BagSubs v, MapSubs va, subG -> None
    | KLabelSubs va, KItemSubs v, subG -> None
    | KLabelSubs va, KListSubs v, subG -> None
    | KLabelSubs va, KSubs v, subG -> None
    | KLabelSubs va, ListSubs v, subG -> None
    | KLabelSubs va, SetSubs v, subG -> None
    | KLabelSubs va, MapSubs v, subG -> None
    | KLabelSubs va, BagSubs v, subG -> None;;

let rec updateMatchingMapMacro _A _B _C _D
  x y xa2 subG = match x, y, xa2, subG with x, y, [], subG -> Some [(x, y)]
    | x, y, (a, b) :: l, subG ->
        (if eq _A x a
          then (match macroEquality _B _C _D y b subG with None -> None
                 | Some ya -> Some ((a, ya) :: l))
          else (match updateMatchingMapMacro _A _B _C _D x y l subG
                 with None -> None | Some la -> Some ((a, b) :: la)));;

let rec patternMacroingInSUKLabel _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with
    IRKLabel a, s, acc, subG ->
      (match s
        with SUKLabel b -> (if equal_labela _A a b then Some acc else None)
        | SUIdKLabel _ -> None | SUKLabelFun (_, _) -> None)
    | IRIdKLabel a, s, acc, subG ->
        updateMatchingMapMacro (equal_metaVar _B) _A _C _D a (KLabelSubs s) acc
          subG;;

let rec subsortListAux _A
  a x1 subG = match a, x1, subG with a, [], subG -> false
    | a, x :: l, subG ->
        (if subsort _A a x subG then true else subsortListAux _A a l subG);;

let rec subsortList _A
  x0 b subG = match x0, b, subG with [], b, subG -> true
    | x :: l, b, subG ->
        (if subsortListAux _A x b subG then subsortList _A l b subG
          else false);;

let rec searchAllNonTermsInSUSet
  = function [] -> []
    | a :: l ->
        (match a with ItemS _ -> searchAllNonTermsInSUSet l
          | IdS _ -> a :: searchAllNonTermsInSUSet l
          | SUSetKItem (_, _) -> a :: searchAllNonTermsInSUSet l);;

let rec mergePatMatchMap _A _B _C _D
  x0 s subG = match x0, s, subG with [], s, subG -> Some s
    | (a, b) :: l, s, subG ->
        (match updateMatchingMapMacro _A _B _C _D a b s subG with None -> None
          | Some sa -> mergePatMatchMap _A _B _C _D l sa subG);;

let rec mergeMapWithOnes _C _D _E _F
  x0 acc subG = match x0, acc, subG with [], acc, subG -> Some acc
    | (a, (b, c)) :: l, acc, subG ->
        (match mergePatMatchMap _C _D _E _F c acc subG with None -> None
          | Some acca -> mergeMapWithOnes _C _D _E _F l acca subG);;

let rec findBijection _B
  l = (match searchOne _B l [] with None -> None
        | Some a ->
          (let (ones, aa) = a in
            (match aa with [] -> Some (ones, [])
              | (ab, b) :: al ->
                (if null al then Some (ones, b)
                  else findBijectionAux _B ab b al))))
and findBijectionAux _B
  a x1 s = match a, x1, s with a, [], s -> None
    | a, (b, c) :: al, s ->
        (match searchOne _B (eliminateEntryList _B b s) []
          with None -> findBijectionAux _B a al s
          | Some (ones, mores) ->
            (if null mores then Some ((a, (b, c)) :: ones, [])
              else (match findBijection _B mores with None -> None
                     | Some (onesa, remains) ->
                       Some ((a, (b, c)) :: ones @ onesa, remains))));;

let rec keys = function [] -> []
               | (a, b) :: l -> a :: keys l;;

let rec searchAllNonTermsInSUMap
  = function [] -> []
    | a :: l ->
        (match a with ItemM (_, _) -> searchAllNonTermsInSUMap l
          | IdM _ -> a :: searchAllNonTermsInSUMap l
          | SUMapKItem (_, _) -> a :: searchAllNonTermsInSUMap l);;

let rec searchAllNonTermsInSUBag
  = function [] -> []
    | a :: l ->
        (match a with ItemB (_, _, _) -> searchAllNonTermsInSUBag l
          | IdB _ -> a :: searchAllNonTermsInSUBag l);;

let rec patternMacroingInSUKList _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with
    KListPatNoVar l, s, acc, subG ->
      (match l with [] -> (match s with [] -> Some acc | _ :: _ -> None)
        | la :: ll ->
          (match s with [] -> None
            | ItemKl x :: sul ->
              (match patternMacroingInSUBigKWithLabel _A _B _C _D la x acc subG
                with None -> None
                | Some acca ->
                  (match
                    patternMacroingInSUKList _A _B _C _D (KListPatNoVar ll) sul
                      acca subG
                    with None -> None | Some a -> Some a))
            | IdKl _ :: _ -> None))
    | KListPat (l, n, r), s, acc, subG ->
        (match l
          with [] ->
            (match rev r
              with [] ->
                updateMatchingMapMacro (equal_metaVar _C) _A _B _D n
                  (KListSubs s) acc subG
              | ra :: rl ->
                (match rev s with [] -> None
                  | ItemKl x :: sul ->
                    (match
                      patternMacroingInSUBigKWithLabel _A _B _C _D ra x acc subG
                      with None -> None
                      | Some acca ->
                        (match
                          patternMacroingInSUKList _A _B _C _D
                            (KListPat (l, n, rev rl)) (rev sul) acca subG
                          with None -> None | Some a -> Some a))
                  | IdKl _ :: _ -> None))
          | la :: ll ->
            (match s with [] -> None
              | ItemKl x :: sul ->
                (match
                  patternMacroingInSUBigKWithLabel _A _B _C _D la x acc subG
                  with None -> None
                  | Some acca ->
                    (match
                      patternMacroingInSUKList _A _B _C _D (KListPat (ll, n, r))
                        sul acca subG
                      with None -> None | Some a -> Some a))
              | IdKl _ :: _ -> None))
and patternMacroingInSUKItem _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with
    IRKItem (l, r, ty), s, acc, subG ->
      (match s
        with SUKItem (la, ra, tya) ->
          (if subsortList (equal_sort _A) tya ty subG
            then (match patternMacroingInSUKLabel _A _C _B _D l la acc subG
                   with None -> None
                   | Some acca ->
                     (match patternMacroingInSUKList _A _B _C _D r ra acca subG
                       with None -> None | Some a -> Some a))
            else None)
        | SUIdKItem (_, _) -> None | SUHOLE _ -> None)
    | IRHOLE a, s, acc, subG ->
        (match s with SUKItem (_, _, _) -> None | SUIdKItem (_, _) -> None
          | SUHOLE aa ->
            (if subsortList (equal_sort _A) aa a subG then Some acc else None))
    | IRIdKItem (a, ba), b, acc, subG ->
        (match b
          with SUKItem (l, r, ty) ->
            (if subsortList (equal_sort _A) ty ba subG
              then updateMatchingMapMacro (equal_metaVar _C) _A _B _D a
                     (KItemSubs (SUKItem (l, r, ty))) acc subG
              else None)
          | SUIdKItem (aa, bb) ->
            (if subsortList (equal_sort _A) bb ba subG
              then updateMatchingMapMacro (equal_metaVar _C) _A _B _D a
                     (KItemSubs (SUIdKItem (aa, bb))) acc subG
              else None)
          | SUHOLE _ -> None)
and patternMacroingInSUK _A _B _C _D
  (KPat (l, n)) s acc subG =
    (match l
      with [] ->
        (match n with None -> (match s with [] -> Some acc | _ :: _ -> None)
          | Some v ->
            updateMatchingMapMacro (equal_metaVar _C) _A _B _D v (KSubs s) acc
              subG)
      | la :: ll ->
        (match s with [] -> None
          | ItemFactor x :: sul ->
            (match patternMacroingInSUKItem _A _B _C _D la x acc subG
              with None -> None
              | Some acca ->
                patternMacroingInSUK _A _B _C _D (KPat (ll, n)) sul acca subG)
          | IdFactor x :: sul ->
            (match la with IRKItem (_, _, _) -> None
              | IRIdKItem (xa, ty) ->
                (if equal_lista (equal_sort _A) ty [K]
                  then (match
                         updateMatchingMapMacro (equal_metaVar _C) _A _B _D xa
                           (KSubs [IdFactor x]) acc subG
                         with None -> None
                         | Some acca ->
                           patternMacroingInSUK _A _B _C _D (KPat (ll, n)) sul
                             acca subG)
                  else None)
              | IRHOLE _ -> None)
          | SUKKItem (x, y, ty) :: sul ->
            (match la with IRKItem (_, _, _) -> None
              | IRIdKItem (xa, _) ->
                (if equal_lista (equal_sort _A) ty [K]
                  then (match
                         updateMatchingMapMacro (equal_metaVar _C) _A _B _D xa
                           (KSubs [SUKKItem (x, y, ty)]) acc subG
                         with None -> None
                         | Some acca ->
                           patternMacroingInSUK _A _B _C _D (KPat (ll, n)) sul
                             acca subG)
                  else None)
              | IRHOLE _ -> None)))
and patternMacroingInSUList _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with
    ListPatNoVar l, s, acc, subG ->
      (match l with [] -> (match s with [] -> Some acc | _ :: _ -> None)
        | la :: ll ->
          (match s with [] -> None
            | ItemL x :: sul ->
              (match patternMacroingInSUK _A _B _C _D la x acc subG
                with None -> None
                | Some acca ->
                  patternMacroingInSUList _A _B _C _D (ListPatNoVar ll) sul acca
                    subG)
            | IdL _ :: _ -> None | SUListKItem (_, _) :: _ -> None))
    | ListPat (l, n, r), s, acc, subG ->
        (match l
          with [] ->
            (match rev r
              with [] ->
                updateMatchingMapMacro (equal_metaVar _C) _A _B _D n
                  (ListSubs s) acc subG
              | ra :: rl ->
                (match rev s with [] -> None
                  | ItemL x :: sul ->
                    (match patternMacroingInSUK _A _B _C _D ra x acc subG
                      with None -> None
                      | Some acca ->
                        patternMacroingInSUList _A _B _C _D
                          (ListPat (l, n, rev rl)) (rev sul) acca subG)
                  | IdL _ :: _ -> None | SUListKItem (_, _) :: _ -> None))
          | la :: ll ->
            (match s with [] -> None
              | ItemL x :: sul ->
                (match patternMacroingInSUK _A _B _C _D la x acc subG
                  with None -> None
                  | Some acca ->
                    patternMacroingInSUList _A _B _C _D (ListPat (ll, n, r)) sul
                      acca subG)
              | IdL _ :: _ -> None | SUListKItem (_, _) :: _ -> None))
and patternMacroingInSUMember _A _B _C _D
  a x1 acc subG = match a, x1, acc, subG with a, [], acc, subG -> (a, [])
    | a, t :: l, acc, subG ->
        (match t
          with ItemS x ->
            (match patternMacroingInSUK _A _B _C _D a x acc subG
              with None -> patternMacroingInSUMember _A _B _C _D a l acc subG
              | Some acca ->
                (let (u, v) = patternMacroingInSUMember _A _B _C _D a l acc subG
                   in
                  (u, (t, acca) :: v)))
          | IdS _ -> patternMacroingInSUMember _A _B _C _D a l acc subG
          | SUSetKItem (_, _) ->
            patternMacroingInSUMember _A _B _C _D a l acc subG)
and patternMacroingInSUSetAux _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with [], s, acc, subG -> []
    | a :: l, s, acc, subG ->
        patternMacroingInSUMember _A _B _C _D a s acc subG ::
          patternMacroingInSUSetAux _A _B _C _D l s acc subG
and patternMacroingInSUSet _A _B _C _D
  (SetPat (l, n)) s acc subG =
    (match
      findBijection (equal_suS _A _B _D)
        (patternMacroingInSUSetAux _A _B _C _D l s acc subG)
      with None -> None
      | Some (ones, remains) ->
        (match n
          with None ->
            (if null (searchAllNonTermsInSUSet s) && null remains
              then mergeMapWithOnes (equal_metaVar _C) _A _B _D ones acc subG
              else None)
          | Some var ->
            (match
              updateMatchingMapMacro (equal_metaVar _C) _A _B _D var
                (SetSubs (searchAllNonTermsInSUSet s @ keys remains)) acc subG
              with None -> None
              | Some acca ->
                mergeMapWithOnes (equal_metaVar _C) _A _B _D ones acca subG)))
and patternMacroingInSUMapMember _A _B _C _D
  a x1 acc subG = match a, x1, acc, subG with a, [], acc, subG -> (a, [])
    | a, t :: l, acc, subG ->
        (let (b, c) = a in
          (match t
            with ItemM (x, y) ->
              (match patternMacroingInSUK _A _B _C _D b x acc subG
                with None ->
                  patternMacroingInSUMapMember _A _B _C _D a l acc subG
                | Some acca ->
                  (match patternMacroingInSUK _A _B _C _D c y acca subG
                    with None ->
                      patternMacroingInSUMapMember _A _B _C _D a l acc subG
                    | Some accaa ->
                      (let (u, v) =
                         patternMacroingInSUMapMember _A _B _C _D a l acc subG
                         in
                        (u, (t, accaa) :: v))))
            | IdM _ -> patternMacroingInSUMapMember _A _B _C _D a l acc subG
            | SUMapKItem (_, _) ->
              patternMacroingInSUMapMember _A _B _C _D a l acc subG))
and patternMacroingInSUMapAux _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with [], s, acc, subG -> []
    | a :: l, s, acc, subG ->
        patternMacroingInSUMapMember _A _B _C _D a s acc subG ::
          patternMacroingInSUMapAux _A _B _C _D l s acc subG
and patternMacroingInSUMap _A _B _C _D
  (MapPat (l, n)) s acc subG =
    (match
      findBijection (equal_suM _A _B _D)
        (patternMacroingInSUMapAux _A _B _C _D l s acc subG)
      with None -> None
      | Some (ones, remains) ->
        (match n
          with None ->
            (if null (searchAllNonTermsInSUMap s) && null remains
              then mergeMapWithOnes (equal_metaVar _C) _A _B _D ones acc subG
              else None)
          | Some var ->
            (match
              updateMatchingMapMacro (equal_metaVar _C) _A _B _D var
                (MapSubs (searchAllNonTermsInSUMap s @ keys remains)) acc subG
              with None -> None
              | Some acca ->
                mergeMapWithOnes (equal_metaVar _C) _A _B _D ones acca subG)))
and patternMacroingInSUBigKWithBag _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with
    IRK t, s, acc, subG ->
      (match s with SUK r -> patternMacroingInSUK _A _B _C _D t r acc subG
        | SUList _ -> None | SUSet _ -> None | SUMap _ -> None
        | SUBag _ -> None)
    | IRBag t, s, acc, subG ->
        (match s with SUK _ -> None | SUList _ -> None | SUSet _ -> None
          | SUMap _ -> None
          | SUBag r -> patternMacroingInSUBag _A _B _C _D t r acc subG)
    | IRList t, s, acc, subG ->
        (match s with SUK _ -> None
          | SUList r -> patternMacroingInSUList _A _B _C _D t r acc subG
          | SUSet _ -> None | SUMap _ -> None | SUBag _ -> None)
    | IRSet t, s, acc, subG ->
        (match s with SUK _ -> None | SUList _ -> None
          | SUSet r -> patternMacroingInSUSet _A _B _C _D t r acc subG
          | SUMap _ -> None | SUBag _ -> None)
    | IRMap t, s, acc, subG ->
        (match s with SUK _ -> None | SUList _ -> None | SUSet _ -> None
          | SUMap r -> patternMacroingInSUMap _A _B _C _D t r acc subG
          | SUBag _ -> None)
and patternMacroingInSUBagMember _A _B _C _D
  a x1 acc subG = match a, x1, acc, subG with a, [], acc, subG -> (a, [])
    | a, t :: l, acc, subG ->
        (let (b, (_, d)) = a in
          (match t
            with ItemB (x, _, z) ->
              (if equal_var _A b x
                then (match
                       patternMacroingInSUBigKWithBag _B _A _C _D d z acc subG
                       with None ->
                         patternMacroingInSUBagMember _A _B _C _D a l acc subG
                       | Some acca ->
                         (let (u, v) =
                            patternMacroingInSUBagMember _A _B _C _D a l acc
                              subG
                            in
                           (u, (t, acca) :: v)))
                else patternMacroingInSUBagMember _A _B _C _D a l acc subG)
            | IdB _ -> patternMacroingInSUBagMember _A _B _C _D a l acc subG))
and patternMacroingInSUBagAux _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with [], s, acc, subG -> []
    | a :: l, s, acc, subG ->
        patternMacroingInSUBagMember _A _B _C _D a s acc subG ::
          patternMacroingInSUBagAux _A _B _C _D l s acc subG
and patternMacroingInSUBag _A _B _C _D
  (BagPat (l, n)) s acc subG =
    (match
      findBijection (equal_suB _A _B _D)
        (patternMacroingInSUBagAux _B _A _C _D l s acc subG)
      with None -> None
      | Some (ones, remains) ->
        (match n
          with None ->
            (if null (searchAllNonTermsInSUBag s) && null remains
              then mergeMapWithOnes (equal_metaVar _C) _A _B _D ones acc subG
              else None)
          | Some var ->
            (match
              updateMatchingMapMacro (equal_metaVar _C) _A _B _D var
                (BagSubs (searchAllNonTermsInSUBag s @ keys remains)) acc subG
              with None -> None
              | Some acca ->
                mergeMapWithOnes (equal_metaVar _C) _A _B _D ones acca subG)))
and patternMacroingInSUBigKWithLabel _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with
    IRBigBag t, s, acc, subG ->
      (match s
        with SUBigBag ta ->
          patternMacroingInSUBigKWithBag _A _B _C _D t ta acc subG
        | SUBigLabel _ -> None)
    | IRBigLabel t, s, acc, subG ->
        (match s with SUBigBag _ -> None
          | SUBigLabel ta ->
            patternMacroingInSUKLabel _A _C _B _D t ta acc subG);;

let rec isGroundTermInSUKItem
  = function
    SUKItem (l, r, ty) -> isGroundTermInSUKLabel l && isGroundTermInSUKList r
    | SUIdKItem (a, b) -> false
    | SUHOLE a -> true
and isGroundTermInSUK
  = function [] -> true
    | b :: l ->
        (match b
          with ItemFactor x -> isGroundTermInSUKItem x && isGroundTermInSUK l
          | IdFactor _ -> false
          | SUKKItem (x, y, _) ->
            isGroundTermInSUKLabel x &&
              (isGroundTermInSUKList y && isGroundTermInSUK l))
and isGroundTermInSUBigKWithBag = function SUK a -> isGroundTermInSUK a
                                  | SUList a -> isGroundTermInSUList a
                                  | SUSet a -> isGroundTermInSUSet a
                                  | SUMap a -> isGroundTermInSUMap a
                                  | SUBag a -> isGroundTermInSUBag a
and isGroundTermInSUBag
  = function [] -> true
    | b :: l ->
        (match b
          with ItemB (_, _, z) ->
            isGroundTermInSUBigKWithBag z && isGroundTermInSUBag l
          | IdB _ -> false)
and isGroundTermInSUBigKWithLabel
  = function SUBigBag a -> isGroundTermInSUBigKWithBag a
    | SUBigLabel a -> isGroundTermInSUKLabel a
and isGroundTermInSUKList
  = function [] -> true
    | b :: l ->
        (match b
          with ItemKl a ->
            isGroundTermInSUBigKWithLabel a && isGroundTermInSUKList l
          | IdKl _ -> false)
and isGroundTermInSUKLabel
  = function SUKLabel a -> true
    | SUKLabelFun (a, b) -> isGroundTermInSUKLabel a && isGroundTermInSUKList b
    | SUIdKLabel n -> false
and isGroundTermInSUMap
  = function [] -> true
    | b :: l ->
        (match b
          with ItemM (x, y) ->
            isGroundTermInSUK x &&
              (isGroundTermInSUK y && isGroundTermInSUMap l)
          | IdM _ -> false
          | SUMapKItem (x, y) ->
            isGroundTermInSUKLabel x &&
              (isGroundTermInSUKList y && isGroundTermInSUMap l))
and isGroundTermInSUSet
  = function [] -> true
    | b :: l ->
        (match b with ItemS x -> isGroundTermInSUK x && isGroundTermInSUSet l
          | IdS _ -> false
          | SUSetKItem (x, y) ->
            isGroundTermInSUKLabel x &&
              (isGroundTermInSUKList y && isGroundTermInSUSet l))
and isGroundTermInSUList
  = function [] -> true
    | b :: l ->
        (match b with ItemL x -> isGroundTermInSUK x && isGroundTermInSUList l
          | IdL _ -> false
          | SUListKItem (x, y) ->
            isGroundTermInSUKLabel x &&
              (isGroundTermInSUKList y && isGroundTermInSUList l));;

let rec isCommonElemInSUSet _A _B _C
  a x1 subG = match a, x1, subG with a, [], subG -> false
    | a, b :: l, subG ->
        (match a
          with ItemS v ->
            (match b
              with ItemS va ->
                (match syntacticMonoidInSUK _A _B _C v va subG
                  with None -> isCommonElemInSUSet _A _B _C a l subG
                  | Some _ -> true)
              | IdS _ -> isCommonElemInSUSet _A _B _C a l subG
              | SUSetKItem (_, _) -> isCommonElemInSUSet _A _B _C a l subG)
          | IdS x ->
            (match b with ItemS _ -> isCommonElemInSUSet _A _B _C a l subG
              | IdS xa ->
                (if equal_metaVara _C x xa then true
                  else isCommonElemInSUSet _A _B _C a l subG)
              | SUSetKItem (_, _) -> isCommonElemInSUSet _A _B _C a l subG)
          | SUSetKItem (x, y) ->
            (match b with ItemS _ -> isCommonElemInSUSet _A _B _C a l subG
              | IdS _ -> isCommonElemInSUSet _A _B _C a l subG
              | SUSetKItem (xa, ya) ->
                (match
                  (syntacticMonoidInSUKLabel _A _B _C x xa subG,
                    syntacticMonoidInSUKList _A _B _C y ya subG)
                  with (None, _) -> isCommonElemInSUSet _A _B _C a l subG
                  | (Some _, None) -> isCommonElemInSUSet _A _B _C a l subG
                  | (Some _, Some _) -> true)));;

let rec isCommonElemInSUMap _A _B _C
  a x1 subG = match a, x1, subG with a, [], subG -> false
    | a, b :: l, subG ->
        (match a
          with ItemM (v, w) ->
            (match b
              with ItemM (va, wa) ->
                (match syntacticMonoidInSUK _A _B _C v va subG
                  with None -> isCommonElemInSUMap _A _B _C a l subG
                  | Some _ ->
                    (match syntacticMonoidInSUK _A _B _C w wa subG
                      with None -> isCommonElemInSUMap _A _B _C a l subG
                      | Some _ -> true))
              | IdM _ -> isCommonElemInSUMap _A _B _C a l subG
              | SUMapKItem (_, _) -> isCommonElemInSUMap _A _B _C a l subG)
          | IdM x ->
            (match b with ItemM (_, _) -> isCommonElemInSUMap _A _B _C a l subG
              | IdM xa ->
                (if equal_metaVara _C x xa then true
                  else isCommonElemInSUMap _A _B _C a l subG)
              | SUMapKItem (_, _) -> isCommonElemInSUMap _A _B _C a l subG)
          | SUMapKItem (x, y) ->
            (match b with ItemM (_, _) -> isCommonElemInSUMap _A _B _C a l subG
              | IdM _ -> isCommonElemInSUMap _A _B _C a l subG
              | SUMapKItem (xa, ya) ->
                (match
                  (syntacticMonoidInSUKLabel _A _B _C x xa subG,
                    syntacticMonoidInSUKList _A _B _C y ya subG)
                  with (None, _) -> isCommonElemInSUMap _A _B _C a l subG
                  | (Some _, None) -> isCommonElemInSUMap _A _B _C a l subG
                  | (Some _, Some _) -> true)));;

let rec getValueInSUMap _A _B _C
  a x1 subG = match a, x1, subG with a, [], subG -> None
    | a, b :: l, subG ->
        (match b
          with ItemM (x, y) ->
            (match syntacticMonoidInSUK _A _B _C a x subG
              with None -> getValueInSUMap _A _B _C a l subG | Some _ -> Some y)
          | IdM _ -> getValueInSUMap _A _B _C a l subG
          | SUMapKItem (_, _) -> getValueInSUMap _A _B _C a l subG);;

let rec regularizeInSUKItem _A _B _C
  x0 subG = match x0, subG with
    SUKItem (l, r, ty), subG ->
      (match regularizeInSUKLabel _A _B _C l subG with None -> None
        | Some a ->
          (match regularizeInSUKList _A _B _C r subG with None -> None
            | Some b -> Some (SUKItem (a, b, ty))))
    | SUHOLE a, subG -> Some (SUHOLE a)
    | SUIdKItem (a, b), subG -> Some (SUIdKItem (a, b))
and regularizeInSUKElem _A _B _C
  x0 subG = match x0, subG with IdFactor x, subG -> Some (IdFactor x)
    | ItemFactor x, subG ->
        (match regularizeInSUKItem _A _B _C x subG with None -> None
          | Some xa -> Some (ItemFactor xa))
    | SUKKItem (x, y, z), subG ->
        (match regularizeInSUKLabel _A _B _C x subG with None -> None
          | Some xa ->
            (match regularizeInSUKList _A _B _C y subG with None -> None
              | Some ya -> Some (SUKKItem (xa, ya, z))))
and regularizeInSUK _A _B _C
  x0 subG = match x0, subG with [], subG -> Some []
    | b :: l, subG ->
        (match regularizeInSUKElem _A _B _C b subG with None -> None
          | Some ba ->
            (match regularizeInSUK _A _B _C l subG with None -> None
              | Some la -> Some (ba :: la)))
and regularizeInSUBigKWithBag _A _B _C
  x0 subG = match x0, subG with
    SUK a, subG ->
      (match regularizeInSUK _A _B _C a subG with None -> None
        | Some aa -> Some (SUK aa))
    | SUList a, subG ->
        (match regularizeInSUList _A _B _C a subG with None -> None
          | Some aa -> Some (SUList aa))
    | SUSet a, subG ->
        (match regularizeInSUSet _A _B _C a subG with None -> None
          | Some aa -> Some (SUSet aa))
    | SUMap a, subG ->
        (match regularizeInSUMap _A _B _C a subG with None -> None
          | Some aa -> Some (SUMap aa))
    | SUBag a, subG ->
        (match regularizeInSUBag _A _B _C a subG with None -> None
          | Some aa -> Some (SUBag aa))
and regularizeInSUBagElem _A _B _C
  x0 subG = match x0, subG with IdB x, subG -> Some (IdB x)
    | ItemB (x, y, z), subG ->
        (match regularizeInSUBigKWithBag _A _B _C z subG with None -> None
          | Some za -> Some (ItemB (x, y, za)))
and regularizeInSUBag _A _B _C
  x0 subG = match x0, subG with [], subG -> Some []
    | b :: l, subG ->
        (match regularizeInSUBagElem _A _B _C b subG with None -> None
          | Some ba ->
            (match regularizeInSUBag _A _B _C l subG with None -> None
              | Some la -> Some (ba :: la)))
and regularizeInSUBigKWithLabel _A _B _C
  x0 subG = match x0, subG with
    SUBigBag a, subG ->
      (match regularizeInSUBigKWithBag _A _B _C a subG with None -> None
        | Some aa -> Some (SUBigBag aa))
    | SUBigLabel a, subG ->
        (match regularizeInSUKLabel _A _B _C a subG with None -> None
          | Some aa -> Some (SUBigLabel aa))
and regularizeInSUKListElem _A _B _C
  x0 subG = match x0, subG with IdKl x, subG -> Some (IdKl x)
    | ItemKl x, subG ->
        (match regularizeInSUBigKWithLabel _A _B _C x subG with None -> None
          | Some xa -> Some (ItemKl xa))
and regularizeInSUKList _A _B _C
  x0 subG = match x0, subG with [], subG -> Some []
    | b :: l, subG ->
        (match regularizeInSUKListElem _A _B _C b subG with None -> None
          | Some ba ->
            (match regularizeInSUKList _A _B _C l subG with None -> None
              | Some la -> Some (ba :: la)))
and regularizeInSUKLabel _A _B _C
  x0 subG = match x0, subG with SUKLabel a, subG -> Some (SUKLabel a)
    | SUIdKLabel a, subG -> Some (SUIdKLabel a)
    | SUKLabelFun (a, b), subG ->
        (match regularizeInSUKLabel _A _B _C a subG with None -> None
          | Some aa ->
            (match regularizeInSUKList _A _B _C b subG with None -> None
              | Some ba -> Some (SUKLabelFun (aa, ba))))
and regularizeInSUMapElem _A _B _C
  x0 subG = match x0, subG with IdM x, subG -> Some (IdM x)
    | ItemM (x, y), subG ->
        (match regularizeInSUK _A _B _C x subG with None -> None
          | Some xa ->
            (match regularizeInSUK _A _B _C y subG with None -> None
              | Some ya -> Some (ItemM (xa, ya))))
    | SUMapKItem (x, y), subG ->
        (match regularizeInSUKLabel _A _B _C x subG with None -> None
          | Some xa ->
            (match regularizeInSUKList _A _B _C y subG with None -> None
              | Some ya -> Some (SUMapKItem (xa, ya))))
and regularizeInSUMap _A _B _C
  x0 subG = match x0, subG with [], subG -> Some []
    | b :: l, subG ->
        (match regularizeInSUMapElem _A _B _C b subG with None -> None
          | Some ba ->
            (match regularizeInSUMap _A _B _C l subG with None -> None
              | Some la ->
                (if isCommonElemInSUMap _A _B _C ba la subG then Some la
                  else (match ba
                         with ItemM (x, _) ->
                           (match getValueInSUMap _A _B _C x la subG
                             with None -> Some (ba :: la) | Some _ -> None)
                         | IdM _ -> Some (ba :: la)
                         | SUMapKItem (_, _) -> Some (ba :: la)))))
and regularizeInSUSetElem _A _B _C
  x0 subG = match x0, subG with IdS x, subG -> Some (IdS x)
    | ItemS x, subG ->
        (match regularizeInSUK _A _B _C x subG with None -> None
          | Some xa -> Some (ItemS xa))
    | SUSetKItem (x, y), subG ->
        (match regularizeInSUKLabel _A _B _C x subG with None -> None
          | Some xa ->
            (match regularizeInSUKList _A _B _C y subG with None -> None
              | Some ya -> Some (SUSetKItem (xa, ya))))
and regularizeInSUSet _A _B _C
  x0 subG = match x0, subG with [], subG -> Some []
    | b :: l, subG ->
        (match regularizeInSUSetElem _A _B _C b subG with None -> None
          | Some ba ->
            (match regularizeInSUSet _A _B _C l subG with None -> None
              | Some la ->
                (if isCommonElemInSUSet _A _B _C ba la subG then Some la
                  else Some (ba :: la))))
and regularizeInSUListElem _A _B _C
  x0 subG = match x0, subG with IdL x, subG -> Some (IdL x)
    | ItemL x, subG ->
        (match regularizeInSUK _A _B _C x subG with None -> None
          | Some xa -> Some (ItemL xa))
    | SUListKItem (x, y), subG ->
        (match regularizeInSUKLabel _A _B _C x subG with None -> None
          | Some xa ->
            (match regularizeInSUKList _A _B _C y subG with None -> None
              | Some ya -> Some (SUListKItem (xa, ya))))
and regularizeInSUList _A _B _C
  x0 subG = match x0, subG with [], subG -> Some []
    | b :: l, subG ->
        (match regularizeInSUListElem _A _B _C b subG with None -> None
          | Some ba ->
            (match regularizeInSUList _A _B _C l subG with None -> None
              | Some la -> Some (ba :: la)));;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (Suc n) xs
                     | n, [] -> n;;

let rec size_list x = gen_length Zero_nat x;;

let rec numberOfItemsInKList (_D1, _D2, _D3)
  = function [] -> zero _D3
    | x :: l ->
        (match x
          with ItemKl _ ->
            plus _D2 (one _D1) (numberOfItemsInKList (_D1, _D2, _D3) l)
          | IdKl _ -> numberOfItemsInKList (_D1, _D2, _D3) l);;

let rec hasIdInKList
  = function [] -> false
    | a :: l -> (match a with ItemKl _ -> hasIdInKList l | IdKl _ -> true);;

let rec getIdInSUKLabel = function SUIdKLabel a -> Some a
                          | SUKLabel v -> None
                          | SUKLabelFun (v, va) -> None;;

let rec getArgSortsMeaning _A
  a x1 = match a, x1 with a, [] -> None
    | aa, (v, (vs, (SingleTon a, (nl, b)))) :: l ->
        (if eq _A aa a then Some vs else getArgSortsMeaning _A aa l)
    | a, (v, (vs, (SetTon s, (nl, b)))) :: l ->
        (if s a then Some vs else getArgSortsMeaning _A a l);;

let rec getArgSort _A a database = getArgSortsMeaning _A a database;;

let rec getSortMeaning _A
  a x1 = match a, x1 with a, [] -> None
    | aa, (v, (vs, (SingleTon a, (nl, b)))) :: l ->
        (if eq _A aa a then Some v else getSortMeaning _A aa l)
    | a, (v, (vs, (SetTon s, (nl, b)))) :: l ->
        (if s a then Some v else getSortMeaning _A a l);;

let rec getSort _A a database = getSortMeaning _A a database;;

let rec checkTermsInSUKItem _A _C
  x0 maxTy acc beta database subG = match x0, maxTy, acc, beta, database, subG
    with
    SUKItem (l, r, ty), maxTy, acc, beta, database, subG ->
      (if subsortList (equal_sort _A) maxTy [K] subG &&
            subsortList (equal_sort _A) ty [K] subG
        then (match getSUKLabelMeaning l
               with None ->
                 (match checkTermsInSUKLabel _A _C l acc beta database subG
                   with None -> None
                   | Some (acca, (betaa, la)) ->
                     (match
                       checkTermsInNoneSUKList _A _C r acca betaa database subG
                       with None -> None
                       | Some (accaa, (betaaa, ra)) ->
                         (match meet (equal_sort _A) ty maxTy subG
                           with [] -> None
                           | tya :: tyl ->
                             (match getIdInSUKLabel la
                               with None ->
                                 Some (accaa,
(betaaa, SUKItem (la, ra, tya :: tyl)))
                               | Some newId ->
                                 (match
                                   updateBeta (equal_metaVar _C) (equal_sort _A)
                                     newId (tya :: tyl) accaa subG
                                   with None -> None
                                   | Some betab ->
                                     Some (accaa,
    (betab, SUKItem (la, ra, tya :: tyl))))))))
               | Some s ->
                 (match getSort (equal_label _A) s database with None -> None
                   | Some theTy ->
                     (match getArgSort (equal_label _A) s database
                       with None -> None
                       | Some tyl ->
                         (match
                           checkTermsInSUKList _A _C r tyl acc beta database
                             subG
                           with None -> None
                           | Some (acca, (betaa, ra)) ->
                             (if isFunctionItem (equal_label _A) s database
                               then (match
                                      meet (equal_sort _A) theTy
(meet (equal_sort _A) ty maxTy subG) subG
                                      with [] -> None
                                      | a :: lista ->
Some (acca, (betaa, SUKItem (l, ra, a :: lista))))
                               else (if subsortList (equal_sort _A) theTy ty
  subG &&
  subsortList (equal_sort _A) theTy maxTy subG
                                      then Some (acca,
          (betaa, SUKItem (l, ra, theTy)))
                                      else None))))))
        else None)
    | SUIdKItem (a, b), maxTy, acc, beta, database, subG ->
        (match meet (equal_sort _A) b maxTy subG with [] -> None
          | aa :: lista ->
            (match
              updateMap (equal_metaVar _C) (equal_sort _A) a (aa :: lista) acc
                subG
              with None -> None
              | Some acca -> Some (acca, (beta, SUIdKItem (a, aa :: lista)))))
    | SUHOLE a, maxTy, acc, beta, database, subG ->
        (match meet (equal_sort _A) a maxTy subG with [] -> None
          | aa :: lista -> Some (acc, (beta, SUHOLE (aa :: lista))))
and checkTermsInSUK _A _C
  l ty acc beta database subG =
    (if equal_lista (equal_sort _A) ty [K]
      then (match l with [] -> Some (acc, (beta, []))
             | ItemFactor x :: xl ->
               (match checkTermsInSUKItem _A _C x [K] acc beta database subG
                 with None -> None
                 | Some (acca, (betaa, xa)) ->
                   (match checkTermsInSUK _A _C xl ty acca betaa database subG
                     with None -> None
                     | Some (accaa, (betaaa, xla)) ->
                       Some (accaa, (betaaa, ItemFactor xa :: xla))))
             | IdFactor x :: xl ->
               (match
                 updateMap (equal_metaVar _C) (equal_sort _A) x [K] acc subG
                 with None -> None
                 | Some acca ->
                   (match checkTermsInSUK _A _C xl ty acca beta database subG
                     with None -> None
                     | Some (accaa, (betaa, xla)) ->
                       Some (accaa, (betaa, IdFactor x :: xla))))
             | SUKKItem (a, b, tya) :: xl ->
               (if subsortList (equal_sort _A) tya [K] subG
                 then (match getSUKLabelMeaning a
                        with None ->
                          (match
                            checkTermsInSUKLabel _A _C a acc beta database subG
                            with None -> None
                            | Some aa ->
                              (let (acca, ab) = aa in
                               let (betaa, ac) = ab in
                                (match
                                  checkTermsInNoneSUKList _A _C b acca betaa
                                    database subG
                                  with None -> None
                                  | Some ba ->
                                    (let (accaa, bb) = ba in
                                     let (betaaa, bc) = bb in
                                      (match
checkTermsInSUK _A _C xl ty accaa betaaa database subG with None -> None
| Some (accb, (betab, xla)) ->
  Some (accb, (betab, SUKKItem (ac, bc, tya) :: xla)))))))
                        | Some s ->
                          (if isFunctionItem (equal_label _A) s database
                            then (match
                                   (getSort (equal_label _A) s database,
                                     getArgSort (equal_label _A) s database)
                                   with (None, _) -> None
                                   | (Some _, None) -> None
                                   | (Some tyaa, Some tyl) ->
                                     (match meet (equal_sort _A) tya tyaa subG
                                       with [] -> None
                                       | aa :: lista ->
 (match checkTermsInSUKList _A _C b tyl acc beta database subG with None -> None
   | Some ba ->
     (let (acca, bb) = ba in
      let (betaa, bc) = bb in
       (match checkTermsInSUK _A _C xl ty acca betaa database subG
         with None -> None
         | Some (accaa, (betaaa, xla)) ->
           Some (accaa, (betaaa, SUKKItem (a, bc, aa :: lista) :: xla)))))))
                            else None))
                 else None))
      else (if subsortList (equal_sort _A) ty [KItem] subG
             then (match l
                    with [ItemFactor a] ->
                      (match
                        checkTermsInSUKItem _A _C a ty acc beta database subG
                        with None -> None
                        | Some aa ->
                          (let (acca, ab) = aa in
                           let (betaa, ac) = ab in
                            Some (acca, (betaa, [ItemFactor ac]))))
                    | [IdFactor a] ->
                      (match
                        updateMap (equal_metaVar _C) (equal_sort _A) a ty acc
                          subG
                        with None -> None
                        | Some acca ->
                          Some (acca, (beta, [ItemFactor (SUIdKItem (a, ty))])))
                    | [SUKKItem (a, b, tya)] ->
                      (if subsortList (equal_sort _A) tya [K] subG
                        then (match getSUKLabelMeaning a
                               with None ->
                                 (match
                                   checkTermsInSUKLabel _A _C a acc beta
                                     database subG
                                   with None -> None
                                   | Some aa ->
                                     (let (acca, ab) = aa in
                                      let (betaa, ac) = ab in
                                       (match
 checkTermsInNoneSUKList _A _C b acca betaa database subG with None -> None
 | Some ba ->
   (let (accaa, bb) = ba in
    let (betaaa, bc) = bb in
     (match meet (equal_sort _A) ty tya subG with [] -> None
       | aaa :: lista ->
         Some (accaa, (betaaa, [SUKKItem (ac, bc, aaa :: lista)])))))))
                               | Some s ->
                                 (if isFunctionItem (equal_label _A) s database
                                   then (let (Some theTy, Some tyl) =
   (getSort (equal_label _A) s database, getArgSort (equal_label _A) s database)
   in
  (match checkTermsInSUKList _A _C b tyl acc beta database subG
    with None -> None
    | Some ba ->
      (let (acca, bb) = ba in
       let (betaa, bc) = bb in
        (match
          meet (equal_sort _A) ty (meet (equal_sort _A) tya theTy subG) subG
          with [] -> None
          | aa :: lista ->
            Some (acca, (betaa, [SUKKItem (a, bc, aa :: lista)]))))))
                                   else None))
                        else None))
             else None))
and checkTermsInSUBigKWithBag _A _C
  x0 ty acc beta database subG = match x0, ty, acc, beta, database, subG with
    SUK a, ty, acc, beta, database, subG ->
      (match ty
        with None ->
          (match checkTermsInSUK _A _C a [K] acc beta database subG
            with None -> None
            | Some aa -> (let (acca, ab) = aa in
                          let (betaa, ac) = ab in
                           Some (acca, (betaa, SUK ac))))
        | Some tya ->
          (if subsortList (equal_sort _A) tya [K] subG
            then (match checkTermsInSUK _A _C a [K] acc beta database subG
                   with None -> None
                   | Some aa ->
                     (let (acca, ab) = aa in
                      let (betaa, ac) = ab in
                       Some (acca, (betaa, SUK ac))))
            else None))
    | SUList a, ty, acc, beta, database, subG ->
        (match ty
          with None ->
            (match checkTermsInSUList _A _C a acc beta database subG
              with None -> None
              | Some aa ->
                (let (acca, ab) = aa in
                 let (betaa, ac) = ab in
                  Some (acca, (betaa, SUList ac))))
          | Some tya ->
            (if equal_lista (equal_sort _A) tya [List]
              then (match checkTermsInSUList _A _C a acc beta database subG
                     with None -> None
                     | Some aa ->
                       (let (acca, ab) = aa in
                        let (betaa, ac) = ab in
                         Some (acca, (betaa, SUList ac))))
              else None))
    | SUSet a, ty, acc, beta, database, subG ->
        (match ty
          with None ->
            (match checkTermsInSUSet _A _C a acc beta database subG
              with None -> None
              | Some aa ->
                (let (acca, ab) = aa in
                 let (betaa, ac) = ab in
                  Some (acca, (betaa, SUSet ac))))
          | Some tya ->
            (if equal_lista (equal_sort _A) tya [Seta]
              then (match checkTermsInSUSet _A _C a acc beta database subG
                     with None -> None
                     | Some aa ->
                       (let (acca, ab) = aa in
                        let (betaa, ac) = ab in
                         Some (acca, (betaa, SUSet ac))))
              else None))
    | SUMap a, ty, acc, beta, database, subG ->
        (match ty
          with None ->
            (match checkTermsInSUMap _A _C a acc beta database subG
              with None -> None
              | Some aa ->
                (let (acca, ab) = aa in
                 let (betaa, ac) = ab in
                  Some (acca, (betaa, SUMap ac))))
          | Some tya ->
            (if equal_lista (equal_sort _A) tya [Map]
              then (match checkTermsInSUMap _A _C a acc beta database subG
                     with None -> None
                     | Some aa ->
                       (let (acca, ab) = aa in
                        let (betaa, ac) = ab in
                         Some (acca, (betaa, SUMap ac))))
              else None))
    | SUBag a, ty, acc, beta, database, subG ->
        (match ty
          with None ->
            (match checkTermsInSUBag _A _C a acc beta database subG
              with None -> None
              | Some aa ->
                (let (acca, ab) = aa in
                 let (betaa, ac) = ab in
                  Some (acca, (betaa, SUBag ac))))
          | Some tya ->
            (if equal_lista (equal_sort _A) tya [Bag]
              then (match checkTermsInSUBag _A _C a acc beta database subG
                     with None -> None
                     | Some aa ->
                       (let (acca, ab) = aa in
                        let (betaa, ac) = ab in
                         Some (acca, (betaa, SUBag ac))))
              else None))
and checkTermsInSUBag _A _C
  x0 acc beta database subG = match x0, acc, beta, database, subG with
    [], acc, beta, database, subG -> Some (acc, (beta, []))
    | b :: l, acc, beta, database, subG ->
        (match b
          with ItemB (x, y, z) ->
            (match checkTermsInSUBigKWithBag _A _C z None acc beta database subG
              with None -> None
              | Some (acca, (betaa, za)) ->
                (match checkTermsInSUBag _A _C l acca betaa database subG
                  with None -> None
                  | Some (accaa, (betaaa, la)) ->
                    Some (accaa, (betaaa, ItemB (x, y, za) :: la))))
          | IdB x ->
            (match updateMap (equal_metaVar _C) (equal_sort _A) x [Bag] acc subG
              with None -> None
              | Some acca ->
                (match checkTermsInSUBag _A _C l acca beta database subG
                  with None -> None
                  | Some (accaa, (betaa, la)) ->
                    Some (accaa, (betaa, IdB x :: la)))))
and checkTermsInSUBigKWithLabel _A _C
  x0 ty acc beta database subG = match x0, ty, acc, beta, database, subG with
    SUBigBag a, ty, acc, beta, database, subG ->
      (match checkTermsInSUBigKWithBag _A _C a ty acc beta database subG
        with None -> None
        | Some aa ->
          (let (acca, ab) = aa in
           let (betaa, ac) = ab in
            Some (acca, (betaa, SUBigBag ac))))
    | SUBigLabel a, ty, acc, beta, database, subG ->
        (match ty
          with None ->
            (match checkTermsInSUKLabel _A _C a acc beta database subG
              with None -> None
              | Some aa ->
                (let (acca, ab) = aa in
                 let (betaa, ac) = ab in
                  Some (acca, (betaa, SUBigLabel ac))))
          | Some tya ->
            (if equal_lista (equal_sort _A) tya [KLabel]
              then (match checkTermsInSUKLabel _A _C a acc beta database subG
                     with None -> None
                     | Some aa ->
                       (let (acca, ab) = aa in
                        let (betaa, ac) = ab in
                         Some (acca, (betaa, SUBigLabel ac))))
              else None))
and checkTermsInSUKListAux _A _C
  x0 tyl acc beta database subG = match x0, tyl, acc, beta, database, subG with
    [], tyl, acc, beta, database, subG -> Some (acc, (beta, ([], [])))
    | b :: l, tyl, acc, beta, database, subG ->
        (match b
          with ItemKl x ->
            (match tyl with [] -> None
              | ty :: tyla ->
                (match
                  checkTermsInSUBigKWithLabel _A _C x (Some ty) acc beta
                    database subG
                  with None -> None
                  | Some (acca, (betaa, xa)) ->
                    (match
                      checkTermsInSUKListAux _A _C l tyla acca betaa database
                        subG
                      with None -> None
                      | Some (accaa, (betaaa, (lb, la))) ->
                        Some (accaa, (betaaa, (ItemKl xa :: lb, la))))))
          | IdKl x ->
            (match
              updateMap (equal_metaVar _C) (equal_sort _A) x [KList] acc subG
              with None -> None
              | Some acca -> Some (acca, (beta, ([], b :: l)))))
and checkTermsInNoneSUKList _A _C
  x0 acc beta database subG = match x0, acc, beta, database, subG with
    [], acc, beta, database, subG -> Some (acc, (beta, []))
    | x :: l, acc, beta, database, subG ->
        (match x
          with ItemKl a ->
            (match
              checkTermsInSUBigKWithLabel _A _C a None acc beta database subG
              with None -> None
              | Some aa ->
                (let (_, ab) = aa in
                 let (_, ac) = ab in
                  (match checkTermsInNoneSUKList _A _C l acc beta database subG
                    with None -> None
                    | Some (acca, (betaa, la)) ->
                      Some (acca, (betaa, ItemKl ac :: la)))))
          | IdKl a ->
            (match
              updateMap (equal_metaVar _C) (equal_sort _A) a [KList] acc subG
              with None -> None
              | Some acca ->
                (match checkTermsInNoneSUKList _A _C l acca beta database subG
                  with None -> None
                  | Some (accaa, (betaa, la)) ->
                    Some (accaa, (betaa, IdKl a :: la)))))
and checkTermsInSUKList _A _C
  l tyl acc beta database subG =
    (if less_nat (size_list tyl)
          (numberOfItemsInKList (one_nat, plus_nat, zero_nat) l)
      then None
      else (if hasIdInKList l
             then (match
                    checkTermsInSUKListAux _A _C l tyl acc beta database subG
                    with None -> None
                    | Some (acca, (betaa, (la, lb))) ->
                      (match
                        checkTermsInSUKListAux _A _C (rev lb) (rev tyl) acca
                          betaa database subG
                        with None -> None
                        | Some (accaa, (betaaa, (laa, lba))) ->
                          (if null lba then Some (accaa, (betaaa, la @ rev laa))
                            else (match
                                   checkTermsInNoneSUKList _A _C (rev lba) accaa
                                     betaaa database subG
                                   with None -> None
                                   | Some (accb, (betab, lbb)) ->
                                     Some (accb,
    (betab, la @ lbb @ rev laa))))))
             else (if equal_nata
                        (numberOfItemsInKList (one_nat, plus_nat, zero_nat) l)
                        (size_list tyl)
                    then (match
                           checkTermsInSUKListAux _A _C l tyl acc beta database
                             subG
                           with None -> None
                           | Some (acca, (betaa, (la, []))) ->
                             Some (acca, (betaa, la))
                           | Some (_, (_, (_, _ :: _))) -> None)
                    else None)))
and checkTermsInSUKLabel _A _C
  x0 acc beta database subG = match x0, acc, beta, database, subG with
    SUKLabel a, acc, beta, database, subG -> Some (acc, (beta, SUKLabel a))
    | SUKLabelFun (a, b), acc, beta, database, subG ->
        (match getSUKLabelMeaning a
          with None ->
            (match checkTermsInSUKLabel _A _C a acc beta database subG
              with None -> None
              | Some aa ->
                (let (acca, ab) = aa in
                 let (betaa, ac) = ab in
                  (match
                    checkTermsInNoneSUKList _A _C b acca betaa database subG
                    with None -> None
                    | Some ba ->
                      (let (accaa, bb) = ba in
                       let (betaaa, bc) = bb in
                        (match getIdInSUKLabel ac
                          with None ->
                            Some (accaa, (betaaa, SUKLabelFun (ac, bc)))
                          | Some x ->
                            (match
                              updateMap (equal_metaVar _C) (equal_sort _A) x
                                [KLabel] betaaa subG
                              with None -> None
                              | Some betab ->
                                Some (accaa,
                                       (betab, SUKLabelFun (ac, bc)))))))))
          | Some s ->
            (if isFunctionItem (equal_label _A) s database
              then (match getArgSort (equal_label _A) s database
                     with None -> None
                     | Some l ->
                       (match getSort (equal_label _A) s database
                         with None -> None
                         | Some ty ->
                           (if subsortList (equal_sort _A) ty [KLabel] subG
                             then (match
                                    checkTermsInSUKList _A _C b l acc beta
                                      database subG
                                    with None -> None
                                    | Some ba ->
                                      (let (acca, bb) = ba in
                                       let (betaa, bc) = bb in
Some (acca, (betaa, SUKLabelFun (a, bc)))))
                             else None)))
              else None))
    | SUIdKLabel n, acc, beta, database, subG ->
        (match updateMap (equal_metaVar _C) (equal_sort _A) n [KLabel] acc subG
          with None -> None | Some acca -> Some (acca, (beta, SUIdKLabel n)))
and checkTermsInSUMap _A _C
  x0 acc beta database subG = match x0, acc, beta, database, subG with
    [], acc, beta, database, subG -> Some (acc, (beta, []))
    | b :: l, acc, beta, database, subG ->
        (match b
          with ItemM (x, y) ->
            (match checkTermsInSUK _A _C x [K] acc beta database subG
              with None -> None
              | Some (acca, (betaa, xa)) ->
                (match checkTermsInSUK _A _C y [K] acca betaa database subG
                  with None -> None
                  | Some (accaa, (betaaa, ya)) ->
                    (match checkTermsInSUMap _A _C l accaa betaaa database subG
                      with None -> None
                      | Some (accb, (betab, la)) ->
                        Some (accb, (betab, ItemM (xa, ya) :: la)))))
          | IdM x ->
            (match updateMap (equal_metaVar _C) (equal_sort _A) x [Map] acc subG
              with None -> None
              | Some acca ->
                (match checkTermsInSUMap _A _C l acca beta database subG
                  with None -> None
                  | Some (accaa, (betaa, la)) ->
                    Some (accaa, (betaa, IdM x :: la))))
          | SUMapKItem (x, y) ->
            (match getSUKLabelMeaning x
              with None ->
                (match checkTermsInSUKLabel _A _C x acc beta database subG
                  with None -> None
                  | Some (acca, (betaa, xa)) ->
                    (match
                      checkTermsInNoneSUKList _A _C y acca betaa database subG
                      with None -> None
                      | Some (accaa, (betaaa, ya)) ->
                        (match
                          checkTermsInSUMap _A _C l accaa betaaa database subG
                          with None -> None
                          | Some (accb, (betab, la)) ->
                            (match getIdInSUKLabel xa
                              with None ->
                                Some (accb, (betab, SUMapKItem (xa, ya) :: la))
                              | Some xx ->
                                (match
                                  updateMap (equal_metaVar _C) (equal_sort _A)
                                    xx [Map] betab subG
                                  with None -> None
                                  | Some betac ->
                                    Some (accb,
   (betac, SUMapKItem (xa, ya) :: la)))))))
              | Some s ->
                (if isFunctionItem (equal_label _A) s database
                  then (match
                         (getSort (equal_label _A) s database,
                           getArgSort (equal_label _A) s database)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some ty, Some tyl) ->
                           (if subsortList (equal_sort _A) ty [Map] subG
                             then (match
                                    checkTermsInSUKList _A _C y tyl acc beta
                                      database subG
                                    with None -> None
                                    | Some (acca, (betaa, ya)) ->
                                      (match
checkTermsInSUMap _A _C l acca betaa database subG with None -> None
| Some (accaa, (betaaa, la)) ->
  Some (accaa, (betaaa, SUMapKItem (x, ya) :: la))))
                             else None))
                  else None)))
and checkTermsInSUSet _A _C
  x0 acc beta database subG = match x0, acc, beta, database, subG with
    [], acc, beta, database, subG -> Some (acc, (beta, []))
    | b :: l, acc, beta, database, subG ->
        (match b
          with ItemS x ->
            (match checkTermsInSUK _A _C x [K] acc beta database subG
              with None -> None
              | Some (acca, (betaa, xa)) ->
                (match checkTermsInSUSet _A _C l acca betaa database subG
                  with None -> None
                  | Some (accaa, (betaaa, la)) ->
                    Some (accaa, (betaaa, ItemS xa :: la))))
          | IdS x ->
            (match
              updateMap (equal_metaVar _C) (equal_sort _A) x [Seta] acc subG
              with None -> None
              | Some acca ->
                (match checkTermsInSUSet _A _C l acca beta database subG
                  with None -> None
                  | Some (accaa, (betaa, la)) ->
                    Some (accaa, (betaa, IdS x :: la))))
          | SUSetKItem (x, y) ->
            (match getSUKLabelMeaning x
              with None ->
                (match checkTermsInSUKLabel _A _C x acc beta database subG
                  with None -> None
                  | Some (acca, (betaa, xa)) ->
                    (match
                      checkTermsInNoneSUKList _A _C y acca betaa database subG
                      with None -> None
                      | Some (accaa, (betaaa, ya)) ->
                        (match
                          checkTermsInSUSet _A _C l accaa betaaa database subG
                          with None -> None
                          | Some (accb, (betab, la)) ->
                            (match getIdInSUKLabel xa
                              with None ->
                                Some (accb, (betab, SUSetKItem (xa, ya) :: la))
                              | Some xx ->
                                (match
                                  updateMap (equal_metaVar _C) (equal_sort _A)
                                    xx [Seta] betab subG
                                  with None -> None
                                  | Some betac ->
                                    Some (accb,
   (betac, SUSetKItem (xa, ya) :: la)))))))
              | Some s ->
                (if isFunctionItem (equal_label _A) s database
                  then (match
                         (getSort (equal_label _A) s database,
                           getArgSort (equal_label _A) s database)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some ty, Some tyl) ->
                           (if subsortList (equal_sort _A) ty [Seta] subG
                             then (match
                                    checkTermsInSUKList _A _C y tyl acc beta
                                      database subG
                                    with None -> None
                                    | Some (acca, (betaa, ya)) ->
                                      (match
checkTermsInSUSet _A _C l acca betaa database subG with None -> None
| Some (accaa, (betaaa, la)) ->
  Some (accaa, (betaaa, SUSetKItem (x, ya) :: la))))
                             else None))
                  else None)))
and checkTermsInSUList _A _C
  x0 acc beta database subG = match x0, acc, beta, database, subG with
    [], acc, beta, database, subG -> Some (acc, (beta, []))
    | b :: l, acc, beta, database, subG ->
        (match b
          with ItemL x ->
            (match checkTermsInSUK _A _C x [K] acc beta database subG
              with None -> None
              | Some (acca, (betaa, xa)) ->
                (match checkTermsInSUList _A _C l acca betaa database subG
                  with None -> None
                  | Some (accaa, (betaaa, la)) ->
                    Some (accaa, (betaaa, ItemL xa :: la))))
          | IdL x ->
            (match
              updateMap (equal_metaVar _C) (equal_sort _A) x [List] acc subG
              with None -> None
              | Some acca ->
                (match checkTermsInSUList _A _C l acca beta database subG
                  with None -> None
                  | Some (accaa, (betaa, la)) ->
                    Some (accaa, (betaa, IdL x :: la))))
          | SUListKItem (x, y) ->
            (match getSUKLabelMeaning x
              with None ->
                (match checkTermsInSUKLabel _A _C x acc beta database subG
                  with None -> None
                  | Some (acca, (betaa, xa)) ->
                    (match
                      checkTermsInNoneSUKList _A _C y acca betaa database subG
                      with None -> None
                      | Some (accaa, (betaaa, ya)) ->
                        (match
                          checkTermsInSUList _A _C l accaa betaaa database subG
                          with None -> None
                          | Some (accb, (betab, la)) ->
                            (match getIdInSUKLabel xa
                              with None ->
                                Some (accb, (betab, SUListKItem (xa, ya) :: la))
                              | Some xx ->
                                (match
                                  updateMap (equal_metaVar _C) (equal_sort _A)
                                    xx [List] betab subG
                                  with None -> None
                                  | Some betac ->
                                    Some (accb,
   (betac, SUListKItem (xa, ya) :: la)))))))
              | Some s ->
                (if isFunctionItem (equal_label _A) s database
                  then (match
                         (getSort (equal_label _A) s database,
                           getArgSort (equal_label _A) s database)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some ty, Some tyl) ->
                           (if equal_lista (equal_sort _A) ty [List]
                             then (match
                                    checkTermsInSUKList _A _C y tyl acc beta
                                      database subG
                                    with None -> None
                                    | Some (acca, (betaa, ya)) ->
                                      (match
checkTermsInSUList _A _C l acca betaa database subG with None -> None
| Some (accaa, (betaaa, la)) ->
  Some (accaa, (betaaa, SUListKItem (x, ya) :: la))))
                             else None))
                  else None)));;

let rec typeCheckCondition _A _B _C
  a database subG =
    (if isGroundTermInSUKItem a
      then (match checkTermsInSUKItem _A _C a [Bool] [] [] database subG
             with None -> None
             | Some (_, (_, aa)) -> regularizeInSUKItem _A _B _C aa subG)
      else None);;

let rec getKLabelInSUKItem
  a = (match a with SUKItem (aa, _, _) -> getSUKLabelMeaning aa
        | SUIdKItem (_, _) -> None | SUHOLE _ -> None);;

let rec localteFunTermInSUKItem _A
  x0 database = match x0, database with
    SUKItem (x, y, z), database ->
      (match localteFunTermInSUKLabel _A x database
        with None ->
          (match localteFunTermInSUKList _A y database
            with None ->
              (match getSUKLabelMeaning x with None -> None
                | Some s ->
                  (if isFunctionItem (equal_label _A) s database
                    then Some (s, (y, (z, SUIdKItem (FunHole, z)))) else None))
            | Some (l, (funa, (ty, r))) ->
              Some (l, (funa, (ty, SUKItem (x, r, z)))))
        | Some (l, (funa, (ty, r))) ->
          Some (l, (funa, (ty, SUKItem (r, y, z)))))
    | SUIdKItem (x, y), database -> None
    | SUHOLE x, database -> None
and localteFunTermInSUK _A
  x0 database = match x0, database with [], database -> None
    | a :: l, database ->
        (match a
          with ItemFactor x ->
            (match localteFunTermInSUKItem _A x database
              with None ->
                (match localteFunTermInSUK _A l database with None -> None
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, a :: r))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, ItemFactor r :: l))))
          | IdFactor _ ->
            (match localteFunTermInSUK _A l database with None -> None
              | Some (la, (funa, (ty, r))) -> Some (la, (funa, (ty, a :: r))))
          | SUKKItem (x, y, z) ->
            (match localteFunTermInSUKLabel _A x database
              with None ->
                (match localteFunTermInSUKList _A y database
                  with None ->
                    (match localteFunTermInSUK _A l database
                      with None ->
                        (match getSUKLabelMeaning x with None -> None
                          | Some s ->
                            (if isFunctionItem (equal_label _A) s database
                              then Some (s,
  (y, (z, (if equal_lista (equal_sort _A) z [K] then IdFactor FunHole
            else ItemFactor (SUIdKItem (FunHole, z))) ::
            l)))
                              else None))
                      | Some (la, (funa, (ty, r))) ->
                        Some (la, (funa, (ty, a :: r))))
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, SUKKItem (x, r, z) :: l))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, SUKKItem (r, y, z) :: l)))))
and localteFunTermInSUBigKWithBag _A
  x0 database = match x0, database with
    SUK a, database ->
      (match localteFunTermInSUK _A a database with None -> None
        | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUK r))))
    | SUList a, database ->
        (match localteFunTermInSUList _A a database with None -> None
          | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUList r))))
    | SUSet a, database ->
        (match localteFunTermInSUSet _A a database with None -> None
          | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUSet r))))
    | SUMap a, database ->
        (match localteFunTermInSUMap _A a database with None -> None
          | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUMap r))))
    | SUBag a, database ->
        (match localteFunTermInSUBag _A a database with None -> None
          | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUBag r))))
and localteFunTermInSUBag _A
  x0 database = match x0, database with [], database -> None
    | a :: l, database ->
        (match a
          with ItemB (x, y, z) ->
            (match localteFunTermInSUBigKWithBag _A z database
              with None ->
                (match localteFunTermInSUBag _A l database with None -> None
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, a :: r))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, ItemB (x, y, r) :: l))))
          | IdB _ ->
            (match localteFunTermInSUBag _A l database with None -> None
              | Some (la, (funa, (ty, r))) -> Some (la, (funa, (ty, a :: r)))))
and localteFunTermInSUBigKWithLabel _A
  x0 database = match x0, database with
    SUBigBag a, database ->
      (match localteFunTermInSUBigKWithBag _A a database with None -> None
        | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUBigBag r))))
    | SUBigLabel a, database ->
        (match localteFunTermInSUKLabel _A a database with None -> None
          | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUBigLabel r))))
and localteFunTermInSUKList _A
  x0 database = match x0, database with [], database -> None
    | a :: l, database ->
        (match a
          with ItemKl x ->
            (match localteFunTermInSUBigKWithLabel _A x database
              with None ->
                (match localteFunTermInSUKList _A l database with None -> None
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, a :: r))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, ItemKl r :: l))))
          | IdKl _ ->
            (match localteFunTermInSUKList _A l database with None -> None
              | Some (la, (funa, (ty, r))) -> Some (la, (funa, (ty, a :: r)))))
and localteFunTermInSUKLabel _A
  x0 database = match x0, database with SUKLabel a, database -> None
    | SUIdKLabel a, database -> None
    | SUKLabelFun (x, y), database ->
        (match localteFunTermInSUKLabel _A x database
          with None ->
            (match localteFunTermInSUKList _A y database
              with None ->
                (match getSUKLabelMeaning x with None -> None
                  | Some s ->
                    (if isFunctionItem (equal_label _A) s database
                      then Some (s, (y, ([KLabel], SUIdKLabel FunHole)))
                      else None))
              | Some (l, (funa, (ty, r))) ->
                Some (l, (funa, (ty, SUKLabelFun (x, r)))))
          | Some (l, (funa, (ty, r))) ->
            Some (l, (funa, (ty, SUKLabelFun (r, y)))))
and localteFunTermInSUMap _A
  x0 database = match x0, database with [], database -> None
    | a :: l, database ->
        (match a
          with ItemM (x, y) ->
            (match localteFunTermInSUK _A x database
              with None ->
                (match localteFunTermInSUK _A y database
                  with None ->
                    (match localteFunTermInSUMap _A l database with None -> None
                      | Some (la, (funa, (ty, r))) ->
                        Some (la, (funa, (ty, a :: r))))
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, ItemM (x, r) :: l))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, ItemM (r, y) :: l))))
          | IdM _ ->
            (match localteFunTermInSUMap _A l database with None -> None
              | Some (la, (funa, (ty, r))) -> Some (la, (funa, (ty, a :: r))))
          | SUMapKItem (x, y) ->
            (match localteFunTermInSUKLabel _A x database
              with None ->
                (match localteFunTermInSUKList _A y database
                  with None ->
                    (match localteFunTermInSUMap _A l database
                      with None ->
                        (match getSUKLabelMeaning x with None -> None
                          | Some s ->
                            (if isFunctionItem (equal_label _A) s database
                              then Some (s, (y, ([Map], IdM FunHole :: l)))
                              else None))
                      | Some (la, (funa, (ty, r))) ->
                        Some (la, (funa, (ty, a :: r))))
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, SUMapKItem (x, r) :: l))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, SUMapKItem (r, y) :: l)))))
and localteFunTermInSUSet _A
  x0 database = match x0, database with [], database -> None
    | a :: l, database ->
        (match a
          with ItemS x ->
            (match localteFunTermInSUK _A x database
              with None ->
                (match localteFunTermInSUSet _A l database with None -> None
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, a :: r))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, ItemS r :: l))))
          | IdS _ ->
            (match localteFunTermInSUSet _A l database with None -> None
              | Some (la, (funa, (ty, r))) -> Some (la, (funa, (ty, a :: r))))
          | SUSetKItem (x, y) ->
            (match localteFunTermInSUKLabel _A x database
              with None ->
                (match localteFunTermInSUKList _A y database
                  with None ->
                    (match localteFunTermInSUSet _A l database
                      with None ->
                        (match getSUKLabelMeaning x with None -> None
                          | Some s ->
                            (if isFunctionItem (equal_label _A) s database
                              then Some (s, (y, ([Seta], IdS FunHole :: l)))
                              else None))
                      | Some (la, (funa, (ty, r))) ->
                        Some (la, (funa, (ty, a :: r))))
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, SUSetKItem (x, r) :: l))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, SUSetKItem (r, y) :: l)))))
and localteFunTermInSUList _A
  x0 database = match x0, database with [], database -> None
    | a :: l, database ->
        (match a
          with ItemL x ->
            (match localteFunTermInSUK _A x database
              with None ->
                (match localteFunTermInSUList _A l database with None -> None
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, a :: r))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, ItemL r :: l))))
          | IdL _ ->
            (match localteFunTermInSUList _A l database with None -> None
              | Some (la, (funa, (ty, r))) -> Some (la, (funa, (ty, a :: r))))
          | SUListKItem (x, y) ->
            (match localteFunTermInSUKLabel _A x database
              with None ->
                (match localteFunTermInSUKList _A y database
                  with None ->
                    (match localteFunTermInSUList _A l database
                      with None ->
                        (match getSUKLabelMeaning x with None -> None
                          | Some s ->
                            (if isFunctionItem (equal_label _A) s database
                              then Some (s, (y, ([List], IdL FunHole :: l)))
                              else None))
                      | Some (la, (funa, (ty, r))) ->
                        Some (la, (funa, (ty, a :: r))))
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, SUListKItem (x, r) :: l))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, SUListKItem (r, y) :: l)))));;

let rec hasFunLabelInSUKItem _A
  x0 database = match x0, database with
    SUKItem (x, y, z), database ->
      hasFunLabelInSUKLabel _A x database ||
        (hasFunLabelInSUKList _A y database ||
          (match getSUKLabelMeaning x with None -> false
            | Some s ->
              (if isFunctionItem (equal_label _A) s database then true
                else false)))
    | SUIdKItem (x, y), database -> false
    | SUHOLE x, database -> false
and hasFunLabelInSUK _A
  x0 database = match x0, database with [], database -> false
    | a :: l, database ->
        (match a
          with ItemFactor x ->
            hasFunLabelInSUKItem _A x database || hasFunLabelInSUK _A l database
          | IdFactor _ -> hasFunLabelInSUK _A l database
          | SUKKItem (x, y, _) ->
            hasFunLabelInSUKLabel _A x database ||
              (hasFunLabelInSUKList _A y database ||
                (hasFunLabelInSUK _A l database ||
                  (match getSUKLabelMeaning x with None -> false
                    | Some s ->
                      (if isFunctionItem (equal_label _A) s database then true
                        else false)))))
and hasFunLabelInSUBigKWithBag _A
  x0 database = match x0, database with
    SUK a, database -> hasFunLabelInSUK _A a database
    | SUList a, database -> hasFunLabelInSUList _A a database
    | SUSet a, database -> hasFunLabelInSUSet _A a database
    | SUMap a, database -> hasFunLabelInSUMap _A a database
    | SUBag a, database -> hasFunLabelInSUBag _A a database
and hasFunLabelInSUBag _A
  x0 database = match x0, database with [], database -> false
    | a :: l, database ->
        (match a
          with ItemB (_, _, z) ->
            hasFunLabelInSUBigKWithBag _A z database ||
              hasFunLabelInSUBag _A l database
          | IdB _ -> hasFunLabelInSUBag _A l database)
and hasFunLabelInSUBigKWithLabel _A
  x0 database = match x0, database with
    SUBigBag a, database -> hasFunLabelInSUBigKWithBag _A a database
    | SUBigLabel a, database -> hasFunLabelInSUKLabel _A a database
and hasFunLabelInSUKList _A
  x0 database = match x0, database with [], database -> false
    | a :: l, database ->
        (match a
          with ItemKl x ->
            hasFunLabelInSUBigKWithLabel _A x database ||
              hasFunLabelInSUKList _A l database
          | IdKl _ -> hasFunLabelInSUKList _A l database)
and hasFunLabelInSUKLabel _A
  x0 database = match x0, database with SUKLabel a, database -> false
    | SUIdKLabel a, database -> false
    | SUKLabelFun (x, y), database ->
        hasFunLabelInSUKLabel _A x database ||
          (hasFunLabelInSUKList _A y database ||
            (match getSUKLabelMeaning x with None -> false
              | Some s ->
                (if isFunctionItem (equal_label _A) s database then true
                  else false)))
and hasFunLabelInSUMap _A
  x0 database = match x0, database with [], database -> false
    | a :: l, database ->
        (match a
          with ItemM (x, y) ->
            hasFunLabelInSUK _A x database ||
              (hasFunLabelInSUK _A y database ||
                hasFunLabelInSUMap _A l database)
          | IdM _ -> hasFunLabelInSUMap _A l database
          | SUMapKItem (x, y) ->
            hasFunLabelInSUKLabel _A x database ||
              (hasFunLabelInSUKList _A y database ||
                (hasFunLabelInSUMap _A l database ||
                  (match getSUKLabelMeaning x with None -> false
                    | Some s ->
                      (if isFunctionItem (equal_label _A) s database then true
                        else false)))))
and hasFunLabelInSUSet _A
  x0 database = match x0, database with [], database -> false
    | a :: l, database ->
        (match a
          with ItemS x ->
            hasFunLabelInSUK _A x database || hasFunLabelInSUSet _A l database
          | IdS _ -> hasFunLabelInSUSet _A l database
          | SUSetKItem (x, y) ->
            hasFunLabelInSUKLabel _A x database ||
              (hasFunLabelInSUKList _A y database ||
                (hasFunLabelInSUSet _A l database ||
                  (match getSUKLabelMeaning x with None -> false
                    | Some s ->
                      (if isFunctionItem (equal_label _A) s database then true
                        else false)))))
and hasFunLabelInSUList _A
  x0 database = match x0, database with [], database -> false
    | a :: l, database ->
        (match a
          with ItemL x ->
            hasFunLabelInSUK _A x database || hasFunLabelInSUList _A l database
          | IdL _ -> hasFunLabelInSUList _A l database
          | SUListKItem (x, y) ->
            hasFunLabelInSUKLabel _A x database ||
              (hasFunLabelInSUKList _A y database ||
                (hasFunLabelInSUList _A l database ||
                  (match getSUKLabelMeaning x with None -> false
                    | Some s ->
                      (if isFunctionItem (equal_label _A) s database then true
                        else false)))));;

let rec if_pred b = (if b then single () else bot_pred);;

let rec times_num
  m n = match m, n with
    Bit1 m, Bit1 n -> Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)))
    | Bit1 m, Bit0 n -> Bit0 (times_num (Bit1 m) n)
    | Bit0 m, Bit1 n -> Bit0 (times_num m (Bit1 n))
    | Bit0 m, Bit0 n -> Bit0 (Bit0 (times_num m n))
    | One, n -> n
    | m, One -> m;;

let rec times_int k l = match k, l with Neg m, Neg n -> Pos (times_num m n)
                    | Neg m, Pos n -> Neg (times_num m n)
                    | Pos m, Neg n -> Neg (times_num m n)
                    | Pos m, Pos n -> Pos (times_num m n)
                    | Zero_int, l -> Zero_int
                    | k, Zero_int -> Zero_int;;

let rec evalMapUpdate _A _B _C
  x0 a b = match x0, a, b with [], a, b -> [ItemM (a, b)]
    | x :: xl, a, b ->
        (match x
          with ItemM (u, _) ->
            (if equal_lista (equal_suKFactor _A _B _C) u a
              then ItemM (a, b) :: xl else x :: evalMapUpdate _A _B _C xl a b)
          | IdM _ -> x :: xl | SUMapKItem (_, _) -> x :: xl);;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec less_eq_set _A
  a b = match a, b with Coset [], Set [] -> false
    | a, Coset ys -> list_all (fun y -> not (member _A y a)) ys
    | Set xs, b -> list_all (fun x -> member _A x b) xs;;

let rec equal_set _A a b = less_eq_set _A a b && less_eq_set _A b a;;

let rec evalEqualSet _A _B _C
  a b = equal_set (equal_list (equal_suKFactor _A _B _C)) (turnSet _A _B _C a)
          (turnSet _A _B _C b);;

let rec evalEqualMap _A _B _C
  a b = equal_set
          (equal_prod (equal_list (equal_suKFactor _A _B _C))
            (equal_list (equal_suKFactor _A _B _C)))
          (turnMap _A _B _C a) (turnMap _A _B _C b);;

let rec evalBuiltinFun _B _C _D _E
  x0 kl database subG = match x0, kl, database, subG with
    GetKLabel, kl, database, subG ->
      (match kl with [] -> None | ItemKl (SUBigBag (SUK [])) :: _ -> None
        | [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (l, _, _))]))] ->
          Some (KLabelSubs l)
        | ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (_, _, _))])) :: _ :: _ ->
          None
        | ItemKl (SUBigBag (SUK (ItemFactor (SUKItem (_, _, _)) :: _ :: _))) ::
            _
          -> None
        | ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _ ->
          None
        | ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _ -> None
        | ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _ -> None
        | ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _ -> None
        | ItemKl (SUBigBag (SUList _)) :: _ -> None
        | ItemKl (SUBigBag (SUSet _)) :: _ -> None
        | ItemKl (SUBigBag (SUMap _)) :: _ -> None
        | ItemKl (SUBigBag (SUBag _)) :: _ -> None
        | ItemKl (SUBigLabel _) :: _ -> None | IdKl _ :: _ -> None)
    | IsKResult, kl, database, subG ->
        (match kl with [] -> None | ItemKl (SUBigBag (SUK [])) :: _ -> None
          | [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel s, _, _))]))]
            -> (match getSort (equal_label _B) s database with None -> None
                 | Some t ->
                   (if subsortList (equal_sort _E) t [KResult] subG
                     then Some (KItemSubs
                                 (SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool])))
                     else Some (KItemSubs
                                 (SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst false)),
                                     [], [Bool])))))
          | ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel _, _, _))])) ::
              _ :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel _, _, _)) :: _ :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUIdKLabel _, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabelFun (_, _), _, _)) :: _))) ::
              _
            -> None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _ ->
            None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUList _)) :: _ -> None
          | ItemKl (SUBigBag (SUSet _)) :: _ -> None
          | ItemKl (SUBigBag (SUMap _)) :: _ -> None
          | ItemKl (SUBigBag (SUBag _)) :: _ -> None
          | ItemKl (SUBigLabel _) :: _ -> None | IdKl _ :: _ -> None)
    | AndBool, kl, database, subG ->
        (match kl with [] -> None | ItemKl (SUBigBag (SUK [])) :: _ -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (UnitLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (FloatConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (StringConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _, [])) ::
                       _))) ::
              _
            -> None
          | [ItemKl
               (SUBigBag
                 (SUK [ItemFactor
                         (SUKItem
                           (SUKLabel (ConstToLabel (BoolConst _)), _,
                             [Bool]))]))]
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUK [])) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (UnitLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IntConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (FloatConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (StringConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _, [])) ::
                         _))) ::
                _
            -> None
          | [ItemKl
               (SUBigBag
                 (SUK [ItemFactor
                         (SUKItem
                           (SUKLabel (ConstToLabel (BoolConst b1)), _,
                             [Bool]))]));
              ItemKl
                (SUBigBag
                  (SUK [ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst b2)), _,
                              [Bool]))]))]
            -> Some (KItemSubs
                      (SUKItem
                        (SUKLabel (ConstToLabel (BoolConst (b1 && b2))), [],
                          [Bool])))
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK [ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              [Bool]))])) ::
                _ :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              [Bool])) ::
                         _ :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Bool :: _ :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              K :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              KItem :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              KLabel :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              KResult :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              KList :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              List :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Seta :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Map :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Bag :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              OtherSort _ :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Top :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Int :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Float :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Id :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              String :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IdConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel Sort, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel GetKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel IsKResult, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel AndBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel OrBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel SetConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel SetItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel ListConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel ListItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapUpdate, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualK, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotEqualK, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotEqualKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (OtherLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (TokenLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel PlusInt, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MinusInt, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel TimesInt, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualSet, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualMap, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUIdKLabel _, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabelFun (_, _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUList _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUSet _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUMap _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUBag _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigLabel _) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              IdKl _ :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _, [Bool])) ::
                       _ :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Bool :: _ :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _, K :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            KItem :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            KLabel :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            KResult :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            KList :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            List :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Seta :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Map :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Bag :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            OtherSort _ :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Top :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Int :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Float :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Id :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            String :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem (SUKLabel (ConstToLabel (IdConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel Sort, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel GetKLabel, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel IsKResult, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel AndBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel OrBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel SetConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel SetItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel ListConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel ListItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapUpdate, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualK, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotEqualK, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualKLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotEqualKLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (OtherLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (TokenLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel PlusInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MinusInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel TimesInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualSet, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualMap, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUIdKLabel _, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabelFun (_, _), _, _)) :: _))) ::
              _
            -> None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _ ->
            None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUList _)) :: _ -> None
          | ItemKl (SUBigBag (SUSet _)) :: _ -> None
          | ItemKl (SUBigBag (SUMap _)) :: _ -> None
          | ItemKl (SUBigBag (SUBag _)) :: _ -> None
          | ItemKl (SUBigLabel _) :: _ -> None | IdKl _ :: _ -> None)
    | OrBool, kl, database, subG ->
        (match kl with [] -> None | ItemKl (SUBigBag (SUK [])) :: _ -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (UnitLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (FloatConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (StringConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _, [])) ::
                       _))) ::
              _
            -> None
          | [ItemKl
               (SUBigBag
                 (SUK [ItemFactor
                         (SUKItem
                           (SUKLabel (ConstToLabel (BoolConst _)), _,
                             [Bool]))]))]
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUK [])) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (UnitLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IntConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (FloatConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (StringConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _, [])) ::
                         _))) ::
                _
            -> None
          | [ItemKl
               (SUBigBag
                 (SUK [ItemFactor
                         (SUKItem
                           (SUKLabel (ConstToLabel (BoolConst b1)), _,
                             [Bool]))]));
              ItemKl
                (SUBigBag
                  (SUK [ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst b2)), _,
                              [Bool]))]))]
            -> Some (KItemSubs
                      (SUKItem
                        (SUKLabel (ConstToLabel (BoolConst (b1 || b2))), [],
                          [Bool])))
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK [ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              [Bool]))])) ::
                _ :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              [Bool])) ::
                         _ :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Bool :: _ :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              K :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              KItem :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              KLabel :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              KResult :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              KList :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              List :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Seta :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Map :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Bag :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              OtherSort _ :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Top :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Int :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Float :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              Id :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _,
                              String :: _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IdConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel Sort, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel GetKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel IsKResult, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel AndBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel OrBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel SetConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel SetItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel ListConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel ListItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapUpdate, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualK, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotEqualK, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotEqualKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (OtherLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (TokenLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel PlusInt, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MinusInt, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel TimesInt, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualSet, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualMap, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUIdKLabel _, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabelFun (_, _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUList _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUSet _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUMap _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigBag (SUBag _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              ItemKl (SUBigLabel _) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              IdKl _ :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _, [Bool])) ::
                       _ :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Bool :: _ :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _, K :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            KItem :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            KLabel :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            KResult :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            KList :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            List :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Seta :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Map :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Bag :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            OtherSort _ :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Top :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Int :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Float :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Id :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            String :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem (SUKLabel (ConstToLabel (IdConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel Sort, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel GetKLabel, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel IsKResult, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel AndBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel OrBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel SetConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel SetItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel ListConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel ListItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapUpdate, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualK, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotEqualK, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualKLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotEqualKLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (OtherLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (TokenLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel PlusInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MinusInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel TimesInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualSet, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualMap, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUIdKLabel _, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabelFun (_, _), _, _)) :: _))) ::
              _
            -> None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _ ->
            None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUList _)) :: _ -> None
          | ItemKl (SUBigBag (SUSet _)) :: _ -> None
          | ItemKl (SUBigBag (SUMap _)) :: _ -> None
          | ItemKl (SUBigBag (SUBag _)) :: _ -> None
          | ItemKl (SUBigLabel _) :: _ -> None | IdKl _ :: _ -> None)
    | NotBool, kl, database, subG ->
        (match kl with [] -> None | ItemKl (SUBigBag (SUK [])) :: _ -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (UnitLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (FloatConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (StringConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _, [])) ::
                       _))) ::
              _
            -> None
          | [ItemKl
               (SUBigBag
                 (SUK [ItemFactor
                         (SUKItem
                           (SUKLabel (ConstToLabel (BoolConst b1)), _,
                             [Bool]))]))]
            -> Some (KItemSubs
                      (SUKItem
                        (SUKLabel (ConstToLabel (BoolConst (not b1))), [],
                          [Bool])))
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            [Bool]))])) ::
              _ :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _, [Bool])) ::
                       _ :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Bool :: _ :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _, K :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            KItem :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            KLabel :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            KResult :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            KList :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            List :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Seta :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Map :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Bag :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            OtherSort _ :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Top :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Int :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Float :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            Id :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _,
                            String :: _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem (SUKLabel (ConstToLabel (IdConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel Sort, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel GetKLabel, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel IsKResult, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel AndBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel OrBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel SetConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel SetItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel ListConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel ListItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapUpdate, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualK, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotEqualK, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualKLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotEqualKLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (OtherLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (TokenLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel PlusInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MinusInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel TimesInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualSet, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualMap, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUIdKLabel _, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabelFun (_, _), _, _)) :: _))) ::
              _
            -> None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _ ->
            None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUList _)) :: _ -> None
          | ItemKl (SUBigBag (SUSet _)) :: _ -> None
          | ItemKl (SUBigBag (SUMap _)) :: _ -> None
          | ItemKl (SUBigBag (SUBag _)) :: _ -> None
          | ItemKl (SUBigLabel _) :: _ -> None | IdKl _ :: _ -> None)
    | MapUpdate, kl, database, subG ->
        (match kl with [] -> None | ItemKl (SUBigBag (SUK _)) :: _ -> None
          | ItemKl (SUBigBag (SUList _)) :: _ -> None
          | ItemKl (SUBigBag (SUSet _)) :: _ -> None
          | [ItemKl (SUBigBag (SUMap _))] -> None
          | [ItemKl (SUBigBag (SUMap _)); ItemKl (SUBigBag (SUK _))] -> None
          | [ItemKl (SUBigBag (SUMap ml)); ItemKl (SUBigBag (SUK key));
              ItemKl (SUBigBag (SUK v))]
            -> Some (MapSubs (evalMapUpdate _B _C _D ml key v))
          | ItemKl (SUBigBag (SUMap _)) ::
              ItemKl (SUBigBag (SUK _)) :: ItemKl (SUBigBag (SUK _)) :: _ :: _
            -> None
          | ItemKl (SUBigBag (SUMap _)) ::
              ItemKl (SUBigBag (SUK _)) :: ItemKl (SUBigBag (SUList _)) :: _
            -> None
          | ItemKl (SUBigBag (SUMap _)) ::
              ItemKl (SUBigBag (SUK _)) :: ItemKl (SUBigBag (SUSet _)) :: _
            -> None
          | ItemKl (SUBigBag (SUMap _)) ::
              ItemKl (SUBigBag (SUK _)) :: ItemKl (SUBigBag (SUMap _)) :: _
            -> None
          | ItemKl (SUBigBag (SUMap _)) ::
              ItemKl (SUBigBag (SUK _)) :: ItemKl (SUBigBag (SUBag _)) :: _
            -> None
          | ItemKl (SUBigBag (SUMap _)) ::
              ItemKl (SUBigBag (SUK _)) :: ItemKl (SUBigLabel _) :: _
            -> None
          | ItemKl (SUBigBag (SUMap _)) ::
              ItemKl (SUBigBag (SUK _)) :: IdKl _ :: _
            -> None
          | ItemKl (SUBigBag (SUMap _)) :: ItemKl (SUBigBag (SUList _)) :: _ ->
            None
          | ItemKl (SUBigBag (SUMap _)) :: ItemKl (SUBigBag (SUSet _)) :: _ ->
            None
          | ItemKl (SUBigBag (SUMap _)) :: ItemKl (SUBigBag (SUMap _)) :: _ ->
            None
          | ItemKl (SUBigBag (SUMap _)) :: ItemKl (SUBigBag (SUBag _)) :: _ ->
            None
          | ItemKl (SUBigBag (SUMap _)) :: ItemKl (SUBigLabel _) :: _ -> None
          | ItemKl (SUBigBag (SUMap _)) :: IdKl _ :: _ -> None
          | ItemKl (SUBigBag (SUBag _)) :: _ -> None
          | ItemKl (SUBigLabel _) :: _ -> None | IdKl _ :: _ -> None)
    | EqualSet, kl, database, subG ->
        (match kl with [] -> None
          | ItemKl a :: lista ->
            (match a
              with SUBigBag aa ->
                (match aa with SUK _ -> None | SUList _ -> None
                  | SUSet ab ->
                    (match lista with [] -> None
                      | ItemKl b :: listaa ->
                        (match b
                          with SUBigBag ba ->
                            (match ba with SUK _ -> None | SUList _ -> None
                              | SUSet bb ->
                                (match listaa
                                  with [] ->
                                    Some (KItemSubs
   (SUKItem
     (SUKLabel (ConstToLabel (BoolConst (evalEqualSet _B _C _D ab bb))), [],
       [Bool])))
                                  | _ :: _ -> None)
                              | SUMap _ -> None | SUBag _ -> None)
                          | SUBigLabel _ -> None)
                      | IdKl _ :: _ -> None)
                  | SUMap _ -> None | SUBag _ -> None)
              | SUBigLabel _ -> None)
          | IdKl _ :: _ -> None)
    | EqualMap, kl, database, subG ->
        (match kl with [] -> None
          | ItemKl a :: lista ->
            (match a
              with SUBigBag aa ->
                (match aa with SUK _ -> None | SUList _ -> None
                  | SUSet _ -> None
                  | SUMap ab ->
                    (match lista with [] -> None
                      | ItemKl b :: listaa ->
                        (match b
                          with SUBigBag ba ->
                            (match ba with SUK _ -> None | SUList _ -> None
                              | SUSet _ -> None
                              | SUMap bb ->
                                (match listaa
                                  with [] ->
                                    Some (KItemSubs
   (SUKItem
     (SUKLabel (ConstToLabel (BoolConst (evalEqualMap _B _C _D ab bb))), [],
       [Bool])))
                                  | _ :: _ -> None)
                              | SUBag _ -> None)
                          | SUBigLabel _ -> None)
                      | IdKl _ :: _ -> None)
                  | SUBag _ -> None)
              | SUBigLabel _ -> None)
          | IdKl _ :: _ -> None)
    | EqualK, kl, database, subG ->
        (match kl with [] -> None
          | ItemKl a :: lista ->
            (match a
              with SUBigBag aa ->
                (match aa
                  with SUK ab ->
                    (match lista with [] -> None
                      | ItemKl b :: listaa ->
                        (match b
                          with SUBigBag ba ->
                            (match ba
                              with SUK bb ->
                                (match listaa
                                  with [] ->
                                    Some (KItemSubs
   (SUKItem
     (SUKLabel
        (ConstToLabel
          (BoolConst (equal_lista (equal_suKFactor _B _C _D) ab bb))),
       [], [Bool])))
                                  | _ :: _ -> None)
                              | SUList _ -> None | SUSet _ -> None
                              | SUMap _ -> None | SUBag _ -> None)
                          | SUBigLabel _ -> None)
                      | IdKl _ :: _ -> None)
                  | SUList _ -> None | SUSet _ -> None | SUMap _ -> None
                  | SUBag _ -> None)
              | SUBigLabel _ -> None)
          | IdKl _ :: _ -> None)
    | NotEqualK, kl, database, subG ->
        (match kl with [] -> None
          | ItemKl a :: lista ->
            (match a
              with SUBigBag aa ->
                (match aa
                  with SUK ab ->
                    (match lista with [] -> None
                      | ItemKl b :: listaa ->
                        (match b
                          with SUBigBag ba ->
                            (match ba
                              with SUK bb ->
                                (match listaa
                                  with [] ->
                                    Some (KItemSubs
   (SUKItem
     (SUKLabel
        (ConstToLabel
          (BoolConst (not (equal_lista (equal_suKFactor _B _C _D) ab bb)))),
       [], [Bool])))
                                  | _ :: _ -> None)
                              | SUList _ -> None | SUSet _ -> None
                              | SUMap _ -> None | SUBag _ -> None)
                          | SUBigLabel _ -> None)
                      | IdKl _ :: _ -> None)
                  | SUList _ -> None | SUSet _ -> None | SUMap _ -> None
                  | SUBag _ -> None)
              | SUBigLabel _ -> None)
          | IdKl _ :: _ -> None)
    | EqualKLabel, kl, database, subG ->
        (match kl with [] -> None
          | ItemKl a :: lista ->
            (match a with SUBigBag _ -> None
              | SUBigLabel aa ->
                (match aa
                  with SUKLabel ab ->
                    (match lista with [] -> None
                      | ItemKl b :: listaa ->
                        (match b with SUBigBag _ -> None
                          | SUBigLabel ba ->
                            (match ba
                              with SUKLabel bb ->
                                (match listaa
                                  with [] ->
                                    Some (KItemSubs
   (SUKItem
     (SUKLabel (ConstToLabel (BoolConst (equal_labela _B ab bb))), [], [Bool])))
                                  | _ :: _ -> None)
                              | SUIdKLabel _ -> None
                              | SUKLabelFun (_, _) -> None))
                      | IdKl _ :: _ -> None)
                  | SUIdKLabel _ -> None | SUKLabelFun (_, _) -> None))
          | IdKl _ :: _ -> None)
    | NotEqualKLabel, kl, database, subG ->
        (match kl with [] -> None
          | ItemKl a :: lista ->
            (match a with SUBigBag _ -> None
              | SUBigLabel aa ->
                (match aa
                  with SUKLabel ab ->
                    (match lista with [] -> None
                      | ItemKl b :: listaa ->
                        (match b with SUBigBag _ -> None
                          | SUBigLabel ba ->
                            (match ba
                              with SUKLabel bb ->
                                (match listaa
                                  with [] ->
                                    Some (KItemSubs
   (SUKItem
     (SUKLabel (ConstToLabel (BoolConst (not (equal_labela _B ab bb)))), [],
       [Bool])))
                                  | _ :: _ -> None)
                              | SUIdKLabel _ -> None
                              | SUKLabelFun (_, _) -> None))
                      | IdKl _ :: _ -> None)
                  | SUIdKLabel _ -> None | SUKLabelFun (_, _) -> None))
          | IdKl _ :: _ -> None)
    | PlusInt, kl, database, subG ->
        (match kl with [] -> None | ItemKl (SUBigBag (SUK [])) :: _ -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (UnitLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | [ItemKl
               (SUBigBag
                 (SUK [ItemFactor
                         (SUKItem
                           (SUKLabel (ConstToLabel (IntConst _)), _, _))]))]
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK [])) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (UnitLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | [ItemKl
               (SUBigBag
                 (SUK [ItemFactor
                         (SUKItem
                           (SUKLabel (ConstToLabel (IntConst b1)), _, _))]));
              ItemKl
                (SUBigBag
                  (SUK [ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IntConst b2)), _, _))]))]
            -> Some (KItemSubs
                      (SUKItem
                        (SUKLabel (ConstToLabel (IntConst (plus_int b1 b2))),
                          [], [Int])))
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK [ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
                _ :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IntConst _)), _, _)) ::
                         _ :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (FloatConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (StringConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IdConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel Sort, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel GetKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel IsKResult, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel AndBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel OrBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel SetConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel SetItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel ListConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel ListItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapUpdate, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualK, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotEqualK, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotEqualKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (OtherLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (TokenLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel PlusInt, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MinusInt, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel TimesInt, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualSet, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualMap, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUIdKLabel _, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabelFun (_, _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUList _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUSet _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUMap _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUBag _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigLabel _) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              IdKl _ :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _)) ::
                       _ :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (FloatConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (StringConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem (SUKLabel (ConstToLabel (IdConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel Sort, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel GetKLabel, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel IsKResult, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel AndBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel OrBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel SetConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel SetItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel ListConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel ListItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapUpdate, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualK, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotEqualK, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualKLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotEqualKLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (OtherLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (TokenLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel PlusInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MinusInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel TimesInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualSet, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualMap, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUIdKLabel _, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabelFun (_, _), _, _)) :: _))) ::
              _
            -> None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _ ->
            None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUList _)) :: _ -> None
          | ItemKl (SUBigBag (SUSet _)) :: _ -> None
          | ItemKl (SUBigBag (SUMap _)) :: _ -> None
          | ItemKl (SUBigBag (SUBag _)) :: _ -> None
          | ItemKl (SUBigLabel _) :: _ -> None | IdKl _ :: _ -> None)
    | MinusInt, kl, database, subG ->
        (match kl with [] -> None | ItemKl (SUBigBag (SUK [])) :: _ -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (UnitLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | [ItemKl
               (SUBigBag
                 (SUK [ItemFactor
                         (SUKItem
                           (SUKLabel (ConstToLabel (IntConst _)), _, _))]))]
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK [])) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (UnitLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | [ItemKl
               (SUBigBag
                 (SUK [ItemFactor
                         (SUKItem
                           (SUKLabel (ConstToLabel (IntConst b1)), _, _))]));
              ItemKl
                (SUBigBag
                  (SUK [ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IntConst b2)), _, _))]))]
            -> Some (KItemSubs
                      (SUKItem
                        (SUKLabel (ConstToLabel (IntConst (minus_int b1 b2))),
                          [], [Int])))
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK [ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
                _ :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IntConst _)), _, _)) ::
                         _ :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (FloatConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (StringConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IdConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel Sort, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel GetKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel IsKResult, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel AndBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel OrBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel SetConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel SetItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel ListConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel ListItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapUpdate, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualK, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotEqualK, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotEqualKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (OtherLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (TokenLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel PlusInt, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MinusInt, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel TimesInt, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualSet, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualMap, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUIdKLabel _, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabelFun (_, _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUList _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUSet _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUMap _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUBag _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigLabel _) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              IdKl _ :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _)) ::
                       _ :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (FloatConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (StringConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem (SUKLabel (ConstToLabel (IdConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel Sort, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel GetKLabel, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel IsKResult, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel AndBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel OrBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel SetConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel SetItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel ListConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel ListItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapUpdate, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualK, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotEqualK, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualKLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotEqualKLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (OtherLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (TokenLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel PlusInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MinusInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel TimesInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualSet, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualMap, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUIdKLabel _, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabelFun (_, _), _, _)) :: _))) ::
              _
            -> None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _ ->
            None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUList _)) :: _ -> None
          | ItemKl (SUBigBag (SUSet _)) :: _ -> None
          | ItemKl (SUBigBag (SUMap _)) :: _ -> None
          | ItemKl (SUBigBag (SUBag _)) :: _ -> None
          | ItemKl (SUBigLabel _) :: _ -> None | IdKl _ :: _ -> None)
    | TimesInt, kl, database, subG ->
        (match kl with [] -> None | ItemKl (SUBigBag (SUK [])) :: _ -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (UnitLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | [ItemKl
               (SUBigBag
                 (SUK [ItemFactor
                         (SUKItem
                           (SUKLabel (ConstToLabel (IntConst _)), _, _))]))]
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK [])) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (UnitLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | [ItemKl
               (SUBigBag
                 (SUK [ItemFactor
                         (SUKItem
                           (SUKLabel (ConstToLabel (IntConst b1)), _, _))]));
              ItemKl
                (SUBigBag
                  (SUK [ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IntConst b2)), _, _))]))]
            -> Some (KItemSubs
                      (SUKItem
                        (SUKLabel (ConstToLabel (IntConst (times_int b1 b2))),
                          [], [Int])))
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK [ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
                _ :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IntConst _)), _, _)) ::
                         _ :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (FloatConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (StringConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (BoolConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor
                          (SUKItem
                            (SUKLabel (ConstToLabel (IdConst _)), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel Sort, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel GetKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel IsKResult, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel AndBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel OrBool, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel SetConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel SetItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel ListConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel ListItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapConLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapItemLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MapUpdate, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualK, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotEqualK, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel NotEqualKLabel, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (OtherLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel (TokenLabel _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel PlusInt, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel MinusInt, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel TimesInt, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualSet, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabel EqualMap, _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUIdKLabel _, _, _)) :: _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl
                (SUBigBag
                  (SUK (ItemFactor (SUKItem (SUKLabelFun (_, _), _, _)) ::
                         _))) ::
                _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUList _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUSet _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUMap _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigBag (SUBag _)) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              ItemKl (SUBigLabel _) :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK [ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _))])) ::
              IdKl _ :: _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (IntConst _)), _, _)) ::
                       _ :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (FloatConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (StringConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem
                          (SUKLabel (ConstToLabel (BoolConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor
                        (SUKItem (SUKLabel (ConstToLabel (IdConst _)), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel Sort, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel GetKLabel, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel IsKResult, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel AndBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel OrBool, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel SetConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel SetItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel ListConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel ListItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapConLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapItemLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MapUpdate, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualK, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotEqualK, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualKLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel NotEqualKLabel, _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (OtherLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel (TokenLabel _), _, _)) ::
                       _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel PlusInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel MinusInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel TimesInt, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualSet, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabel EqualMap, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUIdKLabel _, _, _)) :: _))) ::
              _
            -> None
          | ItemKl
              (SUBigBag
                (SUK (ItemFactor (SUKItem (SUKLabelFun (_, _), _, _)) :: _))) ::
              _
            -> None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _))) :: _ ->
            None
          | ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (IdFactor _ :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) :: _ -> None
          | ItemKl (SUBigBag (SUList _)) :: _ -> None
          | ItemKl (SUBigBag (SUSet _)) :: _ -> None
          | ItemKl (SUBigBag (SUMap _)) :: _ -> None
          | ItemKl (SUBigBag (SUBag _)) :: _ -> None
          | ItemKl (SUBigLabel _) :: _ -> None | IdKl _ :: _ -> None)
    | UnitLabel v, kl, database, subG -> None
    | ConstToLabel v, kl, database, subG -> None
    | Sort, kl, database, subG -> None
    | SetConLabel, kl, database, subG -> None
    | SetItemLabel, kl, database, subG -> None
    | ListConLabel, kl, database, subG -> None
    | ListItemLabel, kl, database, subG -> None
    | MapConLabel, kl, database, subG -> None
    | MapItemLabel, kl, database, subG -> None
    | OtherLabel v, kl, database, subG -> None
    | TokenLabel v, kl, database, subG -> None;;

let builtinLabels : 'a label list
  = [GetKLabel; IsKResult; AndBool; NotBool; OrBool; Sort; MapUpdate; EqualK;
      NotEqualK; EqualSet; EqualMap; EqualKLabel; NotEqualKLabel; PlusInt;
      MinusInt; TimesInt];;

let rec funEvaluationBool_i_i_i_i_o _A _B _C
  x xa xb xc =
    sup_pred
      (bind (single (x, (xa, (xb, xc))))
        (fun a ->
          (match a
            with (_, (database, (_, Continue c))) ->
              bind (if_pred (not (hasFunLabelInSUKItem _A c database)))
                (fun () -> single (Stop c))
            | (_, (_, (_, Stop _))) -> bot_pred
            | (_, (_, (_, Div _))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, xc))))
          (fun a ->
            (match a
              with (allRules, (database, (subG, Continue c))) ->
                bind (if_pred (hasFunLabelInSUKItem _A c database))
                  (fun () ->
                    bind (eq_i_o (localteFunTermInSUKItem _A c database))
                      (fun aa ->
                        (match aa with None -> bot_pred
                          | Some (l, (funa, (_, cr))) ->
                            bind (if_pred
                                   (membera (equal_label _A) builtinLabels l))
                              (fun () ->
                                bind (eq_i_o
                                       (evalBuiltinFun _A _B _C _A l funa
 database subG))
                                  (fun ab ->
                                    (match ab with None -> bot_pred
                                      | Some r ->
bind (eq_i_o (substitutionInSUKItem _C cr [(FunHole, r)]))
  (fun ac ->
    (match ac with None -> bot_pred
      | Some ca ->
        bind (funEvaluationBool_i_i_i_i_o _A _B _C allRules database subG
               (Continue ca))
          (fun ad ->
            (match ad with Continue _ -> bot_pred | Stop cb -> single (Stop cb)
              | Div _ -> bot_pred))))))))))
              | (_, (_, (_, Stop _))) -> bot_pred
              | (_, (_, (_, Div _))) -> bot_pred)))
        (bind (single (x, (xa, (xb, xc))))
          (fun a ->
            (match a
              with (allRules, (database, (subG, Continue c))) ->
                bind (if_pred (hasFunLabelInSUKItem _A c database))
                  (fun () ->
                    bind (eq_i_o (localteFunTermInSUKItem _A c database))
                      (fun aa ->
                        (match aa with None -> bot_pred
                          | Some (l, (funa, (_, cr))) ->
                            bind (if_pred
                                   (not (membera (equal_label _A) builtinLabels
  l)))
                              (fun () ->
                                bind (eq_i_o (getFunRule _A l allRules))
                                  (fun ab ->
                                    (match ab with None -> bot_pred
                                      | Some fl ->
bind (funEvaluationBoolAux_i_i_i_i_i_i_o _A _B _C allRules database subG fl funa
       (Continue cr))
  (fun ac ->
    (match ac with Continue _ -> bot_pred
      | Stop ca ->
        bind (funEvaluationBool_i_i_i_i_o _A _B _C allRules database subG
               (Continue ca))
          (fun ad ->
            (match ad with Continue _ -> bot_pred | Stop cb -> single (Stop cb)
              | Div _ -> bot_pred))
      | Div _ -> bot_pred))))))))
              | (_, (_, (_, Stop _))) -> bot_pred
              | (_, (_, (_, Div _))) -> bot_pred))))
and funEvaluationBoolAux_i_i_i_i_i_i_o _A _B _C
  x xa xb xc xd xe =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
        (fun a ->
          (match a with (_, (_, (_, ([], (_, Continue cr))))) -> single (Div cr)
            | (_, (_, (_, ([], (_, Stop _))))) -> bot_pred
            | (_, (_, (_, ([], (_, Div _))))) -> bot_pred
            | (_, (_, (_, (_ :: _, _)))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
          (fun a ->
            (match a with (_, (_, (_, ([], _)))) -> bot_pred
              | (allRules,
                  (database, (subG, ((p, (_, _)) :: fl, (funa, Continue cr)))))
                -> bind (eq_i_i
                          (equal_option
                            (equal_list
                              (equal_prod (equal_metaVar _C)
                                (equal_subsFactor _A _B _C))))
                          (patternMacroingInSUKList _A _B _C _C p funa [] subG)
                          None)
                     (fun () ->
                       bind (funEvaluationBoolAux_i_i_i_i_i_i_o _A _B _C
                              allRules database subG fl funa (Continue cr))
                         (fun aa ->
                           (match aa with Continue _ -> bot_pred
                             | Stop c -> single (Stop c) | Div _ -> bot_pred)))
              | (_, (_, (_, ((_, (_, _)) :: _, (_, Stop _))))) -> bot_pred
              | (_, (_, (_, ((_, (_, _)) :: _, (_, Div _))))) -> bot_pred)))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allRules,
                    (database,
                      (subG, ((p, (_, c)) :: fl, (funa, Continue cr)))))
                  -> bind (funEvaluationBoolAux_i_i_i_i_i_i_o _A _B _C allRules
                            database subG fl funa (Continue cr))
                       (fun aa ->
                         (match aa with Continue _ -> bot_pred
                           | Stop ca ->
                             bind (eq_i_o
                                    (patternMacroingInSUKList _A _B _C _C p funa
                                      [] subG))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some acc ->
                                     bind (eq_i_o
    (substitutionInSUKItem _C c acc))
                                       (fun ac ->
 (match ac with None -> bot_pred
   | Some value ->
     bind (funEvaluationBool_i_i_i_i_o _A _B _C allRules database subG
            (Continue value))
       (fun ad ->
         (match ad with Continue _ -> bot_pred
           | Stop valuea ->
             bind (eq_i_i (equal_option (equal_label _A))
                    (getKLabelInSUKItem valuea)
                    (Some (ConstToLabel (BoolConst false))))
               (fun () -> single (Stop ca))
           | Div _ -> bot_pred))))))
                           | Div _ -> bot_pred))
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Stop _))))) -> bot_pred
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Div _))))) -> bot_pred)))
          (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allRules,
                    (database, (subG, ((p, (r, c)) :: _, (funa, Continue cr)))))
                  -> bind (eq_i_o
                            (patternMacroingInSUKList _A _B _C _C p funa []
                              subG))
                       (fun aa ->
                         (match aa with None -> bot_pred
                           | Some acc ->
                             bind (eq_i_o (substitutionInSUKItem _C c acc))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some value ->
                                     bind (funEvaluationBool_i_i_i_i_o _A _B _C
    allRules database subG (Continue value))
                                       (fun ac ->
 (match ac with Continue _ -> bot_pred
   | Stop valuea ->
     bind (eq_i_i (equal_option (equal_label _A)) (getKLabelInSUKItem valuea)
            (Some (ConstToLabel (BoolConst true))))
       (fun () ->
         bind (eq_i_o (substitutionInSubsFactor _C r acc))
           (fun ad ->
             (match ad with None -> bot_pred
               | Some ra ->
                 bind (eq_i_o (substitutionInSUKItem _C cr [(FunHole, ra)]))
                   (fun ae ->
                     (match ae with None -> bot_pred
                       | Some ca ->
                         bind (eq_i_o
                                (typeCheckCondition _A _B _C ca database subG))
                           (fun af ->
                             (match af with None -> bot_pred
                               | Some cb -> single (Stop cb))))))))
   | Div _ -> bot_pred))))))
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Stop _))))) -> bot_pred
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Div _))))) ->
                  bot_pred)))));;

let rec boolEvalFun _A _B _C
  allRules database subG c =
    the (equal_state (equal_suKItem _A _B _C))
      (funEvaluationBool_i_i_i_i_o _A _B _C allRules database subG
        (Continue c));;

let rec collectSort _A _C
  x0 acc = match x0, acc with
    SimId (a, b), acc ->
      (if equal_sorta _A b Top then Some acc
        else (if existKey (equal_metaVar _C) a acc
               then (match lookup (equal_metaVar _C) a acc with None -> None
                      | Some ba ->
                        (if equal_sorta _A b ba then Some acc else None))
               else Some (update (equal_metaVar _C) a b acc)))
    | SimTerm (a, bl), acc -> collectSorts _A _C bl acc
    | SimLabel a, acc -> Some acc
    | SimEmpty a, acc -> Some acc
    | SimBagCon (a, b), acc ->
        (match collectSort _A _C a acc with None -> None
          | Some _ -> collectSort _A _C b acc)
    | SimBag (x, y, b), acc -> collectSort _A _C b acc
and collectSorts _A _C
  x0 acc = match x0, acc with [], acc -> Some acc
    | x :: xl, acc ->
        (match collectSort _A _C x acc with None -> None
          | Some a -> collectSorts _A _C xl a);;

let rec flattenListAux = function [] -> []
                         | x :: xl -> ListPatNoVar [x] :: flattenListAux xl;;

let rec flattenList
  = function [] -> Some []
    | x :: xl ->
        (match flattenList xl with None -> None
          | Some xla ->
            (match x with IRBigBag (IRK _) -> None
              | IRBigBag (IRList (ListPatNoVar sl)) ->
                Some (flattenListAux sl @ xla)
              | IRBigBag (IRList (ListPat (sl1, v, sl2))) ->
                Some (flattenListAux sl1 @
                       [ListPat ([], v, [])] @ flattenListAux sl2 @ xla)
              | IRBigBag (IRSet _) -> None | IRBigBag (IRMap _) -> None
              | IRBigBag (IRBag _) -> None | IRBigLabel _ -> None));;

let rec irToSUInMatchFactor _A
  = function KLabelMatching a -> KLabelSubs (irToSUInKLabel a)
    | KItemMatching a -> KItemSubs (irToSUInKItem _A a)
    | KMatching a -> KSubs (irToSUInK _A a)
    | KListMatching a -> KListSubs (irToSUInKList _A a)
    | ListMatching a -> ListSubs (irToSUInList _A a)
    | SetMatching a -> SetSubs (irToSUInSet _A a)
    | MapMatching a -> MapSubs (irToSUInMap _A a)
    | BagMatching a -> BagSubs (irToSUInBag _A a);;

let rec irToSUInPat _A
  x0 database = match x0, database with
    KLabelFunPat (s, l), database ->
      KLabelSubs (SUKLabelFun (SUKLabel s, irToSUInKList _A l))
    | KItemFunPat (s, l), database ->
        (match getSort (equal_label _A) s database
          with None ->
            KItemSubs (SUKItem (SUKLabel s, irToSUInKList _A l, [KItem]))
          | Some ty -> KItemSubs (SUKItem (SUKLabel s, irToSUInKList _A l, ty)))
    | KFunPat (s, l), database ->
        KSubs [SUKKItem (SUKLabel s, irToSUInKList _A l, [K])]
    | ListFunPat (s, l), database ->
        ListSubs [SUListKItem (SUKLabel s, irToSUInKList _A l)]
    | SetFunPat (s, l), database ->
        SetSubs [SUSetKItem (SUKLabel s, irToSUInKList _A l)]
    | MapFunPat (s, l), database ->
        MapSubs [SUMapKItem (SUKLabel s, irToSUInKList _A l)]
    | NormalPat a, database -> irToSUInMatchFactor _A a;;

let rec restructMap
  = function [] -> Some (MapPat ([], None))
    | x :: xl ->
        (match restructMap xl with None -> None
          | Some (MapPat (sl, None)) ->
            (match x with MapPat (sla, None) -> Some (MapPat (sla @ sl, None))
              | MapPat (sla, Some v) -> Some (MapPat (sla @ sl, Some v)))
          | Some (MapPat (sl, Some v)) ->
            (match x with MapPat (sla, None) -> Some (MapPat (sla @ sl, Some v))
              | MapPat (_, Some _) -> None));;

let rec restructSet
  = function [] -> Some (SetPat ([], None))
    | x :: xl ->
        (match restructSet xl with None -> None
          | Some (SetPat (sl, None)) ->
            (match x with SetPat (sla, None) -> Some (SetPat (sla @ sl, None))
              | SetPat (sla, Some v) -> Some (SetPat (sla @ sl, Some v)))
          | Some (SetPat (sl, Some v)) ->
            (match x with SetPat (sla, None) -> Some (SetPat (sla @ sl, Some v))
              | SetPat (_, Some _) -> None));;

let rec restructList
  = function [] -> Some (ListPatNoVar [])
    | x :: xl ->
        (match restructList xl with None -> None
          | Some (ListPatNoVar sl) ->
            (match x with ListPatNoVar sla -> Some (ListPatNoVar (sla @ sl))
              | ListPat (sl1, v, sl2) -> Some (ListPat (sl1, v, sl2 @ sl)))
          | Some (ListPat (sl1, v, sl2)) ->
            (match x with ListPatNoVar sl -> Some (ListPat (sl @ sl1, v, sl2))
              | ListPat (_, _, _) -> None));;

let rec simpleKToIR _A
  x0 database = match x0, database with
    SimId (x, y), database ->
      (match y
        with Bool -> Some (NormalPat (KItemMatching (IRIdKItem (x, [y]))))
        | K -> Some (NormalPat (KMatching (KPat ([], Some x))))
        | KItem -> Some (NormalPat (KItemMatching (IRIdKItem (x, [y]))))
        | KLabel -> Some (NormalPat (KLabelMatching (IRIdKLabel x)))
        | KResult -> Some (NormalPat (KItemMatching (IRIdKItem (x, [y]))))
        | KList -> Some (NormalPat (KListMatching (KListPat ([], x, []))))
        | List -> Some (NormalPat (ListMatching (ListPat ([], x, []))))
        | Seta -> Some (NormalPat (SetMatching (SetPat ([], Some x))))
        | Map -> Some (NormalPat (MapMatching (MapPat ([], Some x))))
        | Bag -> Some (NormalPat (BagMatching (BagPat ([], Some x))))
        | OtherSort _ -> Some (NormalPat (KItemMatching (IRIdKItem (x, [y]))))
        | Top -> Some (NormalPat (KItemMatching (IRIdKItem (x, [y]))))
        | Int -> Some (NormalPat (KItemMatching (IRIdKItem (x, [y]))))
        | Float -> Some (NormalPat (KItemMatching (IRIdKItem (x, [y]))))
        | Id -> Some (NormalPat (KItemMatching (IRIdKItem (x, [y]))))
        | String -> Some (NormalPat (KItemMatching (IRIdKItem (x, [y])))))
    | SimEmpty y, database ->
        (match y
          with Bool ->
            Some (NormalPat
                   (KItemMatching
                     (IRKItem (IRKLabel (UnitLabel y), KListPatNoVar [], [y]))))
          | K -> Some (NormalPat (KMatching (KPat ([], None))))
          | KItem ->
            Some (NormalPat
                   (KItemMatching
                     (IRKItem (IRKLabel (UnitLabel y), KListPatNoVar [], [y]))))
          | KLabel ->
            Some (NormalPat
                   (KItemMatching
                     (IRKItem (IRKLabel (UnitLabel y), KListPatNoVar [], [y]))))
          | KResult ->
            Some (NormalPat
                   (KItemMatching
                     (IRKItem (IRKLabel (UnitLabel y), KListPatNoVar [], [y]))))
          | KList -> Some (NormalPat (KListMatching (KListPatNoVar [])))
          | List -> Some (NormalPat (ListMatching (ListPatNoVar [])))
          | Seta -> Some (NormalPat (SetMatching (SetPat ([], None))))
          | Map -> Some (NormalPat (MapMatching (MapPat ([], None))))
          | Bag -> Some (NormalPat (BagMatching (BagPat ([], None))))
          | OtherSort _ ->
            Some (NormalPat
                   (KItemMatching
                     (IRKItem (IRKLabel (UnitLabel y), KListPatNoVar [], [y]))))
          | Top ->
            Some (NormalPat
                   (KItemMatching
                     (IRKItem (IRKLabel (UnitLabel y), KListPatNoVar [], [y]))))
          | Int ->
            Some (NormalPat
                   (KItemMatching
                     (IRKItem (IRKLabel (UnitLabel y), KListPatNoVar [], [y]))))
          | Float ->
            Some (NormalPat
                   (KItemMatching
                     (IRKItem (IRKLabel (UnitLabel y), KListPatNoVar [], [y]))))
          | Id ->
            Some (NormalPat
                   (KItemMatching
                     (IRKItem (IRKLabel (UnitLabel y), KListPatNoVar [], [y]))))
          | String ->
            Some (NormalPat
                   (KItemMatching
                     (IRKItem
                       (IRKLabel (UnitLabel y), KListPatNoVar [], [y])))))
    | SimLabel l, database -> Some (NormalPat (KLabelMatching (IRKLabel l)))
    | SimBag (x, y, b), database ->
        (match simpleKToIR _A b database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching s)) ->
            Some (NormalPat
                   (BagMatching
                     (BagPat ([(x, (y, IRK (KPat ([s], None))))], None))))
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching s)) ->
            Some (NormalPat (BagMatching (BagPat ([(x, (y, IRK s))], None))))
          | Some (NormalPat (ListMatching s)) ->
            Some (NormalPat (BagMatching (BagPat ([(x, (y, IRList s))], None))))
          | Some (NormalPat (SetMatching s)) ->
            Some (NormalPat (BagMatching (BagPat ([(x, (y, IRSet s))], None))))
          | Some (NormalPat (MapMatching s)) ->
            Some (NormalPat (BagMatching (BagPat ([(x, (y, IRMap s))], None))))
          | Some (NormalPat (BagMatching s)) ->
            Some (NormalPat (BagMatching (BagPat ([(x, (y, IRBag s))], None)))))
    | SimBagCon (l, r), database ->
        (match simpleKToIR _A l database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching _)) -> None
          | Some (NormalPat (ListMatching _)) -> None
          | Some (NormalPat (SetMatching _)) -> None
          | Some (NormalPat (MapMatching _)) -> None
          | Some (NormalPat (BagMatching (BagPat (sl, v)))) ->
            (match simpleKToIR _A r database with None -> None
              | Some (KLabelFunPat (_, _)) -> None
              | Some (KFunPat (_, _)) -> None
              | Some (KItemFunPat (_, _)) -> None
              | Some (ListFunPat (_, _)) -> None
              | Some (SetFunPat (_, _)) -> None
              | Some (MapFunPat (_, _)) -> None
              | Some (NormalPat (KLabelMatching _)) -> None
              | Some (NormalPat (KItemMatching _)) -> None
              | Some (NormalPat (KListMatching _)) -> None
              | Some (NormalPat (KMatching _)) -> None
              | Some (NormalPat (ListMatching _)) -> None
              | Some (NormalPat (SetMatching _)) -> None
              | Some (NormalPat (MapMatching _)) -> None
              | Some (NormalPat (BagMatching (BagPat (sla, va)))) ->
                (match v
                  with None ->
                    Some (NormalPat (BagMatching (BagPat (sl @ sla, va))))
                  | Some _ ->
                    (match va
                      with None ->
                        Some (NormalPat (BagMatching (BagPat (sl @ sla, v))))
                      | Some _ -> None))))
    | SimTerm (l, kl), database ->
        (match simpleKToIRKList _A kl database with None -> None
          | Some kla ->
            (if isFunctionItem (equal_label _A) l database
              then (match getSort (equal_label _A) l database with None -> None
                     | Some t ->
                       (if equal_lista (equal_sort _A) t [KLabel]
                         then Some (KLabelFunPat (l, kla))
                         else (if equal_lista (equal_sort _A) t [K]
                                then Some (KFunPat (l, kla))
                                else (if equal_lista (equal_sort _A) t [List]
                                       then Some (ListFunPat (l, kla))
                                       else (if equal_lista (equal_sort _A) t
          [Seta]
      then Some (SetFunPat (l, kla))
      else (if equal_lista (equal_sort _A) t [Map]
             then Some (MapFunPat (l, kla))
             else Some (KItemFunPat (l, kla))))))))
              else (match l
                     with UnitLabel _ ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | ConstToLabel _ ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | Sort ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | GetKLabel ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | IsKResult ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | AndBool ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | NotBool ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | OrBool ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | SetConLabel ->
                       (match kla
                         with KListPatNoVar newkl ->
                           (match flattenSet newkl with None -> None
                             | Some sl ->
                               (match restructSet sl with None -> None
                                 | Some sla ->
                                   Some (NormalPat (SetMatching sla))))
                         | KListPat (_, _, _) -> None)
                     | SetItemLabel ->
                       (match kla with KListPatNoVar [] -> None
                         | KListPatNoVar [IRBigBag (IRK kx)] ->
                           Some (NormalPat (SetMatching (SetPat ([kx], None))))
                         | KListPatNoVar (IRBigBag (IRK _) :: _ :: _) -> None
                         | KListPatNoVar (IRBigBag (IRList _) :: _) -> None
                         | KListPatNoVar (IRBigBag (IRSet _) :: _) -> None
                         | KListPatNoVar (IRBigBag (IRMap _) :: _) -> None
                         | KListPatNoVar (IRBigBag (IRBag _) :: _) -> None
                         | KListPatNoVar (IRBigLabel _ :: _) -> None
                         | KListPat (_, _, _) -> None)
                     | ListConLabel ->
                       (match kla
                         with KListPatNoVar newkl ->
                           (match flattenList newkl with None -> None
                             | Some sl ->
                               (match restructList sl with None -> None
                                 | Some sla ->
                                   Some (NormalPat (ListMatching sla))))
                         | KListPat (_, _, _) -> None)
                     | ListItemLabel ->
                       (match kla with KListPatNoVar [] -> None
                         | KListPatNoVar [IRBigBag (IRK kx)] ->
                           Some (NormalPat (ListMatching (ListPatNoVar [kx])))
                         | KListPatNoVar (IRBigBag (IRK _) :: _ :: _) -> None
                         | KListPatNoVar (IRBigBag (IRList _) :: _) -> None
                         | KListPatNoVar (IRBigBag (IRSet _) :: _) -> None
                         | KListPatNoVar (IRBigBag (IRMap _) :: _) -> None
                         | KListPatNoVar (IRBigBag (IRBag _) :: _) -> None
                         | KListPatNoVar (IRBigLabel _ :: _) -> None
                         | KListPat (_, _, _) -> None)
                     | MapConLabel ->
                       (match kla
                         with KListPatNoVar newkl ->
                           (match flattenMap newkl with None -> None
                             | Some sl ->
                               (match restructMap sl with None -> None
                                 | Some sla ->
                                   Some (NormalPat (MapMatching sla))))
                         | KListPat (_, _, _) -> None)
                     | MapItemLabel ->
                       (match kla with KListPatNoVar [] -> None
                         | KListPatNoVar [IRBigBag (IRK _)] -> None
                         | KListPatNoVar [IRBigBag (IRK kx); IRBigBag (IRK ky)]
                           -> Some (NormalPat
                                     (MapMatching (MapPat ([(kx, ky)], None))))
                         | KListPatNoVar
                             (IRBigBag (IRK _) :: IRBigBag (IRK _) :: _ :: _)
                           -> None
                         | KListPatNoVar
                             (IRBigBag (IRK _) :: IRBigBag (IRList _) :: _)
                           -> None
                         | KListPatNoVar
                             (IRBigBag (IRK _) :: IRBigBag (IRSet _) :: _)
                           -> None
                         | KListPatNoVar
                             (IRBigBag (IRK _) :: IRBigBag (IRMap _) :: _)
                           -> None
                         | KListPatNoVar
                             (IRBigBag (IRK _) :: IRBigBag (IRBag _) :: _)
                           -> None
                         | KListPatNoVar (IRBigBag (IRK _) :: IRBigLabel _ :: _)
                           -> None
                         | KListPatNoVar (IRBigBag (IRList _) :: _) -> None
                         | KListPatNoVar (IRBigBag (IRSet _) :: _) -> None
                         | KListPatNoVar (IRBigBag (IRMap _) :: _) -> None
                         | KListPatNoVar (IRBigBag (IRBag _) :: _) -> None
                         | KListPatNoVar (IRBigLabel _ :: _) -> None
                         | KListPat (_, _, _) -> None)
                     | MapUpdate ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | EqualK ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | NotEqualK ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | EqualKLabel ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | NotEqualKLabel ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | OtherLabel _ ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | TokenLabel _ ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | PlusInt ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | MinusInt ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | TimesInt ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | EqualSet ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t)))))
                     | EqualMap ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (NormalPat
                                  (KItemMatching
                                    (IRKItem (IRKLabel l, kla, t))))))))
and simpleKToIRKList _A
  x0 database = match x0, database with [], database -> Some (KListPatNoVar [])
    | x :: xl, database ->
        (match simpleKToIRKList _A xl database with None -> None
          | Some (KListPatNoVar xla) ->
            (match simpleKToIR _A x database with None -> None
              | Some (KLabelFunPat (_, _)) -> None
              | Some (KFunPat (_, _)) -> None
              | Some (KItemFunPat (_, _)) -> None
              | Some (ListFunPat (_, _)) -> None
              | Some (SetFunPat (_, _)) -> None
              | Some (MapFunPat (_, _)) -> None
              | Some (NormalPat (KLabelMatching xa)) ->
                Some (KListPatNoVar (IRBigLabel xa :: xla))
              | Some (NormalPat (KItemMatching xa)) ->
                Some (KListPatNoVar (IRBigBag (IRK (KPat ([xa], None))) :: xla))
              | Some (NormalPat (KListMatching (KListPatNoVar sl))) ->
                Some (KListPatNoVar (sl @ xla))
              | Some (NormalPat (KListMatching (KListPat (sl, v, sla)))) ->
                Some (KListPat (sl, v, sla @ xla))
              | Some (NormalPat (KMatching xa)) ->
                Some (KListPatNoVar (IRBigBag (IRK xa) :: xla))
              | Some (NormalPat (ListMatching xa)) ->
                Some (KListPatNoVar (IRBigBag (IRList xa) :: xla))
              | Some (NormalPat (SetMatching xa)) ->
                Some (KListPatNoVar (IRBigBag (IRSet xa) :: xla))
              | Some (NormalPat (MapMatching xa)) ->
                Some (KListPatNoVar (IRBigBag (IRMap xa) :: xla))
              | Some (NormalPat (BagMatching xa)) ->
                Some (KListPatNoVar (IRBigBag (IRBag xa) :: xla)))
          | Some (KListPat (xl1, u, xl2)) ->
            (match simpleKToIR _A x database with None -> None
              | Some (KLabelFunPat (_, _)) -> None
              | Some (KFunPat (_, _)) -> None
              | Some (KItemFunPat (_, _)) -> None
              | Some (ListFunPat (_, _)) -> None
              | Some (SetFunPat (_, _)) -> None
              | Some (MapFunPat (_, _)) -> None
              | Some (NormalPat (KLabelMatching xa)) ->
                Some (KListPat (IRBigLabel xa :: xl1, u, xl2))
              | Some (NormalPat (KItemMatching xa)) ->
                Some (KListPat
                       (IRBigBag (IRK (KPat ([xa], None))) :: xl1, u, xl2))
              | Some (NormalPat (KListMatching (KListPatNoVar sl))) ->
                Some (KListPat (sl @ xl1, u, xl2))
              | Some (NormalPat (KListMatching (KListPat (_, _, _)))) -> None
              | Some (NormalPat (KMatching xa)) ->
                Some (KListPat (IRBigBag (IRK xa) :: xl1, u, xl2))
              | Some (NormalPat (ListMatching xa)) ->
                Some (KListPat (IRBigBag (IRList xa) :: xl1, u, xl2))
              | Some (NormalPat (SetMatching xa)) ->
                Some (KListPat (IRBigBag (IRSet xa) :: xl1, u, xl2))
              | Some (NormalPat (MapMatching xa)) ->
                Some (KListPat (IRBigBag (IRMap xa) :: xl1, u, xl2))
              | Some (NormalPat (BagMatching xa)) ->
                Some (KListPat (IRBigBag (IRBag xa) :: xl1, u, xl2))));;

let rec flattenSUList
  = function [] -> Some []
    | x :: xl ->
        (match flattenSUList xl with None -> None
          | Some xla ->
            (match x with ItemKl (SUBigBag (SUK _)) -> None
              | ItemKl (SUBigBag (SUList sl)) -> Some (sl @ xla)
              | ItemKl (SUBigBag (SUSet _)) -> None
              | ItemKl (SUBigBag (SUMap _)) -> None
              | ItemKl (SUBigBag (SUBag _)) -> None
              | ItemKl (SUBigLabel _) -> None | IdKl _ -> None));;

let rec flattenSUSet
  = function [] -> Some []
    | x :: xl ->
        (match flattenSUSet xl with None -> None
          | Some xla ->
            (match x with ItemKl (SUBigBag (SUK _)) -> None
              | ItemKl (SUBigBag (SUList _)) -> None
              | ItemKl (SUBigBag (SUSet sl)) -> Some (sl @ xla)
              | ItemKl (SUBigBag (SUMap _)) -> None
              | ItemKl (SUBigBag (SUBag _)) -> None
              | ItemKl (SUBigLabel _) -> None | IdKl _ -> None));;

let rec flattenSUMap
  = function [] -> Some []
    | x :: xl ->
        (match flattenSUMap xl with None -> None
          | Some xla ->
            (match x with ItemKl (SUBigBag (SUK _)) -> None
              | ItemKl (SUBigBag (SUList _)) -> None
              | ItemKl (SUBigBag (SUSet _)) -> None
              | ItemKl (SUBigBag (SUMap sl)) -> Some (sl @ xla)
              | ItemKl (SUBigBag (SUBag _)) -> None
              | ItemKl (SUBigLabel _) -> None | IdKl _ -> None));;

let rec simpleKToSU _A
  x0 database = match x0, database with
    SimId (x, y), database ->
      (match y with Bool -> Some (KItemSubs (SUIdKItem (x, [y])))
        | K -> Some (KSubs [IdFactor x])
        | KItem -> Some (KItemSubs (SUIdKItem (x, [y])))
        | KLabel -> Some (KLabelSubs (SUIdKLabel x))
        | KResult -> Some (KItemSubs (SUIdKItem (x, [y])))
        | KList -> Some (KListSubs [IdKl x]) | List -> Some (ListSubs [IdL x])
        | Seta -> Some (SetSubs [IdS x]) | Map -> Some (MapSubs [IdM x])
        | Bag -> Some (BagSubs [IdB x])
        | OtherSort _ -> Some (KItemSubs (SUIdKItem (x, [y])))
        | Top -> Some (KItemSubs (SUIdKItem (x, [y])))
        | Int -> Some (KItemSubs (SUIdKItem (x, [y])))
        | Float -> Some (KItemSubs (SUIdKItem (x, [y])))
        | Id -> Some (KItemSubs (SUIdKItem (x, [y])))
        | String -> Some (KItemSubs (SUIdKItem (x, [y]))))
    | SimEmpty y, database ->
        (match y
          with Bool ->
            Some (KItemSubs (SUKItem (SUKLabel (UnitLabel y), [], [y])))
          | K -> Some (KSubs [])
          | KItem ->
            Some (KItemSubs (SUKItem (SUKLabel (UnitLabel y), [], [y])))
          | KLabel ->
            Some (KItemSubs (SUKItem (SUKLabel (UnitLabel y), [], [y])))
          | KResult ->
            Some (KItemSubs (SUKItem (SUKLabel (UnitLabel y), [], [y])))
          | KList -> Some (KListSubs []) | List -> Some (ListSubs [])
          | Seta -> Some (SetSubs []) | Map -> Some (MapSubs [])
          | Bag -> Some (BagSubs [])
          | OtherSort _ ->
            Some (KItemSubs (SUKItem (SUKLabel (UnitLabel y), [], [y])))
          | Top -> Some (KItemSubs (SUKItem (SUKLabel (UnitLabel y), [], [y])))
          | Int -> Some (KItemSubs (SUKItem (SUKLabel (UnitLabel y), [], [y])))
          | Float ->
            Some (KItemSubs (SUKItem (SUKLabel (UnitLabel y), [], [y])))
          | Id -> Some (KItemSubs (SUKItem (SUKLabel (UnitLabel y), [], [y])))
          | String ->
            Some (KItemSubs (SUKItem (SUKLabel (UnitLabel y), [], [y]))))
    | SimLabel l, database -> Some (KLabelSubs (SUKLabel l))
    | SimBag (x, y, b), database ->
        (match simpleKToSU _A b database with None -> None
          | Some (KLabelSubs _) -> None
          | Some (KItemSubs s) ->
            Some (BagSubs [ItemB (x, y, SUK [ItemFactor s])])
          | Some (KListSubs _) -> None
          | Some (KSubs s) -> Some (BagSubs [ItemB (x, y, SUK s)])
          | Some (ListSubs s) -> Some (BagSubs [ItemB (x, y, SUList s)])
          | Some (SetSubs s) -> Some (BagSubs [ItemB (x, y, SUSet s)])
          | Some (MapSubs s) -> Some (BagSubs [ItemB (x, y, SUMap s)])
          | Some (BagSubs s) -> Some (BagSubs [ItemB (x, y, SUBag s)]))
    | SimBagCon (l, r), database ->
        (match simpleKToSU _A l database with None -> None
          | Some (KLabelSubs _) -> None | Some (KItemSubs _) -> None
          | Some (KListSubs _) -> None | Some (KSubs _) -> None
          | Some (ListSubs _) -> None | Some (SetSubs _) -> None
          | Some (MapSubs _) -> None
          | Some (BagSubs la) ->
            (match simpleKToSU _A r database with None -> None
              | Some (KLabelSubs _) -> None | Some (KItemSubs _) -> None
              | Some (KListSubs _) -> None | Some (KSubs _) -> None
              | Some (ListSubs _) -> None | Some (SetSubs _) -> None
              | Some (MapSubs _) -> None
              | Some (BagSubs ra) -> Some (BagSubs (la @ ra))))
    | SimTerm (l, kl), database ->
        (match simpleKToSUKList _A kl database with None -> None
          | Some kla ->
            (if isFunctionItem (equal_label _A) l database
              then (match getSort (equal_label _A) l database with None -> None
                     | Some t ->
                       (if equal_lista (equal_sort _A) t [KLabel]
                         then Some (KLabelSubs (SUKLabelFun (SUKLabel l, kla)))
                         else (if equal_lista (equal_sort _A) t [K]
                                then Some (KSubs
    [SUKKItem (SUKLabel l, kla, [K])])
                                else (if equal_lista (equal_sort _A) t [List]
                                       then Some (ListSubs
           [SUListKItem (SUKLabel l, kla)])
                                       else (if equal_lista (equal_sort _A) t
          [Seta]
      then Some (SetSubs [SUSetKItem (SUKLabel l, kla)])
      else (if equal_lista (equal_sort _A) t [Map]
             then Some (MapSubs [SUMapKItem (SUKLabel l, kla)])
             else Some (KItemSubs (SUKItem (SUKLabel l, kla, t)))))))))
              else (match l
                     with UnitLabel _ ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | ConstToLabel _ ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | Sort ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | GetKLabel ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | IsKResult ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | AndBool ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | NotBool ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | OrBool ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | SetConLabel ->
                       (match flattenSUSet kla with None -> None
                         | Some newkl -> Some (SetSubs newkl))
                     | SetItemLabel ->
                       (match kla with [] -> None
                         | [ItemKl (SUBigBag (SUK kx))] ->
                           Some (SetSubs [ItemS kx])
                         | ItemKl (SUBigBag (SUK _)) :: _ :: _ -> None
                         | ItemKl (SUBigBag (SUList _)) :: _ -> None
                         | ItemKl (SUBigBag (SUSet _)) :: _ -> None
                         | ItemKl (SUBigBag (SUMap _)) :: _ -> None
                         | ItemKl (SUBigBag (SUBag _)) :: _ -> None
                         | ItemKl (SUBigLabel _) :: _ -> None
                         | IdKl _ :: _ -> None)
                     | ListConLabel ->
                       (match flattenSUList kla with None -> None
                         | Some newkl -> Some (ListSubs newkl))
                     | ListItemLabel ->
                       (match kla with [] -> None
                         | [ItemKl (SUBigBag (SUK kx))] ->
                           Some (ListSubs [ItemL kx])
                         | ItemKl (SUBigBag (SUK _)) :: _ :: _ -> None
                         | ItemKl (SUBigBag (SUList _)) :: _ -> None
                         | ItemKl (SUBigBag (SUSet _)) :: _ -> None
                         | ItemKl (SUBigBag (SUMap _)) :: _ -> None
                         | ItemKl (SUBigBag (SUBag _)) :: _ -> None
                         | ItemKl (SUBigLabel _) :: _ -> None
                         | IdKl _ :: _ -> None)
                     | MapConLabel ->
                       (match flattenSUMap kla with None -> None
                         | Some newkl -> Some (MapSubs newkl))
                     | MapItemLabel ->
                       (match kla with [] -> None
                         | [ItemKl (SUBigBag (SUK _))] -> None
                         | [ItemKl (SUBigBag (SUK kx));
                             ItemKl (SUBigBag (SUK ky))]
                           -> Some (MapSubs [ItemM (kx, ky)])
                         | ItemKl (SUBigBag (SUK _)) ::
                             ItemKl (SUBigBag (SUK _)) :: _ :: _
                           -> None
                         | ItemKl (SUBigBag (SUK _)) ::
                             ItemKl (SUBigBag (SUList _)) :: _
                           -> None
                         | ItemKl (SUBigBag (SUK _)) ::
                             ItemKl (SUBigBag (SUSet _)) :: _
                           -> None
                         | ItemKl (SUBigBag (SUK _)) ::
                             ItemKl (SUBigBag (SUMap _)) :: _
                           -> None
                         | ItemKl (SUBigBag (SUK _)) ::
                             ItemKl (SUBigBag (SUBag _)) :: _
                           -> None
                         | ItemKl (SUBigBag (SUK _)) ::
                             ItemKl (SUBigLabel _) :: _
                           -> None
                         | ItemKl (SUBigBag (SUK _)) :: IdKl _ :: _ -> None
                         | ItemKl (SUBigBag (SUList _)) :: _ -> None
                         | ItemKl (SUBigBag (SUSet _)) :: _ -> None
                         | ItemKl (SUBigBag (SUMap _)) :: _ -> None
                         | ItemKl (SUBigBag (SUBag _)) :: _ -> None
                         | ItemKl (SUBigLabel _) :: _ -> None
                         | IdKl _ :: _ -> None)
                     | MapUpdate ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | EqualK ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | NotEqualK ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | EqualKLabel ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | NotEqualKLabel ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | OtherLabel _ ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | TokenLabel _ ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | PlusInt ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | MinusInt ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | TimesInt ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | EqualSet ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t))))
                     | EqualMap ->
                       (match getSort (equal_label _A) l database
                         with None -> None
                         | Some t ->
                           Some (KItemSubs (SUKItem (SUKLabel l, kla, t)))))))
and simpleKToSUKList _A
  x0 database = match x0, database with [], database -> Some []
    | x :: xl, database ->
        (match simpleKToSUKList _A xl database with None -> None
          | Some xla ->
            (match simpleKToSU _A x database with None -> None
              | Some (KLabelSubs xa) -> Some (ItemKl (SUBigLabel xa) :: xla)
              | Some (KItemSubs xa) ->
                Some (ItemKl (SUBigBag (SUK [ItemFactor xa])) :: xla)
              | Some (KListSubs sl) -> Some (sl @ xla)
              | Some (KSubs xa) -> Some (ItemKl (SUBigBag (SUK xa)) :: xla)
              | Some (ListSubs xa) ->
                Some (ItemKl (SUBigBag (SUList xa)) :: xla)
              | Some (SetSubs xa) -> Some (ItemKl (SUBigBag (SUSet xa)) :: xla)
              | Some (MapSubs xa) -> Some (ItemKl (SUBigBag (SUMap xa)) :: xla)
              | Some (BagSubs xa) ->
                Some (ItemKl (SUBigBag (SUBag xa)) :: xla)));;

let rec mergeFunRules _A
  l a b x3 = match l, a, b, x3 with l, a, b, [] -> Some [FunPat (l, a, b)]
    | l, a, b, x :: xl ->
        (match x
          with FunPat (la, aa, ba) ->
            (if equal_labela _A l la
              then (match b with None -> Some (FunPat (l, aa @ a, ba) :: xl)
                     | Some bo ->
                       (match ba
                         with None -> Some (FunPat (l, aa @ a, Some bo) :: xl)
                         | Some _ -> None))
              else (match mergeFunRules _A l a b xl with None -> None
                     | Some xla -> Some (x :: xla)))
          | MacroPat (_, _, _) ->
            (match mergeFunRules _A l a b xl with None -> None
              | Some xla -> Some (x :: xla))
          | AnywherePat (_, _, _, _) ->
            (match mergeFunRules _A l a b xl with None -> None
              | Some xla -> Some (x :: xla))
          | KRulePat (_, _, _, _) ->
            (match mergeFunRules _A l a b xl with None -> None
              | Some xla -> Some (x :: xla))
          | BagRulePat (_, _, _, _) ->
            (match mergeFunRules _A l a b xl with None -> None
              | Some xla -> Some (x :: xla)));;

let rec getAllSubsortOnItem _A
  x0 a = match x0, a with [], a -> []
    | (x, y) :: l, a ->
        (if eq _A y a then x :: getAllSubsortOnItem _A l a
          else getAllSubsortOnItem _A l a);;

let rec formGraph _A
  x0 s = match x0, s with [], s -> []
    | a :: l, s -> (a, getAllSubsortOnItem _A s a) :: formGraph _A l s;;

let rec insertA _A
  xa0 a x = match xa0, a, x with [], a, x -> [(a, [x])]
    | (a, kl) :: l, v, x ->
        (if eq _A a v then (a, x :: kl) :: l else (a, kl) :: insertA _A l v x);;

let rec regPart
  x a xa2 = match x, a, xa2 with x, a, [] -> regMatch x a
    | x, a, s :: l ->
        (if regMatch x a then regMatch (Rep x) (s :: l)
          else regPart x (a @ [s]) l)
and regMatch
  a s = (match a with Eps -> null s | Sym x -> equal_lista equal_char s [x]
          | Alt (x, y) -> regMatch x s || regMatch y s
          | TheSeq (x, y) -> regSplit x y [] s
          | Rep x -> (match s with [] -> true | b :: aa -> regPart x [b] aa))
and regSplit
  x y s xa3 = match x, y, s, xa3 with x, y, s, [] -> false
    | x, y, s, a :: al ->
        (if regMatch x s then regMatch y (a :: al)
          else regSplit x y (s @ [a]) al);;

let rec typeCheckProgramState _A _B _C
  a database subG =
    (if isGroundTermInSUBag a
      then (match checkTermsInSUBag _A _C a [] [] database subG
             with None -> None
             | Some (_, (_, aa)) -> regularizeInSUBag _A _B _C aa subG)
      else None);;

let rec funEvaluationAux_i_i_i_i_i_i_o _A _B _C
  x xa xb xc xd xe =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
        (fun a ->
          (match a with (_, (_, (_, ([], (_, Continue br))))) -> single (Div br)
            | (_, (_, (_, ([], (_, Stop _))))) -> bot_pred
            | (_, (_, (_, ([], (_, Div _))))) -> bot_pred
            | (_, (_, (_, (_ :: _, _)))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
          (fun a ->
            (match a with (_, (_, (_, ([], _)))) -> bot_pred
              | (allRules,
                  (database, (subG, ((p, (_, _)) :: fl, (funa, Continue br)))))
                -> bind (eq_i_i
                          (equal_option
                            (equal_list
                              (equal_prod (equal_metaVar _C)
                                (equal_subsFactor _A _B _C))))
                          (patternMacroingInSUKList _A _B _C _C p funa [] subG)
                          None)
                     (fun () ->
                       bind (funEvaluationAux_i_i_i_i_i_i_o _A _B _C allRules
                              database subG fl funa (Continue br))
                         (fun aa ->
                           (match aa with Continue _ -> bot_pred
                             | Stop b -> single (Stop b) | Div _ -> bot_pred)))
              | (_, (_, (_, ((_, (_, _)) :: _, (_, Stop _))))) -> bot_pred
              | (_, (_, (_, ((_, (_, _)) :: _, (_, Div _))))) -> bot_pred)))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allRules,
                    (database,
                      (subG, ((p, (_, c)) :: fl, (funa, Continue br)))))
                  -> bind (funEvaluationAux_i_i_i_i_i_i_o _A _B _C allRules
                            database subG fl funa (Continue br))
                       (fun aa ->
                         (match aa with Continue _ -> bot_pred
                           | Stop b ->
                             bind (eq_i_o
                                    (patternMacroingInSUKList _A _B _C _C p funa
                                      [] subG))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some acc ->
                                     bind (eq_i_o
    (substitutionInSUKItem _C c acc))
                                       (fun ac ->
 (match ac with None -> bot_pred
   | Some value ->
     bind (funEvaluationBool_i_i_i_i_o _A _B _C allRules database subG
            (Continue value))
       (fun ad ->
         (match ad with Continue _ -> bot_pred
           | Stop valuea ->
             bind (eq_i_i (equal_option (equal_label _A))
                    (getKLabelInSUKItem valuea)
                    (Some (ConstToLabel (BoolConst false))))
               (fun () -> single (Stop b))
           | Div _ -> bot_pred))))))
                           | Div _ -> bot_pred))
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Stop _))))) -> bot_pred
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Div _))))) -> bot_pred)))
          (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allRules,
                    (database, (subG, ((p, (r, c)) :: _, (funa, Continue br)))))
                  -> bind (eq_i_o
                            (patternMacroingInSUKList _A _B _C _C p funa []
                              subG))
                       (fun aa ->
                         (match aa with None -> bot_pred
                           | Some acc ->
                             bind (eq_i_o (substitutionInSUKItem _C c acc))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some value ->
                                     bind (funEvaluationBool_i_i_i_i_o _A _B _C
    allRules database subG (Continue value))
                                       (fun ac ->
 (match ac with Continue _ -> bot_pred
   | Stop valuea ->
     bind (eq_i_i (equal_option (equal_label _A)) (getKLabelInSUKItem valuea)
            (Some (ConstToLabel (BoolConst true))))
       (fun () ->
         bind (eq_i_o (substitutionInSubsFactor _C r acc))
           (fun ad ->
             (match ad with None -> bot_pred
               | Some ra ->
                 bind (eq_i_o (substitutionInSUBag _C br [(FunHole, ra)]))
                   (fun ae ->
                     (match ae with None -> bot_pred
                       | Some b ->
                         bind (eq_i_o
                                (typeCheckProgramState _A _B _C b database
                                  subG))
                           (fun af ->
                             (match af with None -> bot_pred
                               | Some ba -> single (Stop ba))))))))
   | Div _ -> bot_pred))))))
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Stop _))))) -> bot_pred
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Div _))))) ->
                  bot_pred)))));;

let rec funEvaluation_i_i_i_i_o _A _B _C
  x xa xb xc =
    sup_pred
      (bind (single (x, (xa, (xb, xc))))
        (fun a ->
          (match a
            with (_, (database, (_, Continue b))) ->
              bind (if_pred (not (hasFunLabelInSUBag _A b database)))
                (fun () -> single (Stop b))
            | (_, (_, (_, Stop _))) -> bot_pred
            | (_, (_, (_, Div _))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, xc))))
          (fun a ->
            (match a
              with (allRules, (database, (subG, Continue c))) ->
                bind (if_pred (hasFunLabelInSUBag _A c database))
                  (fun () ->
                    bind (eq_i_o (localteFunTermInSUBag _A c database))
                      (fun aa ->
                        (match aa with None -> bot_pred
                          | Some (l, (funa, (_, cr))) ->
                            bind (if_pred
                                   (membera (equal_label _A) builtinLabels l))
                              (fun () ->
                                bind (eq_i_o
                                       (evalBuiltinFun _A _B _C _A l funa
 database subG))
                                  (fun ab ->
                                    (match ab with None -> bot_pred
                                      | Some r ->
bind (eq_i_o (substitutionInSUBag _C cr [(FunHole, r)]))
  (fun ac ->
    (match ac with None -> bot_pred
      | Some ca ->
        bind (funEvaluation_i_i_i_i_o _A _B _C allRules database subG
               (Continue ca))
          (fun ad ->
            (match ad with Continue _ -> bot_pred | Stop cb -> single (Stop cb)
              | Div _ -> bot_pred))))))))))
              | (_, (_, (_, Stop _))) -> bot_pred
              | (_, (_, (_, Div _))) -> bot_pred)))
        (bind (single (x, (xa, (xb, xc))))
          (fun a ->
            (match a
              with (allRules, (database, (subG, Continue b))) ->
                bind (if_pred (hasFunLabelInSUBag _A b database))
                  (fun () ->
                    bind (eq_i_o (localteFunTermInSUBag _A b database))
                      (fun aa ->
                        (match aa with None -> bot_pred
                          | Some (l, (funa, (_, br))) ->
                            bind (if_pred
                                   (not (membera (equal_label _A) builtinLabels
  l)))
                              (fun () ->
                                bind (eq_i_o (getFunRule _A l allRules))
                                  (fun ab ->
                                    (match ab with None -> bot_pred
                                      | Some fl ->
bind (funEvaluationAux_i_i_i_i_i_i_o _A _B _C allRules database subG fl funa
       (Continue br))
  (fun ac ->
    (match ac with Continue _ -> bot_pred
      | Stop ba ->
        bind (funEvaluation_i_i_i_i_o _A _B _C allRules database subG
               (Continue ba))
          (fun ad ->
            (match ad with Continue _ -> bot_pred | Stop bb -> single (Stop bb)
              | Div _ -> bot_pred))
      | Div _ -> bot_pred))))))))
              | (_, (_, (_, Stop _))) -> bot_pred
              | (_, (_, (_, Div _))) -> bot_pred))));;

let rec funRuleEvalFun _A _B _C
  allRules database subG c =
    the (equal_state (equal_list (equal_suB _A _B _C)))
      (funEvaluation_i_i_i_i_o _A _B _C allRules database subG (Continue c));;

let rec removeSubsorts
  = function [] -> []
    | x :: xl ->
        (match x with Syntax (_, _, _) -> x :: removeSubsorts xl
          | Subsort (_, _) -> removeSubsorts xl
          | Token (_, _, _) -> x :: removeSubsorts xl
          | ListSyntax (_, _, _, _) -> x :: removeSubsorts xl);;

let rec tupleToRulePat _A _D _E
  (x, (y, (z, u))) database =
    (if membera (equal_ruleAttrib _D _E) u Macro
      then (match simpleKToIR _A x database with None -> None
             | Some (KLabelFunPat (_, _)) -> None
             | Some (KFunPat (_, _)) -> None | Some (KItemFunPat (_, _)) -> None
             | Some (ListFunPat (_, _)) -> None
             | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
             | Some (NormalPat (KLabelMatching _)) -> None
             | Some (NormalPat (KItemMatching (IRKItem (IRKLabel l, kl, _)))) ->
               (match simpleKToSU _A y database with None -> None
                 | Some (KLabelSubs _) -> None
                 | Some (KItemSubs ya) ->
                   (match simpleKToSU _A z database with None -> None
                     | Some (KLabelSubs _) -> None
                     | Some (KItemSubs za) ->
                       (match getKLabelInSUKItem za with None -> None
                         | Some (UnitLabel _) -> None
                         | Some (ConstToLabel (IntConst _)) -> None
                         | Some (ConstToLabel (FloatConst _)) -> None
                         | Some (ConstToLabel (StringConst _)) -> None
                         | Some (ConstToLabel (BoolConst true)) ->
                           Some (MacroPat (l, kl, [ItemFactor ya]))
                         | Some (ConstToLabel (BoolConst false)) -> None
                         | Some (ConstToLabel (IdConst _)) -> None
                         | Some Sort -> None | Some GetKLabel -> None
                         | Some IsKResult -> None | Some AndBool -> None
                         | Some NotBool -> None | Some OrBool -> None
                         | Some SetConLabel -> None | Some SetItemLabel -> None
                         | Some ListConLabel -> None
                         | Some ListItemLabel -> None | Some MapConLabel -> None
                         | Some MapItemLabel -> None | Some MapUpdate -> None
                         | Some EqualK -> None | Some NotEqualK -> None
                         | Some EqualKLabel -> None
                         | Some NotEqualKLabel -> None
                         | Some (OtherLabel _) -> None
                         | Some (TokenLabel _) -> None | Some PlusInt -> None
                         | Some MinusInt -> None | Some TimesInt -> None
                         | Some EqualSet -> None | Some EqualMap -> None)
                     | Some (KListSubs _) -> None | Some (KSubs _) -> None
                     | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                     | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
                 | Some (KListSubs _) -> None
                 | Some (KSubs ya) ->
                   (match simpleKToSU _A z database with None -> None
                     | Some (KLabelSubs _) -> None
                     | Some (KItemSubs za) ->
                       (match getKLabelInSUKItem za with None -> None
                         | Some (UnitLabel _) -> None
                         | Some (ConstToLabel (IntConst _)) -> None
                         | Some (ConstToLabel (FloatConst _)) -> None
                         | Some (ConstToLabel (StringConst _)) -> None
                         | Some (ConstToLabel (BoolConst true)) ->
                           Some (MacroPat (l, kl, ya))
                         | Some (ConstToLabel (BoolConst false)) -> None
                         | Some (ConstToLabel (IdConst _)) -> None
                         | Some Sort -> None | Some GetKLabel -> None
                         | Some IsKResult -> None | Some AndBool -> None
                         | Some NotBool -> None | Some OrBool -> None
                         | Some SetConLabel -> None | Some SetItemLabel -> None
                         | Some ListConLabel -> None
                         | Some ListItemLabel -> None | Some MapConLabel -> None
                         | Some MapItemLabel -> None | Some MapUpdate -> None
                         | Some EqualK -> None | Some NotEqualK -> None
                         | Some EqualKLabel -> None
                         | Some NotEqualKLabel -> None
                         | Some (OtherLabel _) -> None
                         | Some (TokenLabel _) -> None | Some PlusInt -> None
                         | Some MinusInt -> None | Some TimesInt -> None
                         | Some EqualSet -> None | Some EqualMap -> None)
                     | Some (KListSubs _) -> None | Some (KSubs _) -> None
                     | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                     | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
                 | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                 | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
             | Some (NormalPat (KItemMatching (IRKItem (IRIdKLabel _, _, _))))
               -> None
             | Some (NormalPat (KItemMatching (IRIdKItem (_, _)))) -> None
             | Some (NormalPat (KItemMatching (IRHOLE _))) -> None
             | Some (NormalPat (KListMatching _)) -> None
             | Some (NormalPat (KMatching (KPat ([], _)))) -> None
             | Some (NormalPat
                      (KMatching (KPat ([IRKItem (IRKLabel l, kl, _)], None))))
               -> (match simpleKToSU _A y database with None -> None
                    | Some (KLabelSubs _) -> None
                    | Some (KItemSubs ya) ->
                      (match simpleKToSU _A z database with None -> None
                        | Some (KLabelSubs _) -> None
                        | Some (KItemSubs za) ->
                          (match getKLabelInSUKItem za with None -> None
                            | Some (UnitLabel _) -> None
                            | Some (ConstToLabel (IntConst _)) -> None
                            | Some (ConstToLabel (FloatConst _)) -> None
                            | Some (ConstToLabel (StringConst _)) -> None
                            | Some (ConstToLabel (BoolConst true)) ->
                              Some (MacroPat (l, kl, [ItemFactor ya]))
                            | Some (ConstToLabel (BoolConst false)) -> None
                            | Some (ConstToLabel (IdConst _)) -> None
                            | Some Sort -> None | Some GetKLabel -> None
                            | Some IsKResult -> None | Some AndBool -> None
                            | Some NotBool -> None | Some OrBool -> None
                            | Some SetConLabel -> None
                            | Some SetItemLabel -> None
                            | Some ListConLabel -> None
                            | Some ListItemLabel -> None
                            | Some MapConLabel -> None
                            | Some MapItemLabel -> None | Some MapUpdate -> None
                            | Some EqualK -> None | Some NotEqualK -> None
                            | Some EqualKLabel -> None
                            | Some NotEqualKLabel -> None
                            | Some (OtherLabel _) -> None
                            | Some (TokenLabel _) -> None | Some PlusInt -> None
                            | Some MinusInt -> None | Some TimesInt -> None
                            | Some EqualSet -> None | Some EqualMap -> None)
                        | Some (KListSubs _) -> None | Some (KSubs _) -> None
                        | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                        | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
                    | Some (KListSubs _) -> None
                    | Some (KSubs ya) ->
                      (match simpleKToSU _A z database with None -> None
                        | Some (KLabelSubs _) -> None
                        | Some (KItemSubs za) ->
                          (match getKLabelInSUKItem za with None -> None
                            | Some (UnitLabel _) -> None
                            | Some (ConstToLabel (IntConst _)) -> None
                            | Some (ConstToLabel (FloatConst _)) -> None
                            | Some (ConstToLabel (StringConst _)) -> None
                            | Some (ConstToLabel (BoolConst true)) ->
                              Some (MacroPat (l, kl, ya))
                            | Some (ConstToLabel (BoolConst false)) -> None
                            | Some (ConstToLabel (IdConst _)) -> None
                            | Some Sort -> None | Some GetKLabel -> None
                            | Some IsKResult -> None | Some AndBool -> None
                            | Some NotBool -> None | Some OrBool -> None
                            | Some SetConLabel -> None
                            | Some SetItemLabel -> None
                            | Some ListConLabel -> None
                            | Some ListItemLabel -> None
                            | Some MapConLabel -> None
                            | Some MapItemLabel -> None | Some MapUpdate -> None
                            | Some EqualK -> None | Some NotEqualK -> None
                            | Some EqualKLabel -> None
                            | Some NotEqualKLabel -> None
                            | Some (OtherLabel _) -> None
                            | Some (TokenLabel _) -> None | Some PlusInt -> None
                            | Some MinusInt -> None | Some TimesInt -> None
                            | Some EqualSet -> None | Some EqualMap -> None)
                        | Some (KListSubs _) -> None | Some (KSubs _) -> None
                        | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                        | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
                    | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                    | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
             | Some (NormalPat
                      (KMatching (KPat ([IRKItem (IRKLabel _, _, _)], Some _))))
               -> None
             | Some (NormalPat
                      (KMatching
                        (KPat (IRKItem (IRKLabel _, _, _) :: _ :: _, _))))
               -> None
             | Some (NormalPat
                      (KMatching (KPat (IRKItem (IRIdKLabel _, _, _) :: _, _))))
               -> None
             | Some (NormalPat (KMatching (KPat (IRIdKItem (_, _) :: _, _)))) ->
               None
             | Some (NormalPat (KMatching (KPat (IRHOLE _ :: _, _)))) -> None
             | Some (NormalPat (ListMatching _)) -> None
             | Some (NormalPat (SetMatching _)) -> None
             | Some (NormalPat (MapMatching _)) -> None
             | Some (NormalPat (BagMatching _)) -> None)
      else (if membera (equal_ruleAttrib _D _E) u Anywhere
             then (match simpleKToIR _A x database with None -> None
                    | Some (KLabelFunPat (_, _)) -> None
                    | Some (KFunPat (_, _)) -> None
                    | Some (KItemFunPat (_, _)) -> None
                    | Some (ListFunPat (_, _)) -> None
                    | Some (SetFunPat (_, _)) -> None
                    | Some (MapFunPat (_, _)) -> None
                    | Some (NormalPat (KLabelMatching _)) -> None
                    | Some (NormalPat
                             (KItemMatching (IRKItem (IRKLabel l, kl, _))))
                      -> (match simpleKToSU _A y database with None -> None
                           | Some (KLabelSubs _) -> None
                           | Some (KItemSubs ya) ->
                             (match simpleKToSU _A z database with None -> None
                               | Some (KLabelSubs _) -> None
                               | Some (KItemSubs za) ->
                                 Some (AnywherePat (l, kl, [ItemFactor ya], za))
                               | Some (KListSubs _) -> None
                               | Some (KSubs _) -> None
                               | Some (ListSubs _) -> None
                               | Some (SetSubs _) -> None
                               | Some (MapSubs _) -> None
                               | Some (BagSubs _) -> None)
                           | Some (KListSubs _) -> None
                           | Some (KSubs ya) ->
                             (match simpleKToSU _A z database with None -> None
                               | Some (KLabelSubs _) -> None
                               | Some (KItemSubs za) ->
                                 Some (AnywherePat (l, kl, ya, za))
                               | Some (KListSubs _) -> None
                               | Some (KSubs _) -> None
                               | Some (ListSubs _) -> None
                               | Some (SetSubs _) -> None
                               | Some (MapSubs _) -> None
                               | Some (BagSubs _) -> None)
                           | Some (ListSubs _) -> None
                           | Some (SetSubs _) -> None | Some (MapSubs _) -> None
                           | Some (BagSubs _) -> None)
                    | Some (NormalPat
                             (KItemMatching (IRKItem (IRIdKLabel _, _, _))))
                      -> None
                    | Some (NormalPat (KItemMatching (IRIdKItem (_, _)))) ->
                      None
                    | Some (NormalPat (KItemMatching (IRHOLE _))) -> None
                    | Some (NormalPat (KListMatching _)) -> None
                    | Some (NormalPat (KMatching (KPat ([], _)))) -> None
                    | Some (NormalPat
                             (KMatching
                               (KPat ([IRKItem (IRKLabel l, kl, _)], None))))
                      -> (match simpleKToSU _A y database with None -> None
                           | Some (KLabelSubs _) -> None
                           | Some (KItemSubs ya) ->
                             (match simpleKToSU _A z database with None -> None
                               | Some (KLabelSubs _) -> None
                               | Some (KItemSubs za) ->
                                 Some (AnywherePat (l, kl, [ItemFactor ya], za))
                               | Some (KListSubs _) -> None
                               | Some (KSubs _) -> None
                               | Some (ListSubs _) -> None
                               | Some (SetSubs _) -> None
                               | Some (MapSubs _) -> None
                               | Some (BagSubs _) -> None)
                           | Some (KListSubs _) -> None
                           | Some (KSubs ya) ->
                             (match simpleKToSU _A z database with None -> None
                               | Some (KLabelSubs _) -> None
                               | Some (KItemSubs za) ->
                                 Some (AnywherePat (l, kl, ya, za))
                               | Some (KListSubs _) -> None
                               | Some (KSubs _) -> None
                               | Some (ListSubs _) -> None
                               | Some (SetSubs _) -> None
                               | Some (MapSubs _) -> None
                               | Some (BagSubs _) -> None)
                           | Some (ListSubs _) -> None
                           | Some (SetSubs _) -> None | Some (MapSubs _) -> None
                           | Some (BagSubs _) -> None)
                    | Some (NormalPat
                             (KMatching
                               (KPat ([IRKItem (IRKLabel _, _, _)], Some _))))
                      -> None
                    | Some (NormalPat
                             (KMatching
                               (KPat (IRKItem (IRKLabel _, _, _) :: _ :: _,
                                       _))))
                      -> None
                    | Some (NormalPat
                             (KMatching
                               (KPat (IRKItem (IRIdKLabel _, _, _) :: _, _))))
                      -> None
                    | Some (NormalPat
                             (KMatching (KPat (IRIdKItem (_, _) :: _, _))))
                      -> None
                    | Some (NormalPat (KMatching (KPat (IRHOLE _ :: _, _)))) ->
                      None
                    | Some (NormalPat (ListMatching _)) -> None
                    | Some (NormalPat (SetMatching _)) -> None
                    | Some (NormalPat (MapMatching _)) -> None
                    | Some (NormalPat (BagMatching _)) -> None)
             else (match simpleKToIR _A x database
                    with Some (KLabelFunPat (l, kl)) ->
                      (match simpleKToSU _A y database with None -> None
                        | Some (KLabelSubs ya) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              (if not (membera (equal_ruleAttrib _D _E) u Owise)
                                then Some (FunPat
    (l, [(KLabelFunPat (l, kl), (KLabelSubs ya, za))], None))
                                else Some (FunPat
    (l, [], Some (KLabelFunPat (l, kl), (KLabelSubs ya, za)))))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)
                        | Some (KItemSubs _) -> None
                        | Some (KListSubs _) -> None | Some (KSubs _) -> None
                        | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                        | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
                    | Some (KFunPat (l, kl)) ->
                      (match simpleKToSU _A y database with None -> None
                        | Some (KLabelSubs _) -> None
                        | Some (KItemSubs ya) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              (if not (membera (equal_ruleAttrib _D _E) u Owise)
                                then Some (FunPat
    (l, [(KFunPat (l, kl), (KSubs [ItemFactor ya], za))], None))
                                else Some (FunPat
    (l, [], Some (KFunPat (l, kl), (KSubs [ItemFactor ya], za)))))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)
                        | Some (KListSubs _) -> None
                        | Some (KSubs ya) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              (if not (membera (equal_ruleAttrib _D _E) u Owise)
                                then Some (FunPat
    (l, [(KFunPat (l, kl), (KSubs ya, za))], None))
                                else Some (FunPat
    (l, [], Some (KFunPat (l, kl), (KSubs ya, za)))))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)
                        | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                        | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
                    | Some (KItemFunPat (l, kl)) ->
                      (match simpleKToSU _A y database with None -> None
                        | Some (KLabelSubs _) -> None
                        | Some (KItemSubs ya) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              (if not (membera (equal_ruleAttrib _D _E) u Owise)
                                then Some (FunPat
    (l, [(KItemFunPat (l, kl), (KItemSubs ya, za))], None))
                                else Some (FunPat
    (l, [], Some (KItemFunPat (l, kl), (KItemSubs ya, za)))))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)
                        | Some (KListSubs _) -> None | Some (KSubs []) -> None
                        | Some (KSubs [ItemFactor ya]) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              (if not (membera (equal_ruleAttrib _D _E) u Owise)
                                then Some (FunPat
    (l, [(KItemFunPat (l, kl), (KItemSubs ya, za))], None))
                                else Some (FunPat
    (l, [], Some (KItemFunPat (l, kl), (KItemSubs ya, za)))))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)
                        | Some (KSubs (ItemFactor _ :: _ :: _)) -> None
                        | Some (KSubs (IdFactor _ :: _)) -> None
                        | Some (KSubs (SUKKItem (_, _, _) :: _)) -> None
                        | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                        | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
                    | Some (ListFunPat (l, kl)) ->
                      (match simpleKToSU _A y database with None -> None
                        | Some (KLabelSubs _) -> None
                        | Some (KItemSubs _) -> None
                        | Some (KListSubs _) -> None | Some (KSubs _) -> None
                        | Some (ListSubs ya) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              (if not (membera (equal_ruleAttrib _D _E) u Owise)
                                then Some (FunPat
    (l, [(ListFunPat (l, kl), (ListSubs ya, za))], None))
                                else Some (FunPat
    (l, [], Some (ListFunPat (l, kl), (ListSubs ya, za)))))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)
                        | Some (SetSubs _) -> None | Some (MapSubs _) -> None
                        | Some (BagSubs _) -> None)
                    | Some (SetFunPat (l, kl)) ->
                      (match simpleKToSU _A y database with None -> None
                        | Some (KLabelSubs _) -> None
                        | Some (KItemSubs _) -> None
                        | Some (KListSubs _) -> None | Some (KSubs _) -> None
                        | Some (ListSubs _) -> None
                        | Some (SetSubs ya) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              (if not (membera (equal_ruleAttrib _D _E) u Owise)
                                then Some (FunPat
    (l, [(SetFunPat (l, kl), (SetSubs ya, za))], None))
                                else Some (FunPat
    (l, [], Some (SetFunPat (l, kl), (SetSubs ya, za)))))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)
                        | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
                    | Some (MapFunPat (l, kl)) ->
                      (match simpleKToSU _A y database with None -> None
                        | Some (KLabelSubs _) -> None
                        | Some (KItemSubs _) -> None
                        | Some (KListSubs _) -> None | Some (KSubs _) -> None
                        | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                        | Some (MapSubs ya) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              (if not (membera (equal_ruleAttrib _D _E) u Owise)
                                then Some (FunPat
    (l, [(MapFunPat (l, kl), (MapSubs ya, za))], None))
                                else Some (FunPat
    (l, [], Some (MapFunPat (l, kl), (MapSubs ya, za)))))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)
                        | Some (BagSubs _) -> None)
                    | Some (NormalPat (KItemMatching xa)) ->
                      (match simpleKToSU _A y database with None -> None
                        | Some (KLabelSubs _) -> None
                        | Some (KItemSubs ya) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              Some (KRulePat
                                     (KPat ([xa], None), [ItemFactor ya], za,
                                       (if membera (equal_ruleAttrib _D _E) u
     Transition
 then true else false)))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)
                        | Some (KListSubs _) -> None
                        | Some (KSubs ya) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              Some (KRulePat
                                     (KPat ([xa], None), ya, za,
                                       (if membera (equal_ruleAttrib _D _E) u
     Transition
 then true else false)))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)
                        | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                        | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
                    | Some (NormalPat (KMatching xa)) ->
                      (match simpleKToSU _A y database with None -> None
                        | Some (KLabelSubs _) -> None
                        | Some (KItemSubs ya) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              Some (KRulePat
                                     (xa, [ItemFactor ya], za,
                                       (if membera (equal_ruleAttrib _D _E) u
     Transition
 then true else false)))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)
                        | Some (KListSubs _) -> None
                        | Some (KSubs ya) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              Some (KRulePat
                                     (xa, ya, za,
                                       (if membera (equal_ruleAttrib _D _E) u
     Transition
 then true else false)))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)
                        | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                        | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
                    | Some (NormalPat (BagMatching xa)) ->
                      (match simpleKToSU _A y database with None -> None
                        | Some (KLabelSubs _) -> None
                        | Some (KItemSubs _) -> None
                        | Some (KListSubs _) -> None | Some (KSubs _) -> None
                        | Some (ListSubs _) -> None | Some (SetSubs _) -> None
                        | Some (MapSubs _) -> None
                        | Some (BagSubs ya) ->
                          (match simpleKToSU _A z database with None -> None
                            | Some (KLabelSubs _) -> None
                            | Some (KItemSubs za) ->
                              Some (BagRulePat
                                     (xa, ya, za,
                                       (if membera (equal_ruleAttrib _D _E) u
     Transition
 then true else false)))
                            | Some (KListSubs _) -> None
                            | Some (KSubs _) -> None | Some (ListSubs _) -> None
                            | Some (SetSubs _) -> None
                            | Some (MapSubs _) -> None
                            | Some (BagSubs _) -> None)))));;

let rec hasOutOfPositionStrict
  x0 l = match x0, l with [], l -> false
    | n :: la, l ->
        (if less_nat (size_list l) n then true
          else hasOutOfPositionStrict la l);;

let rec getArgSortsInSyntax
  = function Single (NonTerminal a) -> [[a]]
    | Single (Terminal a) -> []
    | Con (NonTerminal a, l) -> [a] :: getArgSortsInSyntax l
    | Con (Terminal a, l) -> getArgSortsInSyntax l;;

let rec getRidStrictAttrs
  = function [] -> []
    | b :: l ->
        (match b with Strict _ -> getRidStrictAttrs l
          | Seqstrict -> getRidStrictAttrs l | Left -> b :: getRidStrictAttrs l
          | Right -> b :: getRidStrictAttrs l
          | Hook _ -> b :: getRidStrictAttrs l
          | Function -> b :: getRidStrictAttrs l
          | Klabel _ -> b :: getRidStrictAttrs l
          | Bracket -> b :: getRidStrictAttrs l
          | Tokena -> b :: getRidStrictAttrs l
          | Avoid -> b :: getRidStrictAttrs l
          | OnlyLabel -> b :: getRidStrictAttrs l
          | NotInRules -> b :: getRidStrictAttrs l
          | Regex _ -> b :: getRidStrictAttrs l
          | NonAssoc -> b :: getRidStrictAttrs l
          | OtherSynAttr _ -> b :: getRidStrictAttrs l);;

let rec symbolsToKLabelAux
  = function Single (Terminal s) -> s
    | Single (NonTerminal v) ->
        [Char (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One))))))]
    | Con (NonTerminal v, l) ->
        [Char (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One))))))] @
          symbolsToKLabelAux l
    | Con (Terminal s, l) -> s @ symbolsToKLabelAux l;;

let rec symbolsToKLabel
  a = OtherLabel
        ([Char (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))] @ symbolsToKLabelAux a);;

let rec getStrictInAttributes
  = function [] -> None
    | b :: l ->
        (match b with Strict a -> Some a | Seqstrict -> getStrictInAttributes l
          | Left -> getStrictInAttributes l | Right -> getStrictInAttributes l
          | Hook _ -> getStrictInAttributes l
          | Function -> getStrictInAttributes l
          | Klabel _ -> getStrictInAttributes l
          | Bracket -> getStrictInAttributes l
          | Tokena -> getStrictInAttributes l | Avoid -> getStrictInAttributes l
          | OnlyLabel -> getStrictInAttributes l
          | NotInRules -> getStrictInAttributes l
          | Regex _ -> getStrictInAttributes l
          | NonAssoc -> getStrictInAttributes l
          | OtherSynAttr _ -> getStrictInAttributes l);;

let rec generatingStrict
  x0 n = match x0, n with [], n -> []
    | b :: l, n -> n :: generatingStrict l (plus_nata n one_nata);;

let rec getStrictList
  sl tyl =
    (match getStrictInAttributes sl with None -> []
      | Some nl -> (if null nl then generatingStrict tyl one_nata else nl));;

let rec getKLabelName = function [] -> None
                        | Klabel a :: l -> Some (OtherLabel a)
                        | Strict v :: l -> getKLabelName l
                        | Seqstrict :: l -> getKLabelName l
                        | Left :: l -> getKLabelName l
                        | Right :: l -> getKLabelName l
                        | Hook v :: l -> getKLabelName l
                        | Function :: l -> getKLabelName l
                        | Bracket :: l -> getKLabelName l
                        | Tokena :: l -> getKLabelName l
                        | Avoid :: l -> getKLabelName l
                        | OnlyLabel :: l -> getKLabelName l
                        | NotInRules :: l -> getKLabelName l
                        | Regex v :: l -> getKLabelName l
                        | NonAssoc :: l -> getKLabelName l
                        | OtherSynAttr v :: l -> getKLabelName l;;

let rec isBracket = function [] -> false
                    | Bracket :: l -> true
                    | Strict v :: l -> isBracket l
                    | Seqstrict :: l -> isBracket l
                    | Left :: l -> isBracket l
                    | Right :: l -> isBracket l
                    | Hook v :: l -> isBracket l
                    | Function :: l -> isBracket l
                    | Klabel v :: l -> isBracket l
                    | Tokena :: l -> isBracket l
                    | Avoid :: l -> isBracket l
                    | OnlyLabel :: l -> isBracket l
                    | NotInRules :: l -> isBracket l
                    | Regex v :: l -> isBracket l
                    | NonAssoc :: l -> isBracket l
                    | OtherSynAttr v :: l -> isBracket l;;

let rec syntaxToKItem
  = function
    Syntax (a, b, c) ->
      (if isBracket c then None
        else (match getKLabelName c
               with None ->
                 (if membera equal_synAttrib c Function
                   then Some [([a], (getArgSortsInSyntax b,
                                      (SingleTon (symbolsToKLabel b),
(getRidStrictAttrs c, true))))]
                   else (if hasOutOfPositionStrict
                              (getStrictList c (getArgSortsInSyntax b))
                              (getArgSortsInSyntax b)
                          then None
                          else Some [([a], (getArgSortsInSyntax b,
     (SingleTon (symbolsToKLabel b), (c, false))))]))
               | Some t ->
                 (if membera equal_synAttrib c Function
                   then Some [([a], (getArgSortsInSyntax b,
                                      (SingleTon t,
(getRidStrictAttrs c, true))))]
                   else (if hasOutOfPositionStrict
                              (getStrictList c (getArgSortsInSyntax b))
                              (getArgSortsInSyntax b)
                          then None
                          else Some [([a], (getArgSortsInSyntax b,
     (SingleTon t, (c, false))))]))))
    | Token (a, s, c) ->
        Some [([a], ([], (SetTon
                            (fun aa ->
                              (match aa with UnitLabel _ -> false
                                | ConstToLabel _ -> false | Sort -> false
                                | GetKLabel -> false | IsKResult -> false
                                | AndBool -> false | NotBool -> false
                                | OrBool -> false | SetConLabel -> false
                                | SetItemLabel -> false | ListConLabel -> false
                                | ListItemLabel -> false | MapConLabel -> false
                                | MapItemLabel -> false | MapUpdate -> false
                                | EqualK -> false | NotEqualK -> false
                                | EqualKLabel -> false | NotEqualKLabel -> false
                                | OtherLabel _ -> false
                                | TokenLabel ab -> regMatch s ab
                                | PlusInt -> false | MinusInt -> false
                                | TimesInt -> false | EqualSet -> false
                                | EqualMap -> false)),
                           (getRidStrictAttrs c,
                             membera equal_synAttrib c Function))))]
    | Subsort (a, b) -> None
    | ListSyntax (a, b, s, c) ->
        (match getKLabelName c
          with None ->
            (if hasOutOfPositionStrict (getStrictList c [[b]; [a]]) [[b]; [a]]
              then None
              else Some [([a], ([[b]; [a]],
                                 (SingleTon
                                    (symbolsToKLabel
                                      (Con
(NonTerminal b, Con (Terminal s, Single (NonTerminal a))))),
                                   (c, false))));
                          ([a], ([], (SingleTon (UnitLabel a),
                                       (getRidStrictAttrs c, false))))])
          | Some t ->
            (if hasOutOfPositionStrict (getStrictList c [[b]; [a]]) [[b]; [a]]
              then None
              else Some [([a], ([[b]; [a]], (SingleTon t, (c, false))));
                          ([a], ([], (SingleTon (UnitLabel a),
                                       (getRidStrictAttrs c, false))))]));;

let rec syntaxSetToKItemSetAux
  x0 order = match x0, order with [], order -> Some []
    | a :: l, order ->
        (match syntaxToKItem a with None -> None
          | Some la ->
            (match syntaxSetToKItemSetAux l (order @ [a]) with None -> None
              | Some laa -> Some (la @ laa)));;

let builtinSymbolTables :
  ('a sort list *
    (('b sort list) list *
      ('c label kItemSyntax * (synAttrib list * bool)))) list
  = [([KLabel], ([[K]], (SingleTon GetKLabel, ([Function], true))));
      ([Bool], ([[K]], (SingleTon IsKResult, ([Function], true))));
      ([Bool], ([[K]; [K]], (SingleTon AndBool, ([Function], true))));
      ([Bool], ([[K]], (SingleTon NotBool, ([Function], true))));
      ([Bool], ([[K]; [K]], (SingleTon OrBool, ([Function], true))));
      ([String], ([[K]], (SingleTon Sort, ([Function], true))));
      ([Map], ([[Map]; [K]; [K]], (SingleTon MapUpdate, ([Function], true))));
      ([Bool], ([[K]; [K]], (SingleTon EqualK, ([Function], true))));
      ([Bool], ([[K]; [K]], (SingleTon NotEqualK, ([Function], true))));
      ([Bool], ([[Map]; [Map]], (SingleTon EqualMap, ([Function], true))));
      ([Bool], ([[Seta]; [Seta]], (SingleTon EqualSet, ([Function], true))));
      ([Bool],
        ([[KLabel]; [KLabel]], (SingleTon EqualKLabel, ([Function], true))));
      ([Bool],
        ([[KLabel]; [KLabel]], (SingleTon NotEqualKLabel, ([Function], true))));
      ([Int], ([[Int]; [Int]], (SingleTon PlusInt, ([Function], true))));
      ([Int], ([[Int]; [Int]], (SingleTon MinusInt, ([Function], true))));
      ([Int], ([[Int]; [Int]], (SingleTon TimesInt, ([Function], true))))];;

let rec isStringConst = function ConstToLabel (StringConst n) -> true
                        | UnitLabel v -> false
                        | ConstToLabel (IntConst va) -> false
                        | ConstToLabel (FloatConst va) -> false
                        | ConstToLabel (BoolConst va) -> false
                        | ConstToLabel (IdConst va) -> false
                        | Sort -> false
                        | GetKLabel -> false
                        | IsKResult -> false
                        | AndBool -> false
                        | NotBool -> false
                        | OrBool -> false
                        | SetConLabel -> false
                        | SetItemLabel -> false
                        | ListConLabel -> false
                        | ListItemLabel -> false
                        | MapConLabel -> false
                        | MapItemLabel -> false
                        | MapUpdate -> false
                        | EqualK -> false
                        | NotEqualK -> false
                        | EqualKLabel -> false
                        | NotEqualKLabel -> false
                        | OtherLabel v -> false
                        | TokenLabel v -> false
                        | PlusInt -> false
                        | MinusInt -> false
                        | TimesInt -> false
                        | EqualSet -> false
                        | EqualMap -> false;;

let rec isFloatConst = function ConstToLabel (FloatConst n) -> true
                       | UnitLabel v -> false
                       | ConstToLabel (IntConst va) -> false
                       | ConstToLabel (StringConst va) -> false
                       | ConstToLabel (BoolConst va) -> false
                       | ConstToLabel (IdConst va) -> false
                       | Sort -> false
                       | GetKLabel -> false
                       | IsKResult -> false
                       | AndBool -> false
                       | NotBool -> false
                       | OrBool -> false
                       | SetConLabel -> false
                       | SetItemLabel -> false
                       | ListConLabel -> false
                       | ListItemLabel -> false
                       | MapConLabel -> false
                       | MapItemLabel -> false
                       | MapUpdate -> false
                       | EqualK -> false
                       | NotEqualK -> false
                       | EqualKLabel -> false
                       | NotEqualKLabel -> false
                       | OtherLabel v -> false
                       | TokenLabel v -> false
                       | PlusInt -> false
                       | MinusInt -> false
                       | TimesInt -> false
                       | EqualSet -> false
                       | EqualMap -> false;;

let rec isBoolConst = function ConstToLabel (BoolConst n) -> true
                      | UnitLabel v -> false
                      | ConstToLabel (IntConst va) -> false
                      | ConstToLabel (FloatConst va) -> false
                      | ConstToLabel (StringConst va) -> false
                      | ConstToLabel (IdConst va) -> false
                      | Sort -> false
                      | GetKLabel -> false
                      | IsKResult -> false
                      | AndBool -> false
                      | NotBool -> false
                      | OrBool -> false
                      | SetConLabel -> false
                      | SetItemLabel -> false
                      | ListConLabel -> false
                      | ListItemLabel -> false
                      | MapConLabel -> false
                      | MapItemLabel -> false
                      | MapUpdate -> false
                      | EqualK -> false
                      | NotEqualK -> false
                      | EqualKLabel -> false
                      | NotEqualKLabel -> false
                      | OtherLabel v -> false
                      | TokenLabel v -> false
                      | PlusInt -> false
                      | MinusInt -> false
                      | TimesInt -> false
                      | EqualSet -> false
                      | EqualMap -> false;;

let rec isIntConst = function ConstToLabel (IntConst n) -> true
                     | UnitLabel v -> false
                     | ConstToLabel (FloatConst va) -> false
                     | ConstToLabel (StringConst va) -> false
                     | ConstToLabel (BoolConst va) -> false
                     | ConstToLabel (IdConst va) -> false
                     | Sort -> false
                     | GetKLabel -> false
                     | IsKResult -> false
                     | AndBool -> false
                     | NotBool -> false
                     | OrBool -> false
                     | SetConLabel -> false
                     | SetItemLabel -> false
                     | ListConLabel -> false
                     | ListItemLabel -> false
                     | MapConLabel -> false
                     | MapItemLabel -> false
                     | MapUpdate -> false
                     | EqualK -> false
                     | NotEqualK -> false
                     | EqualKLabel -> false
                     | NotEqualKLabel -> false
                     | OtherLabel v -> false
                     | TokenLabel v -> false
                     | PlusInt -> false
                     | MinusInt -> false
                     | TimesInt -> false
                     | EqualSet -> false
                     | EqualMap -> false;;

let rec isIdConst = function ConstToLabel (IdConst n) -> true
                    | UnitLabel v -> false
                    | ConstToLabel (IntConst va) -> false
                    | ConstToLabel (FloatConst va) -> false
                    | ConstToLabel (StringConst va) -> false
                    | ConstToLabel (BoolConst va) -> false
                    | Sort -> false
                    | GetKLabel -> false
                    | IsKResult -> false
                    | AndBool -> false
                    | NotBool -> false
                    | OrBool -> false
                    | SetConLabel -> false
                    | SetItemLabel -> false
                    | ListConLabel -> false
                    | ListItemLabel -> false
                    | MapConLabel -> false
                    | MapItemLabel -> false
                    | MapUpdate -> false
                    | EqualK -> false
                    | NotEqualK -> false
                    | EqualKLabel -> false
                    | NotEqualKLabel -> false
                    | OtherLabel v -> false
                    | TokenLabel v -> false
                    | PlusInt -> false
                    | MinusInt -> false
                    | TimesInt -> false
                    | EqualSet -> false
                    | EqualMap -> false;;

let builtinConstTable :
  ('a sort list * ('b list * ('c label kItemSyntax * ('d list * bool)))) list
  = [([Int], ([], (SetTon isIntConst, ([], false))));
      ([Float], ([], (SetTon isFloatConst, ([], false))));
      ([String], ([], (SetTon isStringConst, ([], false))));
      ([Bool], ([], (SetTon isBoolConst, ([], false))));
      ([Id], ([], (SetTon isIdConst, ([], false))))];;

let rec syntaxSetToKItems
  l = (match syntaxSetToKItemSetAux l [] with None -> None
        | Some la -> Some (la @ builtinSymbolTables @ builtinConstTable));;

let rec mergeList = function [] -> []
                    | x :: l -> x @ mergeList l;;

let rec mergeTuples = function [] -> []
                      | (a, b) :: l -> mergeList b @ mergeTuples l;;

let rec collectDatabase
  (Parsed (c, a, b)) = syntaxSetToKItems (removeSubsorts (mergeTuples a));;

let rec tupleToRulePats _A _D _E
  x0 database = match x0, database with [], database -> Some []
    | x :: xl, database ->
        (match tupleToRulePat _A _D _E x database with None -> None
          | Some a ->
            (match a
              with FunPat (l, aa, b) ->
                (match tupleToRulePats _A _D _E xl database with None -> None
                  | Some c -> mergeFunRules _A l aa b c)
              | MacroPat (label, irKList, lista) ->
                (match tupleToRulePats _A _D _E xl database with None -> None
                  | Some xla -> Some (MacroPat (label, irKList, lista) :: xla))
              | AnywherePat (label, irKList, lista, suKItem) ->
                (match tupleToRulePats _A _D _E xl database with None -> None
                  | Some xla ->
                    Some (AnywherePat (label, irKList, lista, suKItem) :: xla))
              | KRulePat (irK, lista, suKItem, boola) ->
                (match tupleToRulePats _A _D _E xl database with None -> None
                  | Some xla ->
                    Some (KRulePat (irK, lista, suKItem, boola) :: xla))
              | BagRulePat (irBag, lista, suKItem, boola) ->
                (match tupleToRulePats _A _D _E xl database with None -> None
                  | Some xla ->
                    Some (BagRulePat (irBag, lista, suKItem, boola) :: xla))));;

let rec getAllSubsortInList _A
  = function [] -> []
    | Subsort (a, b) :: l ->
        inserta (equal_prod (equal_sort _A) (equal_sort _A)) (a, b)
          (getAllSubsortInList _A l)
    | Syntax (v, va, vb) :: l -> getAllSubsortInList _A l
    | Token (v, va, vb) :: l -> getAllSubsortInList _A l
    | ListSyntax (v, va, vb, vc) :: l -> getAllSubsortInList _A l;;

let rec getAllSubsortInListList _A
  = function [] -> []
    | x :: l -> getAllSubsortInList _A x @ getAllSubsortInListList _A l;;

let rec getAllSubsortInTuples _B
  = function [] -> []
    | (a, b) :: l -> getAllSubsortInListList _B b @ getAllSubsortInTuples _B l;;

let rec getAllSubsortInKFile _A
  (Parsed (c, a, b)) = getAllSubsortInTuples _A a;;

let rec addImplicitSubsorts _A
  x s xa2 = match x, s, xa2 with x, s, [] -> []
    | x, s, a :: l ->
        (if membera _A s a then addImplicitSubsorts _A x s l
          else (x, a) :: addImplicitSubsorts _A x s l);;

let builtinSorts : 'a sort list
  = [KItem; K; KList; List; Seta; Bag; Map; KResult; KLabel];;

let rec getKResultSubsorts _A
  x0 subG = match x0, subG with [], subG -> []
    | a :: l, subG ->
        (if membera (equal_sort _A) builtinSorts a
          then getKResultSubsorts _A l subG
          else (if subsortAux (equal_sort _A) KResult a subG
                 then getKResultSubsorts _A l subG
                 else (KResult, a) :: getKResultSubsorts _A l subG));;

let topSubsort : ('a sort * 'b sort) list
  = [(K, Top); (KList, Top); (List, Top); (Seta, Top); (Bag, Top); (Map, Top);
      (KLabel, Top)];;

let rec getAllSorts _A
  = function [] -> []
    | Syntax (x, pros, l) :: xs -> inserta (equal_sort _A) x (getAllSorts _A xs)
    | ListSyntax (a, b, pros, l) :: xs ->
        inserta (equal_sort _A) a (getAllSorts _A xs)
    | Token (a, s, l) :: xs -> inserta (equal_sort _A) a (getAllSorts _A xs)
    | Subsort (v, va) :: xs -> getAllSorts _A xs;;

let rec preAllSubsorts _A
  (Parsed (c, a, b)) =
    getAllSubsortInKFile _A (Parsed (c, a, b)) @
      addImplicitSubsorts (equal_sort _A) KItem builtinSorts
        (getAllSorts _A (mergeTuples a)) @
        [(KResult, KItem); (KItem, K)] @ topSubsort;;

let rec insertAll _A a x1 = match a, x1 with a, [] -> a
                       | a, b :: l -> insertAll _A (inserta _A b a) l;;

let rec preSubsortGraph _A
  (Parsed (c, a, b)) =
    formGraph (equal_sort _A)
      (insertAll (equal_sort _A) (getAllSorts _A (mergeTuples a)) builtinSorts)
      (preAllSubsorts _A (Parsed (c, a, b)));;

let rec kResultSubsorts _A
  (Parsed (c, a, b)) =
    getKResultSubsorts _A (getAllSorts _A (mergeTuples a))
      (preSubsortGraph _A (Parsed (c, a, b)));;

let rec allSubsorts _A
  (Parsed (c, a, b)) =
    getAllSubsortInKFile _A (Parsed (c, a, b)) @
      addImplicitSubsorts (equal_sort _A) KItem builtinSorts
        (getAllSorts _A (mergeTuples a)) @
        [(KResult, KItem); (KItem, K)] @
          topSubsort @ kResultSubsorts _A (Parsed (c, a, b));;

let rec collectSortInRule _A _C
  (x, (y, (z, a))) =
    (match collectSort _A _C x [] with None -> None
      | Some acc ->
        (match collectSort _A _C y acc with None -> None
          | Some aa -> collectSort _A _C z aa));;

let rec assignSortInRule _A _C
  (x, (y, (z, a))) =
    (match collectSortInRule _A _C (x, (y, (z, a))) with None -> None
      | Some acc ->
        (match assignSort _A _C x acc with None -> None
          | Some xa ->
            (match assignSort _A _C y acc with None -> None
              | Some ya ->
                (match assignSort _A _C z acc with None -> None
                  | Some za -> Some (xa, (ya, (za, a)))))));;

let rec formDatabase _A
  = function [] -> []
    | (a, (al, (k, b))) :: l -> insertA _A (formDatabase _A l) a (al, (k, b));;

let rec subsortGraph _A
  (Parsed (c, a, b)) =
    formGraph (equal_sort _A)
      (insertAll (equal_sort _A) (getAllSorts _A (mergeTuples a)) builtinSorts)
      (allSubsorts _A (Parsed (c, a, b)));;

let rec assignSortInRules _A _C
  = function [] -> Some []
    | x :: xl ->
        (match assignSortInRule _A _C x with None -> None
          | Some xa ->
            (match assignSortInRules _A _C xl with None -> None
              | Some xla -> Some (xa :: xla)));;

let rec suToIRInSubsFactor _A
  x0 database = match x0, database with
    KLabelSubs a, database -> suToIRInKLabel _A a database
    | KItemSubs a, database -> suToIRInKItem _A a database
    | KSubs a, database -> suToIRInK _A a database
    | KListSubs a, database ->
        (match suToIRInKList _A a database with None -> None
          | Some aa -> Some (NormalPat (KListMatching aa)))
    | ListSubs a, database -> suToIRInList _A a database
    | SetSubs a, database -> suToIRInSet _A a database
    | MapSubs a, database -> suToIRInMap _A a database
    | BagSubs a, database ->
        (match suToIRInBag _A a database with None -> None
          | Some aa -> Some (NormalPat (BagMatching aa)));;

let rec tupleToRuleInParsed _A _B _C
  a = (let Parsed (_, _, y) = a in
        (match assignSortInRules _A _C y with None -> None
          | Some ya ->
            (match collectDatabase a with None -> None
              | Some aa -> tupleToRulePats _A _B _A ya aa)));;

let rec insertInDatabase _A _B
  x0 a b = match x0, a, b with [], a, b -> []
    | (x, y) :: l, a, b ->
        (if eq _A a x then (x, insertAll _B y b) :: l
          else (x, y) :: insertInDatabase _A _B l a b);;

let rec formSubsortDatabase _A _B
  x0 d = match x0, d with [], d -> d
    | (x, y) :: l, d ->
        (match searchDataBaseByKey _A d y
          with None -> formSubsortDatabase _A _B l d
          | Some vs ->
            formSubsortDatabase _A _B l (insertInDatabase _A _B d x vs));;

let rec preSubsortTerms _A _D _E
  theory database =
    formSubsortDatabase (equal_sort _A)
      (equal_prod (equal_list (equal_sort _A)) (equal_prod _D _E))
      (preAllSubsorts _A theory) (formDatabase (equal_sort _A) database);;

let rec getNonTerminalInList
  = function Single (Terminal a) -> []
    | Single (NonTerminal a) -> [a]
    | Con (Terminal a, l) -> getNonTerminalInList l
    | Con (NonTerminal a, l) -> a :: getNonTerminalInList l;;

end;; (*struct K*)
