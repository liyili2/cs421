

  syntax Id ::= Token{[a-z][a-z A-Z 0-9]*} []
  syntax KItem ::= 'some(K) [klabel('some)]
  syntax KItem ::= "none" [klabel('none)]
  syntax Term ::= Id
  syntax Term ::= 'const(Id, Terms)  [klabel('const)]
  syntax TermPair ::= 'termPair(Term, Term) [klabel('termPair)]

  syntax Terms ::= List{Term,","} [klabel('listCon)]
  syntax TermPair ::= 'termPair(Id, Terms) [klabel('termPair)]
  syntax Int ::= 'termLength(Terms) [function,klabel('termLength)]
  syntax KItem ::= 'resultSet(Set) [klabel('resultSet)]
  syntax KItem ::= 'result(Set, Map)  [klabel('result)]

  syntax KItem ::= 'applyDec(TermPair) [function,klabel('applyDec)]
  syntax Set ::= 'decom(Terms, Terms) [function, klabel('decom)]
  syntax List ::= 'applyOneDec(List, Set, K, K, Set) [function, klabel('applyOneDec)]
  syntax Bool ::= 'applyDel(TermPair) [function,klabel('applyDel)]
  syntax List ::= 'applyOneDel(List, Set, K, Set) [function, klabel('applyOneDel)]
  syntax KItem ::= 'orient(TermPair) [function, klabel('orient)]
  syntax List ::= 'applyOrient(List, Set, K, K, Set) [function, klabel('applyOrient)]

  syntax Bool ::= 'occur(Id, Term) [function,klabel('occur)]
  syntax Bool ::= 'occurs(Id, Terms) [function,klabel('occurs)]


  syntax Term ::= 'subst(K, Id, Term) [function,klabel('subst)]
  syntax Set ::= 'substInSet(Set, Id, Term) [function,klabel('substInSet)]
  syntax Map ::= 'substMap(Map, Id, Term) [function,klabel('substMap)]
  syntax Map ::= 'singleUnif(K, Set, Map) [function,klabel('singleUnif)]
  syntax Set ::= 'singleUnifSet(K, Set, Set, Map) [function,klabel('singleUnifSet)]

  rule 'termLength(.Terms) => '0(.KList)
  rule 'termLength('listCon(A:Term, B:Terms)) => '+Int('termLength(B), '1(.KList))

  rule 'applyDel('termPair(A:Term, A:Term)) => 'true(.KList)
  rule 'applyDel('termPair(A:Term, B:Term)) => 'false(.KList)
       requires '=/=K(A, B)

  rule 'applyOneDel(L:List, S:Set, .K, .Set) => L
  rule 'applyOneDel(L:List, S:Set, .K, SetCon(SetItem(X:K), S1:Set))
                 => 'applyOneDel(L, S, X, S1)
  rule 'applyOneDel(L:List, S:Set, 'termPair(A:Term, A:Term), S1:Set)
          => 'applyOneDel(ListCon(L, ListItem('resultSet(SetCon(S, S1)))),
            SetCon(S, SetItem('termPair(A, A))), .K, S1)
  rule 'applyOneDel(L:List, S:Set, 'termPair(A:Term, B:Term), S1:Set)
          => 'applyOneDel(L, SetCon(S, SetItem('termPair(A, B))), .K, S1)
       requires '=/=K(A, B)

  rule 'decom(.Terms, .Terms) => .Set
  rule 'decom('listCon(A:Term, AL:Terms), 'listCon(B:Term, BL:Terms))
            => SetCon(SetItem('termPair(A, B)), 'decom(AL, BL))

  rule 'applyDec('termPair('const(A:Id, AL:Terms), 'const(A:Id, BL:Terms)))
             => 'some('resultSet('decom(AL, BL)))
       requires '==K('termLength(AL), 'termLength(BL))
  rule 'applyDec('termPair(A:Term, B:Term)) => 'none(.KList) [owise]

  rule 'applyOneDec(L:List, S:Set, .K, .K, .Set) => L
  rule 'applyOneDec(L:List, S:Set, .K, .K, SetCon(SetItem(X:K), S1:Set))
                 => 'applyOneDec(L, S, .K, X, S1)
  rule 'applyOneDec(L:List, S:Set, .K, 'termPair(A:Term, B:Term), S1:Set)
          => 'applyOneDec(L:List, S:Set, 'applyDec('termPair(A:Term, B:Term)),
                       'termPair(A:Term, B:Term), S1:Set)
  rule 'applyOneDec(L:List, S:Set, 'none(.KList), 'termPair(A:Term, B:Term), S1:Set)
          => 'applyOneDec(L, SetCon(S, SetItem('termPair(A:Term, B:Term))), .K, .K, S1)
  rule 'applyOneDec(L:List, S:Set, 'some('resultSet(RS:Set)), 'termPair(A:Term, B:Term), S1:Set)
           => 'applyOneDec(ListCon(L, ListItem('resultSet(SetCon(S, SetCon(RS, S1))))),
                  SetCon(S, SetItem('termPair(A:Term, B:Term))), .K, .K, S1)

  rule 'orient('termPair('const(A:Id, AL:Terms), B:Id))
             => 'some('termPair(B, 'const(A, AL)))
  rule 'orient('termPair(A:Term, B:Term)) => 'none(.KList) [owise]

  rule 'applyOrient(L:List, S:Set, .K, .K, .Set) => L
  rule 'applyOrient(L:List, S:Set, .K, .K, SetCon(SetItem(X:K), S1:Set))
                 => 'applyOrient(L, S, .K, X, S1)
  rule 'applyOrient(L:List, S:Set, .K, 'termPair(A:Term, B:Term), S1:Set)
          => 'applyOrient(L:List, S:Set, 'orient('termPair(A:Term, B:Term)),
                       'termPair(A:Term, B:Term), S1:Set)
  rule 'applyOrient(L:List, S:Set, 'none(.KList), 'termPair(A:Term, B:Term), S1:Set)
              => 'applyOrient(L, SetCon(S, SetItem('termPair(A:Term, B:Term))), .K, .K, S1)
  rule 'applyOrient(L:List, S:Set, 'some(X:K),
                       'termPair(A:Term, B:Term), S1:Set)
              => 'applyOrient(ListCon(L, ListItem('resultSet(SetCon(S, SetCon(SetItem(X), S1))))),
                      SetCon(S, SetItem('termPair(A:Term, B:Term))), .K, .K, S1)

  rule 'occur(X:Id, X:Id) => 'true(.KList)
  rule 'occur(X:Id, Y:Id) => 'false(.KList)
       requires '=/=K(X, Y)
  rule 'occur(X:Id, 'const(A:Id, T:Terms))
            => 'occurs(X, T)
  rule 'occurs(X:Id, .Terms) => 'false(.KList)
  rule 'occurs(X:Id, 'listCon(T:Term, Ts:Terms))
          => 'orBool('occur(X, T), 'occurs(X, Ts))



