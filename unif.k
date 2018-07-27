

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
  syntax Term ::= 'subst(K, Id, Term) [function,klabel('subst)]
  syntax Set ::= 'substInSet(Set, Id, Term) [function,klabel('substInSet)]
  syntax Map ::= 'substMap(Map, Id, Term) [function,klabel('substMap)]


  syntax KItem ::= 'applyDec(TermPair) [function,klabel('applyDec)]
  syntax Set ::= 'decom(Terms, Terms) [function, klabel('decom)]
  syntax List ::= 'applyOneDec(List, Set, K, K, Set) [function, klabel('applyOneDec)]
  syntax Bool ::= 'applyDel(TermPair) [function,klabel('applyDel)]
  syntax List ::= 'applyOneDel(List, Set, K, Set) [function, klabel('applyOneDel)]
  syntax KItem ::= 'toOrient(TermPair) [function, klabel('toOrient)]
  syntax List ::= 'applyOrient(List, Set, K, K, Set) [function, klabel('applyOrient)]

  syntax Bool ::= 'occur(Id, Term)                        [function,klabel('occur)]
  syntax Bool ::= 'occurs(Id, Terms)                      [function,klabel('occurs)]
  syntax KItem ::= 'toEliminate(TermPair, Set, Map)       [function, klabel('toEliminate)]
  syntax List ::= 'applyElim(List, Set, K, K, Set, Map)   [function, klabel('applyElim)]

  syntax Bool ::= 'existOneSet(List, Set) [function, klabel('existOneSet)]
  syntax Bool ::= 'existOneResult(List, K)  [function, klabel('existOneResult)]
  syntax Bool ::= 'singleUnif(K, K, K) [function,klabel('singleUnif)]

  syntax KItem ::= "delete"    [klabel('delete)]
  syntax KItem ::= "orient"    [klabel('orient)]
  syntax KItem ::= "decompose" [klabel('decompose)]
  syntax KItem ::= "eliminate" [klabel('eliminate)]

  configuration <k> PGM:KItem </k>

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

  rule 'toOrient('termPair('const(A:Id, AL:Terms), B:Id))
             => 'some('termPair(B, 'const(A, AL)))
  rule 'toOrient('termPair(A:Term, B:Term)) => 'none(.KList) [owise]

  rule 'applyOrient(L:List, S:Set, .K, .K, .Set) => L
  rule 'applyOrient(L:List, S:Set, .K, .K, SetCon(SetItem(X:K), S1:Set))
                 => 'applyOrient(L, S, .K, X, S1)
  rule 'applyOrient(L:List, S:Set, .K, 'termPair(A:Term, B:Term), S1:Set)
          => 'applyOrient(L:List, S:Set, 'toOrient('termPair(A:Term, B:Term)),
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

  syntax Term ::= 'subst(K, Id, Term) [function,klabel('subst)]
  syntax Set ::= 'substInSet(Set, Id, Term) [function,klabel('substInSet)]
  syntax Map ::= 'substMap(Map, Id, Term) [function,klabel('substMap)]

  rule 'subst('termPair(A:Term, B:Term), X:Id, T:Term)
         => 'termPair('subst(A, X, T), 'subst(B, X, T))
  rule 'subst(X:Id, X, T:Term) => T
  rule 'subst(X:Id, Y:Id, T:Term) => X
       requires '=/=K(X, Y)
  rule 'subst('const(X:Id, Ts:Terms), Y:Id, T:Term)
            => 'const(X, 'subst(Ts, Y, T))
  rule 'subst(.Terms, Y:Id, T:Term) => .Terms
  rule 'subst('listCon(A:Term, B:Terms), Y:Id, T:Term)
          => 'listCon('subst(A, Y, T), 'subst(B, Y, T))

  rule 'substInSet(.Set, X:Id, T:Term) => .Set
  rule 'substInSet(SetCon(SetItem(A:K), S:Set), X:Id, T:Term)
        => SetCon(SetItem('subst(A, X, T)), 'substInSet(S, X, T))

  rule 'substMap(.Map, X:Id, T:Term) => .Map
  rule 'substMap(MapCon(MapItem(Y:Id, A:Term), M:Map), X:Id, T:Term)
          => MapCon(MapItem(Y, 'subst(A, X, T)), 'substMap(M, X, T))
       requires 'notBool('occur(Y, T))
  rule 'substMap(MapCon(MapItem(Y:Id, A:Term), M:Map), X:Id, T:Term)
          => MapCon(MapItem(Y, A), 'substMap(M, X, T))
       requires 'occur(Y, T)

  rule 'toEliminate('termPair(A:Id, B:Term), S:Set, M:Map)
           => 'some('result('substInSet(S, A, B), 'substInSet(M, A, B)))
       requires 'notBool('occur(A, B))
  rule 'toEliminate('termPair(A:Term, B:Term), S:Set, M:Map) => 'none(.KList) [owise]

  rule 'applyElim(L:List, S:Set, .K, .K, .Set, M:Map) => L
  rule 'applyElim(L:List, S:Set, .K, .K, SetCon(SetItem(X:K), S1:Set), M:Map)
                 => 'applyElim(L, S, .K, X, S1, M)
  rule 'applyElim(L:List, S:Set, .K, 'termPair(A:Term, B:Term), S1:Set, M:Map)
          => 'applyElim(L:List, S:Set, 'toEliminate('termPair(A:Term, B:Term), SetCon(S, S1), M),
                       'termPair(A:Term, B:Term), S1:Set, M)
  rule 'applyElim(L:List, S:Set, 'none(.KList), 'termPair(A:Term, B:Term), S1:Set, M:Map)
         => 'applyElim(L, SetCon(S, SetItem('termPair(A:Term, B:Term))), .K, .K, S1, M)
  rule 'applyElim(L:List, S:Set, 'some('result(RS:Set, RM:Map)),
               'termPair(A:Term, B:Term), S1:Set, M:Map)
         => 'applyElim(ListCon(L, ListItem('result(RS:Set, RM:Map))),
                   SetCon(S, SetItem('termPair(A:Term, B:Term))), .K, .K, S1, M)

  rule 'existOneSet(.List, S2:Set) => 'false(.KList)
  rule 'existOneSet(ListCon(ListItem('resultSet(S1:Set)), L:List), S2:Set) => 'true(.KList)
       requires '==Set(S1, S2)
  rule 'existOneSet(ListCon(ListItem('resultSet(S1:Set)), L:List), S2:Set)
              => 'existOneSet(L, S2)
       requires 'notBool('==Set(S1, S2))

  rule 'existOneResult(.List, A:K) => 'false(.KList)
  rule 'existOneResult(ListCon(ListItem('result(S1:Set, M1:Map)), L:List),
               'result(S2:Set, M2:Map)) => 'true(.KList)
       requires 'andBool('==Set(S1, S2), '==Map(M1, M2))
  rule 'existOneResult(ListCon(ListItem('result(S1:Set, M1:Map)), L:List),
           'result(S2:Set, M2:Map)) => 'existOneResult(L, 'result(S2:Set, M2:Map))
       requires 'orBool('notBool('==Set(S1, S2)), 'notBool('==Map(M1, M2)))

  rule 'singleUnif('delete(.KList), 'result(S1:Set, M1:Map), 'result(S2:Set, M2:Map))
           => 'existOneSet('applyOneDel(.List, .Set, .K, S1), S2)
  rule 'singleUnif('decompose(.KList), 'result(S1:Set, M1:Map), 'result(S2:Set, M2:Map))
           => 'existOneSet('applyOneDec(.List, .Set, .K, .K, S1), S2)
  rule 'singleUnif('orient(.KList), 'result(S1:Set, M1:Map), 'result(S2:Set, M2:Map))
           => 'existOneSet('applyOrient(.List, .Set, .K, .K, S1), S2)
  rule 'singleUnif('eliminate(.KList), 'result(S1:Set, M1:Map), 'result(S2:Set, M2:Map))
           => 'existOneResult('applyElim(.List, .Set, .K, S1, M1), 'result(S2, M2))

