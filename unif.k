
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

  syntax Bool ::= 'subset(Set, Set)   [function, klabel('subset)]
  syntax Set ::= 'minusSet(Set, Set)  [function, klabel('minusSet)]
  syntax KItem ::= "succecss" [klabel('success)]
  syntax KItem ::= 'error(String) [klabel('error)]

  syntax KItem ::= 'checkOneDel(Set, Set) [function, klabel('checkOneDel)]
  syntax KItem ::= 'checkOneDec(Set, Set) [function, klabel('checkOneDec)]
  syntax KItem ::= 'checkOneDecAux(Set, Set) [function, klabel('checkOneDecAux)]
  syntax KItem ::= 'checkOrient(Set, Set) [function, klabel('checkOrient)]
  syntax KItem ::= 'checkElim(Set, Map, Set, Map) [function, klabel('checkElim)]
  syntax KItem ::= 'checkElimAux(K, Set, Map) [function, klabel('checkElimAux)]

  syntax Set ::= 'decom(Terms, Terms) [function, klabel('decom)]

  syntax Bool ::= 'occur(Id, Term)                        [function,klabel('occur)]
  syntax Bool ::= 'occurs(Id, Terms)                      [function,klabel('occurs)]
  syntax KItem ::= 'toEliminate(TermPair, Set, Map)       [function, klabel('toEliminate)]

  syntax Bool ::= 'singleUnif(K, K, K) [function,klabel('singleUnif)]

  syntax KItem ::= "delete"    [klabel('delete)]
  syntax KItem ::= "orient"    [klabel('orient)]
  syntax KItem ::= "decompose" [klabel('decompose)]
  syntax KItem ::= "eliminate" [klabel('eliminate)]

  configuration <k> PGM:KItem </k>

  rule 'termLength(.Terms) => '0(.KList)
  rule 'termLength('listCon(A:Term, B:Terms)) => '+Int('termLength(B), '1(.KList))

  rule 'subset(.Set, S:Set) => 'true(.KList)
  rule 'subset(SetCon(SetItem(A:K), S:Set), SetCon(SetItem(A:K), S':Set))
          => 'subset(S, S')
  rule 'subset(SetCon(SetItem(A:K), S:Set), S':Set) => 'false(.KList)  [owise]

  rule 'minusSet(S:Set, .Set) => S
  rule 'minusSet(SetCon(SetItem(A:K), S:Set), SetCon(SetItem(A:K), S':Set))
            => 'minusSet(S, S')
  rule 'minusSet(S:Set, SetCon(SetItem(B:K), S':Set))
            => 'minusSet(S, S') [owise]

  rule 'checkOneDel(SetCon(SetItem('termPair(A:Term, A:Term)),
                  S:Set), S:Set) => 'success(.KList)
  rule 'checkOneDel(SetCon(SetItem('termPair(A:Term, B:Term)),
                  S:Set), S:Set) => 'error("The two terms are not equal so that they cannot be deleted.")
       requires '=/=K(A, B)
  rule 'checkOneDel(S:Set, S':Set) => 'error("Syntactic error: might have mis-written the output terms, or apply the wrong rule.")
       [owise]

  rule 'decom(.Terms, .Terms) => .Set
  rule 'decom('listCon(A:Term, AL:Terms), 'listCon(B:Term, BL:Terms))
            => SetCon(SetItem('termPair(A, B)), 'decom(AL, BL))

  rule 'checkOneDec(SetCon(SetItem('termPair(A:Term, B:Term)), S1:Set), S:Set)
         => 'checkOneDecAux(S1, 'minusSet(S, 'decom(A, B)))
       requires 'subset('decom(A, B), S)
  rule 'checkOneDec(SetCon(SetItem('termPair(A:Term, B:Term)), S1:Set), S:Set)
         => 'error("The decomposition rule is not applied properly.")  [owise]

  rule 'checkOneDecAux(S:Set, S:Set) => 'success(.KList)
  rule 'checkOneDecAux(S:Set, S':Set) => 'error("Syntactic error: might have mis-written the output terms, or apply the wrong rule.") [owise]

  rule 'checkOrient(SetCon(SetItem('termPair('const(A:Id, AL:Terms),
           B:Id)), S:Set), SetCon(SetItem('termPair(B, 'const(A:Id, AL:Terms))),
              S:Set)) => 'success(.KList)
  rule 'checkOrient(SetCon(SetItem('termPair('const(A:Id, AL:Terms),
           B:Id)), S:Set), SetCon(SetItem('termPair(X:Term, Y:Term)),
              S:Set)) => 'error("Does not apply orient rule correctly.")
       requires 'andBool('=/=K(X, B), '=/=K(Y, 'const(A:Id, AL:Terms)))
  rule 'checkOrient(SetCon(SetItem('termPair('const(A:Id, AL:Terms),
           B:Id)), S:Set), S':Set)
         => 'error("Syntactic error: might have mis-written the output terms, or apply the wrong rule.")
       [owise]

  rule 'occur(X:Id, X:Id) => 'true(.KList)
  rule 'occur(X:Id, Y:Id) => 'false(.KList)
       requires '=/=K(X, Y)
  rule 'occur(X:Id, 'const(A:Id, T:Terms))
            => 'occurs(X, T)
  rule 'occurs(X:Id, .Terms) => 'false(.KList)
  rule 'occurs(X:Id, 'listCon(T:Term, Ts:Terms))
          => 'orBool('occur(X, T), 'occurs(X, Ts))

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
           => 'result('substInSet(S, A, B), 'substMap(M, A, B))

  rule 'checkElim(SetCon(SetItem('termPair(A:Id, B:Term)), S:Set),
                 M:Map, S':Set, M':Map)
              => 'checkElimAux('toEliminate('termPair(A:Id, B:Term), S, M), S', M')
        requires 'notBool('occur(A, B))
  rule 'checkElim(S:Set, M:Map, S':Set, M':Map)
             => 'error("There is no term that can be applied with the elimination rule.")
        [owise]

  rule 'checkElimAux('result(S:Set, M:Map), S:Set, M:Map) => 'success(.KList)
  rule 'checkElimAux('result(S:Set, M:Map), S':Set, M':Map)
          => 'error("The result is not a correct application result of the elimination rule.") [owise]

  rule 'singleUnif('delete(.KList), 'result(S1:Set, M1:Map), 'result(S2:Set, M2:Map))
           => 'checkOneDel(S1, S2)
  rule 'singleUnif('decompose(.KList), 'result(S1:Set, M1:Map), 'result(S2:Set, M2:Map))
           => 'checkOneDec(S1, S2)
  rule 'singleUnif('orient(.KList), 'result(S1:Set, M1:Map), 'result(S2:Set, M2:Map))
           => 'checkOrient(S1, S2)
  rule 'singleUnif('eliminate(.KList), 'result(S1:Set, M1:Map), 'result(S2:Set, M2:Map))
           => 'checkElim(S1, M1, S2, M2)

program 'occur($y(.KList), 'const($f(.KList), 'listCon($h(.KList), 'listCon($x(.KList), .Terms))))
