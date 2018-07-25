

  syntax Id ::= Token{[a-z][a-z A-Z 0-9]*} []
  syntax Term ::= Id
  syntax Term ::= 'const(Id, Terms)  [klabel('const)]  
  syntax Terms ::= List{Term,","} [klabel('listCon)]
  syntax TermPair ::= 'termPair(Id, Terms) [klabel('termPair)]
  syntax KItem ::= 'result(Set, Map)  [klabel('result)]
  syntax Int ::= 'termLength(Terms) [function,klabel('termLength)]
  syntax Bool ::= 'occur(K, Term) [function,klabel('occur)]
  syntax Bool ::= 'occurs(K, Terms) [function,klabel('occurs)]
  syntax Term ::= 'subst(K, Id, Term) [function,klabel('subst)]
  syntax Set ::= 'substInSet(Set, Id, Term) [function,klabel('substInSet)]
  syntax Map ::= 'substMap(Map, Id, Term) [function,klabel('substMap)]
  syntax Set ::= 'decompose(Terms, Terms) [function,klabel('decompose)]
  syntax Map ::= 'singleUnif(K, Set, Map) [function,klabel('singleUnif)]
  syntax Set ::= 'singleUnifSet(K, Set, Set, Map) [function,klabel('singleUnifSet)]

  rule 'termLength(.Terms) => '0(.KList)
  rule 'termLength('listCon(A:Term, B:Terms)) => '+Int('termLength(B), '1(.KList))

  rule 'decompose(.Terms, .Terms) => .Set
