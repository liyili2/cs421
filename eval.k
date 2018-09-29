
  syntax KItem ::= 'some(K) [klabel('some)]
  syntax KItem ::= "none" [klabel('none)]
  syntax KItem ::= 'result(Map) [klabel('result)]
  syntax KItem ::= 'continue(Map) [klabel('continue)]
  syntax KItem ::= "succecss" [klabel('success)]
  syntax KItem ::= 'error(String) [klabel('error)]

  syntax Term ::= Id
  syntax Term ::= Int
  syntax Term ::= 'plus(Term, Term) [klabel('plus)]
  syntax Term ::= 'minus(Term, Term) [klabel('minus)]
  syntax Term ::= 'times(Term, Term) [klabel('times)]
  syntax Term ::= 'app(Term, Term) [klabel('app)]
  syntax Term ::= 'fun(Id, Term) [klabel('fun)]
  syntax Term ::= 'letIn(Ids, Term, Term) [klabel('letIn)]
  syntax Term ::= 'let(Ids, Term) [klabel('let)]

  syntax Terms ::= List{Term, ","} [klabel('con)]
  syntax Ids ::= List{Id, ","} [klabel('idCon)]

  syntax Term ::= 'innerLet(Id, Term) [klabel('innerLet)]
  syntax Term ::= 'innerLetIn(Id, Term, Term) [klabel('innerLetIn)]
  syntax Term ::= 'termMarker(Term, Int) [klabel('termMarker)]
  syntax Term ::= 'marker(Int)  [klabel('marker)]

  syntax KResult ::= Int
                   | 'closure(Id, Term, Map) [klabel('closure)]

  configuration <k> PGM:KItem </k>

  syntax KItem ::= 'lookup(Map, K) [function, klabel('lookup)]
  rule 'lookup(.Map, A:K) => 'none(.KList)
  rule 'lookup(MapCon(MapItem(A:K, V:K), M:Map), A:K) => 'some(V)
  rule 'lookup(MapCon(MapItem(A':K, V:K), M:Map), A:K)
          => 'lookup(M, A)
       requires '=/=K(A, A')

  syntax Term ::= 'formFunTerm(Ids, Term) [function, klabel('formFunTerm)]
  syntax Term ::= 'toInnerLet(Term) [function, klabel('toInnerLet)]
  syntax Terms ::= 'toInnerLets(Terms) [function, klabel('toInnerLets)]

  rule 'formFunTerm(.Ids, T:Term) => T
  rule 'formFunTerm('idCon(A:Id, B:Ids), T:Term)
         => 'fun(A, 'formFunTerm(B, T))

  rule 'toInnerLet('let('idCon(F:Id, B:Ids), T:Term))
            => 'innerLet(F, 'formFunTerm(B, 'toInnerLet(T)))
  rule 'toInnerLet('letIn('idCon(F:Id, B:Ids), T1:Term, T2:Term))
          => 'innerLetIn(F, 'formFunTerm(B, 'toInnerLet(T1)), 'toInnerLet(T2))
  rule 'toInnerLet(A:Term) => A [owise] 

  rule 'toInnerLets(.Terms) => .Terms
  rule 'toInnerLets('con(T:Term, Ts:Terms)) => 'con('toInnerLet(T), 'toInnerLets(Ts))

  syntax Term ::= 'removeMarker(Term) [function, klabel('removeMarker)]
  rule 'removeMarker(I:Int) => I
  rule 'removeMarker(A:Id) => A
  rule 'removeMarker('plus(A:Term, B:Term))
         => 'plus('removeMarker(A), 'removeMarker(B))
  rule 'removeMarker('minus(A:Term, B:Term))
         => 'minus('removeMarker(A), 'removeMarker(B))
  rule 'removeMarker('times(A:Term, B:Term))
         => 'times('removeMarker(A), 'removeMarker(B))
  rule 'removeMarker('fun(A:Id, B:Term))
         => 'fun(A, 'removeMarker(B))
  rule 'removeMarker('app(A:Term, B:Term))
         => 'app('removeMarker(A), 'removeMarker(B))
  rule 'removeMarker('innerLet(A:Id, B:Term))
         => 'innerLet(A, 'removeMarker(B))
  rule 'removeMarker('let(A:Ids, B:Term))
         => 'let(A, 'removeMarker(B))
  rule 'removeMarker('innerLetIn(A:Id, B:Term, C:Term))
         => 'innerLetIn(A, 'removeMarker(B), 'removeMarker(C))
  rule 'removeMarker('letIn(A:Ids, B:Term, C:Term))
         => 'letIn(A, 'removeMarker(B), 'removeMarker(C))
  rule 'removeMarker('termMarker(T:Term, A:Int)) => 'removeMarker(T)

  syntax KItem ::= 'eval(Term, Map) [function, klabel('eval)]
  syntax KItem ::= 'evalPlus(K, K)  [function, klabel('evalPlus)]
  syntax KItem ::= 'evalMinus(K, K)  [function, klabel('evalMinus)]
  syntax KItem ::= 'evalTimes(K, K)  [function, klabel('evalTimes)]
  syntax KItem ::= 'evalApp(K, K) [function, klabel('evalApp)]
  syntax KItem ::= 'evalLet(Id, K, Map) [function, klabel('evalLet)]
  syntax KItem ::= 'evalLetIn(Id, K, Term, Map) [function, klabel('evalLetIn)]

  rule 'eval(I:Int, M:Map) => 'some(I)
  rule 'eval(A:Id, M:Map) => 'lookup(M, A)
  rule 'eval('plus(A:K, B:K), M:Map)
          => 'evalPlus('eval(A,M), 'eval(B,M))
  rule 'eval('minus(A:K, B:K), M:Map)
          => 'evalMinus('eval(A,M), 'eval(B,M))
  rule 'eval('times(A:K, B:K), M:Map)
          => 'evalTimes('eval(A,M), 'eval(B,M))
  rule 'eval('fun(A:Id, T:Term), M:Map)
            => 'some('closure(A, 'removeMarker(T), M))
  rule 'eval('app(T1:Term, T2:Term), M:Map)
            => 'evalApp('eval(T1, M), 'eval(T2, M))
  rule 'eval('let(X:Ids, T:Term), M:Map)
         => 'eval('toInnerLet('let(X, T)), M)
  rule 'eval('letIn(X:Ids, T1:Term, T2:Term), M:Map)
         => 'eval('toInnerLet('letIn(X, T1, T2)), M)
  rule 'eval('innerLet(X:Id, T:Term), M:Map)
          => 'evalLet(X, 'eval(T, M), M)
  rule 'eval('innerLetIn(X:Id, T:Term, T1:Term), M:Map)
         => 'evalLetIn(X, 'eval(T, M), T1, M)
  rule 'eval('termMarker(T:Term, I:Int), M:Map)
            => 'some('result(MapItem(I, 'result(M))))

  rule 'evalPlus('some(A:Int), 'some(B:Int)) => 'some('+Int(A, B))
  rule 'evalPlus('some('result(M:Map)), B:K) => 'some('result(M))
  rule 'evalPlus(B:K, 'some('result(M:Map))) => 'some('result(M))
  rule 'evalPlus(A:K, B:K) => 'none(.KList) [owise]
  rule 'evalMinus('some(A:Int), 'some(B:Int)) => 'some('-Int(A, B))
  rule 'evalMinus('some('result(M:Map)), B:K) => 'some('result(M))
  rule 'evalMinus(B:K, 'some('result(M:Map))) => 'some('result(M))
  rule 'evalMinus(A:K, B:K) => 'none(.KList) [owise]
  rule 'evalTimes('some(A:Int), 'some(B:Int)) => 'some('*Int(A, B))
  rule 'evalTimes('some('result(M:Map)), B:K) => 'some('result(M))
  rule 'evalTimes(B:K, 'some('result(M:Map))) => 'some('result(M))
  rule 'evalTimes(A:K, B:K) => 'none(.KList) [owise]

  rule 'evalApp('some('closure(X:Id, T:Term, M1:Map)), 'some(V:KResult))
          => 'eval(T, 'mapUpdate(M1, X, V))
  rule 'evalApp('some('result(M:Map)), B:K) => 'some('result(M))
  rule 'evalApp(B:K, 'some('result(M:Map))) => 'some('result(M))
  rule 'evalApp(A:K, B:K) => 'none(.KList) [owise]

  rule 'evalLet(X:Id, 'some(A:KResult), M:Map)
                     => 'some('continue('mapUpdate(M, X, A)))
  rule 'evalLet(X:Id, 'some('result(M:Map)), M1:Map) => 'some('result(M))
  rule 'evalLet(X:Id, B:K, M:Map) => 'none(.KList) [owise]

  rule 'evalLetIn(X:Id, 'some(A:KResult), T:Term, M:Map)
         => 'eval(T, 'mapUpdate(M, X, A))
  rule 'evalLetIn(X:Id, 'some('result(M:Map)), T:Term, M1:Map)
         => 'some('result(M:Map))
  rule 'evalLetIn(X:Id, A:K, T:Term, M:Map) => 'none(.KList) [owise]

  syntax Map ::= 'evalTerms(Terms, Map)        [function, klabel('evalTerms)]
               | 'evalTermsAux(Terms, K, Map)  [function, klabel('evalTermsAux)]
  rule 'evalTerms(.Terms, M:Map) => .Map
  rule 'evalTerms('con('marker(I:Int), Ts:Terms), M:Map)
             => MapItem(I, 'result(M))
  rule 'evalTerms('con(T:Term, Ts:Terms), M:Map)
         => 'evalTermsAux(Ts, 'eval(T, M), M:Map) [owise]
  rule 'evalTermsAux(Ts:Terms, 'some('result(M:Map)), M1:Map) => M
  rule 'evalTermsAux(Ts:Terms, 'some('continue(M:Map)), M1:Map)
            => 'evalTerms(Ts, M)
  rule 'evalTermsAux(Ts:Terms, 'some(A:KResult), M1:Map) => 'evalTerms(Ts, M1)
  rule 'evalTermsAux(Ts:Terms, A:K, M:Map) => .Map [owise]

  syntax Bool ::= 'subMap(Map, Map)   [function, klabel('subMap)]
  rule 'subMap(.Map, S:Map) => 'true(.KList)
  rule 'subMap(MapCon(MapItem(A:K, B:K), S:Map), MapCon(MapItem(A:K, B:K), S':Map))
          => 'subMap(S, S')
  rule 'subMap(MapCon(MapItem(A:K, B:K), S:Map), S':Map)
                 => 'false(.KList)  [owise]

  syntax Map ::= 'minusMap(Map, Map)  [function, klabel('minusMap)]
  rule 'minusMap(S:Map, .Map) => S
  rule 'minusMap(MapCon(MapItem(A:K, B:K), S:Map), MapCon(MapItem(A:K, B:K), S':Map))
            => 'minusMap(S, S')
  rule 'minusMap(S:Map, MapCon(MapItem(A:K, B:K), S':Map))
            => 'minusMap(S, S') [owise]

  syntax Bool ::= 'isAKey(K, Map) [function, klabel('isAKey)]
  rule 'isAKey(A:K, MapCon(MapItem(A:K, B:K), M:Map))
          => 'true(.KList)
  rule 'isAKey(A:K, M:Map) => 'false(.KList) [owise]


  syntax KItem ::= 'judgeEval(Terms, Map, Map, Map, Int) [function, klabel('judgeEval)]
                 | 'judgeEvalAux(K, Map, Map) [function, klabel('judgeEvalAux)]
                 | 'findError(Map, Map) [function, klabel('findError)]

  rule 'judgeEval(Ts:Terms, Pre:Map, Point:Map, An:Map, I:Int)
          => 'judgeEvalAux('lookup('evalTerms(Ts, Pre), I), Point, An)
  rule 'judgeEvalAux('some('result(M:Map)), Point:Map, M:Map)
             => 'success(.KList)
  rule 'judgeEvalAux('some('result(M:Map)), Point:Map, M':Map)
             => 'findError('minusMap(M, Point), 'minusMap(M', Point))
       requires 'notBool('==Map(M, M'))
  rule 'judgeEvalAux(A:K, Point:Map, B:Map)
              => 'error("unknown error, maybe syntactic error.") [owise]

  rule 'findError(MapCon(MapItem(A:K, C:Int), M:Map), MapCon(MapItem(A:K, D:Int), M':Map))
            => 'error("An integer value of an environment key is calculated wrong.")
       requires '=/=K(C, D)
  rule 'findError(MapCon(MapItem(A:K, 'closure(X:Id, T:Term, M1:Map)), M:Map),
                 MapCon(MapItem(A:K, 'closure(X':Id, T':Term, M1':Map)), M':Map))
            => 'error("The closure has the wrong function name for an environment key.")
       requires '=/=K(X, X')
  rule 'findError(MapCon(MapItem(A:K, 'closure(X:Id, T:Term, M1:Map)), M:Map),
                 MapCon(MapItem(A:K, 'closure(X:Id, T':Term, M1':Map)), M':Map))
            => 'error("User mis-calculated the function body for the closure for an environment key.")
       requires '=/=K(T, T')
  rule 'findError(MapCon(MapItem(A:K, 'closure(X:Id, T:Term, M1:Map)), M:Map),
                 MapCon(MapItem(A:K, 'closure(X:Id, T:Term, M1':Map)), M':Map))
            => 'error("User mis-calculated the environment associated with a closure.")
       requires 'notBool('==Map(M1, M1'))
  rule 'findError(MapCon(MapItem(A:K, B:K), M:Map), M':Map)
            => 'error("User misses a key in the environment.")
       requires 'notBool('isAKey(A, M'))
  rule 'findError(M:Map, M':Map) => 'error("Unknown error") [owise]

  syntax Terms ::= 'getRidFirstMarker(Terms) [function]
                 | 'getRidFirstAux(Term, Term, Terms) [function]
  rule 'getRidFirstMarker(.Terms) => .Terms
  rule 'getRidFirstMarker('con('marker(A:Int), Ts:Terms)) => Ts
  rule 'getRidFirstMarker('con(T:Term, Ts:Terms))
              => 'getRidFirstAux(T, 'removeMarker(T), Ts) [owise]
  rule 'getRidFirstAux(T:Term, T, Ts:Terms)
       => 'con(T, 'getRidFirstMarker(Ts))
  rule 'getRidFirstAux(T:Term, T':Term, Ts:Terms)
            => 'con(T', Ts)  [owise]

  syntax KItem ::= 'judgeAllEvalAux(Terms, Map, Map, Int, Int)  [function]
                 | 'judgeAllEvalNext(Terms, K, K, Map, Int, Int) [function]
                 | 'judgeAllEvals(Terms, Map, Int) [function]
  rule 'judgeAllEvalAux(Ts:Terms, MapCon(MapItem(I, 'result(M:Map)), RM:Map),
                    Point:Map, I:Int, N:Int) 
            => 'judgeAllEvalNext(Ts, 'judgeEval(Ts, .Map, Point, M, I),
                        'lookup('evalTerms(Ts, .Map), I), RM, I, N)
        requires '<=Int(I, N)
  rule 'judgeAllEvalAux(Ts:Terms, M:Map, Point:Map, I:Int, N:Int) => 'success(.KList)
        requires '<Int(N, I)
  rule 'judgeAllEvalNext(Ts:Terms, 'success(.KList), 'some('result(M:Map)), RM:Map, I:Int, N:Int)
            => 'judgeAllEvalAux('getRidFirstMarker(Ts), RM, M, '+Int(I, '1(.KList)), N)
  rule 'judgeAllEvalNext(Ts:Terms, 'error(S:String), R:K, RM:Map, I:Int, N:Int)
         => 'error('+String("Error at point ", '+String('intToString(I), S)))

  rule 'judgeAllEvals(Ts:Terms, M:Map, N:Int) => 'judgeAllEvalAux(Ts, M, .Map, '1(.KList), N)
       requires 'isAKey('1(.KList), M)
  rule 'judgeAllEvals(Ts:Terms, M:Map, N:Int) => 'error("Unknown errors.") [owise]

program 'judgeAllEvals('con('let('idCon($x(.KList), .Ids), '5(.KList)),
               'con('let('idCon($a(.KList), .Ids), 'plus($x(.KList), '4(.KList))),
              'con('marker('1(.KList)),
            'con('let('idCon($f(.KList), 'idCon($x(.KList), 'idCon($y(.KList), .Ids))),
                  'plus($x(.KList), 'plus($y(.KList), $a(.KList)))),
            'con('marker('2(.KList)),
         'con('let('idCon($h(.KList), 'idCon($z(.KList), .Ids)),
                  'app($f(.KList), 'plus($z(.KList), '4(.KList)))),
           'con('marker('3(.KList)),
         'con('let('idCon($a(.KList), .Ids),
               'letIn('idCon($h(.KList), 'idCon($x(.KList), .Ids)),
               'app('app($f(.KList),$a(.KList)), 'app('app($h(.KList), '3(.KList)),$x(.KList))),
                    'termMarker('app($h(.KList), 'times('2(.KList), $x(.KList))), '4(.KList)))),
          'con('marker('5(.KList)), .Terms))))))))),
         MapCon(MapItem('1(.KList),
           'result(MapCon(MapItem($x(.KList), '3(.KList)), MapItem($a(.KList), '9(.KList))))),
       MapCon(MapItem('2(.KList),
         'result(MapCon(MapItem($x(.KList), '5(.KList)), MapCon(MapItem($a(.KList), '9(.KList)),
           MapItem($f(.KList), 'closure($x(.KList), 'fun($y(.KList),
                    'plus($x(.KList), 'plus($y(.KList), $a(.KList)))),
                MapCon(MapItem($x(.KList), '5(.KList)), MapItem($a(.KList), '9(.KList))))))))),
    MapCon(MapItem('3(.KList),
         'result(MapCon(MapItem($h(.KList), 'closure($z(.KList), 
                    'app($f(.KList), 'plus($z(.KList), '4(.KList))),
              MapCon(MapItem($f(.KList), 'closure($x(.KList), 'fun($y(.KList),
                    'plus($x(.KList), 'plus($y(.KList), $a(.KList)))),
                MapCon(MapItem($x(.KList), '5(.KList)), MapItem($a(.KList), '9(.KList))))),
          MapCon(MapItem($x(.KList), '5(.KList)), MapItem($a(.KList), '9(.KList)))))),
         MapCon(MapItem($x(.KList), '5(.KList)), MapCon(MapItem($a(.KList), '9(.KList)),
           MapItem($f(.KList), 'closure($x(.KList), 'fun($y(.KList),
                    'plus($x(.KList), 'plus($y(.KList), $a(.KList)))),
                MapCon(MapItem($x(.KList), '5(.KList)), MapItem($a(.KList), '9(.KList)))))))))),
       MapCon(MapItem('4(.KList),
          'result(MapCon(MapItem($h(.KList), 'closure($x(.KList), 
            'app('app($f(.KList),$a(.KList)), 'app('app($h(.KList), '3(.KList)),$x(.KList))),
              MapCon(MapItem($h(.KList), 'closure($z(.KList), 
                    'app($f(.KList), 'plus($z(.KList), '4(.KList))),
              MapCon(MapItem($f(.KList), 'closure($x(.KList), 'fun($y(.KList),
                    'plus($x(.KList), 'plus($y(.KList), $a(.KList)))),
                MapCon(MapItem($x(.KList), '5(.KList)), MapItem($a(.KList), '9(.KList))))),
          MapCon(MapItem($x(.KList), '5(.KList)), MapItem($a(.KList), '9(.KList)))))),
         MapCon(MapItem($x(.KList), '5(.KList)), MapCon(MapItem($a(.KList), '9(.KList)),
           MapItem($f(.KList), 'closure($x(.KList), 'fun($y(.KList),
                    'plus($x(.KList), 'plus($y(.KList), $a(.KList)))),
                MapCon(MapItem($x(.KList), '5(.KList)), MapItem($a(.KList), '9(.KList)))))))))),
         MapCon(MapItem($x(.KList), '5(.KList)), MapCon(MapItem($a(.KList), '9(.KList)),
           MapItem($f(.KList), 'closure($x(.KList), 'fun($y(.KList),
                    'plus($x(.KList), 'plus($y(.KList), $a(.KList)))),
                MapCon(MapItem($x(.KList), '5(.KList)), MapItem($a(.KList), '9(.KList)))))))))),
        MapItem('5(.KList),
          'result(MapCon(MapItem($h(.KList), 'closure($z(.KList), 
                    'app($f(.KList), 'plus($z(.KList), '4(.KList))),
              MapCon(MapItem($f(.KList), 'closure($x(.KList), 'fun($y(.KList),
                    'plus($x(.KList), 'plus($y(.KList), $a(.KList)))),
                MapCon(MapItem($x(.KList), '5(.KList)), MapItem($a(.KList), '9(.KList))))),
          MapCon(MapItem($x(.KList), '5(.KList)), MapItem($a(.KList), '9(.KList)))))),
         MapCon(MapItem($x(.KList), '5(.KList)), MapCon(MapItem($a(.KList), '44(.KList)),
           MapItem($f(.KList), 'closure($x(.KList), 'fun($y(.KList),
                    'plus($x(.KList), 'plus($y(.KList), $a(.KList)))),
                MapCon(MapItem($x(.KList), '5(.KList)), MapItem($a(.KList), '9(.KList))))))))))
          )))), '5(.KList))


