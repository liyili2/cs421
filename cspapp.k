
  syntax KItem ::= 'some(K) [klabel('some)]
  syntax KItem ::= "none" [klabel('none)]
  syntax KItem ::= "succecss" [klabel('success)]
  syntax KItem ::= 'error(String) [klabel('error)]

  syntax Op ::= "+" [klabel('plus)]
              | "-" [klabel('minus)]
              | "*" [klabel('times)]
              | "<" [klabel('lt)]
              | "<=" [klabel('leq)]
              | ">"  [klabel('gt)]
              | ">=" [klabel('geq)]

  syntax Input ::= Id | Int | Float
                 | 'ifelse(Input, Input, Input)  [klabel('ifelse)]
                 | 'app(Input, Input) [klabel('app)]
                 | 'bin(Op, Input, Input)  [klabel('bin)]
                 | 'unary(Op, Input) [klabel('unary)]
                 | 'fun(Id, Input)   [klabel('fun)]
                 | 'let(Id, Input, Input) [klabel('let)]

  syntax Exp ::= Id | Int | Float
               | 'cpsapp(Exp, Exp) [klabel('cpsapp)]
               | 'cpsbin(Op, Exp, Exp) [klabel('cpsbin)]
               | 'cpsunary(Op, Exp) [klabel('cpsunary)]
               | 'cpsfun(Id, Exp) [klabel('cpsfun)]
               | 'continue(Id, Exp) [klabel('continue)]
 

  syntax Exp ::= 'eval(Exp, Map)  [klabel('eval)]
  syntax Exp ::= "undef" [klabel('undef)]

  syntax KItem ::= 'lookup(Map, K) [function, klabel('lookup)]
  rule 'lookup(.Map, A:K) => 'none(.KList)
  rule 'lookup(MapCon(MapItem(A:K, V:K), M:Map), A:K) => 'some(V)
  rule 'lookup(MapCon(MapItem(A':K, V:K), M:Map), A:K)
          => 'lookup(M, A)
       requires '=/=K(A, A')

  syntax Bool ::= 'equalExp(K, K) [function, klabel('equalExp)]
  rule 'equalExp('eval(A:K, B:Map), 'eval(C:K, D:Map))
            => 'andBool('==K(A, C), '==Map(B, D))
  rule 'equalExp(A:K, B:K) => '==K(A, B) [owise]

  syntax KItem ::= 'dealWith(K) [function, klabel('dealWith)]
  rule 'dealWith('none(.KList)) => 'undef(.KList)
  rule 'dealWith('some(A:KItem)) => A

  syntax KItem ::= 'patMatch(K, Pats) [function, klabel('patMatch)]
                 | 'patMatchAux(K, Pat, Pats) [function, klabel('patMatchAux)]
  rule 'patMatch(A:K, .Pats) => 'none(.KList)
  rule 'patMatch(A:K, 'patCon(X:Pat, Es:Pats))
         => 'patMatchAux(A, X, Es)
  rule 'patMatchAux(A:Int, 'pat(A:Int, E:Exp), Ps:Pats)
         => 'some('result(E, .Map))
  rule 'patMatchAux(A:Int, 'pat(X:Id, E:Exp), Ps:Pats)
         => 'some('result(E, MapItem(X, A)))
  rule 'patMatchAux(A:Float, 'pat(A:Float, E:Exp), Ps:Pats)
         => 'some('result(E, .Map))
  rule 'patMatchAux(A:Float, 'pat(X:Id, E:Exp), Ps:Pats)
         => 'some('result(E, MapItem(X, A)))
  rule 'patMatchAux(A:K, 'pat(X:Exp, E:Exp), Ps:Pats)
         => 'patMatch(A, Ps)

  syntax KItem ::= 'calEval(Exp, Map) [function, klabel('calEval)]
                 | 'nextEval(Exp) [function, klabel('nextEval)]
  rule 'nextEval('plus(A:Int, B:Int)) => '+Int(A, B)
  rule 'nextEval('minus(A:Int, B:Int)) => '-Int(A, B)
  rule 'nextEval('times(A:Int, B:Int)) => '*Int(A, B)
  rule 'nextEval('div(A:Int, B:Int)) => '/Int(A, B)
  rule 'nextEval('mod(A:Int, B:Int)) => '%Int(A, B)
  rule 'nextEval('dplus(A:Int, B:Int)) => '+Float(A, B)
  rule 'nextEval('dminus(A:Int, B:Int)) => '-Float(A, B)
  rule 'nextEval('dtimes(A:Int, B:Int)) => '*Float(A, B)
  rule 'nextEval('ddiv(A:Int, B:Int)) => '/Float(A, B)
  rule 'nextEval('less(A:Int, B:Int)) => '<Int(A, B)
  rule 'nextEval('leq(A:Int, B:Int)) => '<=Int(A, B)
  rule 'nextEval('greater(A:Int, B:Int)) => '>Int(A, B)
  rule 'nextEval('geq(A:Int, B:Int)) => '>=Int(A, B)
  rule 'nextEval('less(A:Float, B:Float)) => '<Float(A, B)
  rule 'nextEval('leq(A:Float, B:Float)) => '<=Float(A, B)
  rule 'nextEval('greater(A:Float, B:Float)) => '>Float(A, B)
  rule 'nextEval('geq(A:Float, B:Float)) => '>=Float(A, B)
  rule 'nextEval('equal(A:K, B:K)) => '==K(A, B)
  rule 'nextEval(A:K) => 'undef(.KList) [owise]

  rule 'calEval(A:Int, M:Map) => A
  rule 'calEval(A:Float, M:Map) => A
  rule 'calEval(A:Id, M:Map) => 'dealWith('lookup(M, A))
  rule 'calEval('plus(A:Exp, B:Exp), M:Map)
                  => 'nextEval('plus('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('minus(A:Exp, B:Exp), M:Map)
                  => 'nextEval('minus('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('times(A:Exp, B:Exp), M:Map)
                  => 'nextEval('times('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('div(A:Exp, B:Exp), M:Map)
                  => 'nextEval('div('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('mod(A:Exp, B:Exp), M:Map)
                  => 'nextEval('mod('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('dplus(A:Exp, B:Exp), M:Map)
                  => 'nextEval('dplus('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('dminus(A:Exp, B:Exp), M:Map)
                  => 'nextEval('dminus('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('dtimes(A:Exp, B:Exp), M:Map)
                  => 'nextEval('dtimes('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('ddiv(A:Exp, B:Exp), M:Map)
                  => 'nextEval('ddiv('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('less(A:Exp, B:Exp), M:Map)
                  => 'nextEval('less('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('leq(A:Exp, B:Exp), M:Map)
                  => 'nextEval('leq('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('greater(A:Exp, B:Exp), M:Map)
                  => 'nextEval('greater('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('geq(A:Exp, B:Exp), M:Map)
                  => 'nextEval('geq('calEval(A, M), 'calEval(B, M)))
  rule 'calEval('equal(A:Exp, B:Exp), M:Map)
                  => 'nextEval('equal('calEval(A, M), 'calEval(B, M)))

  syntax KItem ::= 'infer(Exp, K, Name) [function, klabel('infer)]

  rule 'infer('eval(A:Int, M:Map), A:Int,'const(.KList)) => 'success(.KList)
  rule 'infer('eval(A:Int, M:Map), A':Int, X:Name) => 'error("Wrong inference rule name.")
       requires '=/=K(X, 'const(.KList))
  rule 'infer('eval(A:Int, M:Map), A':K, 'const(.KList)) => 'error("Wrong inference result.")
       requires '=/=K(A, A')

  rule 'infer('eval(A:Float, M:Map), A:Float,'const(.KList)) => 'success(.KList)
  rule 'infer('eval(A:Float, M:Map), A':Float, X:Name) => 'error("Wrong inference rule name.")
       requires '=/=K(X, 'const(.KList))
  rule 'infer('eval(A:Float, M:Map), A':K, 'const(.KList)) => 'error("Wrong inference result.")
       requires '=/=K(A, A')

  rule 'infer('eval(A:Id, M:Map), B:K, 'var(.KList)) => 'success(.KList)
       requires '==K('lookup(M, A), 'some(B))
  rule 'infer('eval(A:Id, M:Map), 'undef(.KList), 'var(.KList)) => 'success(.KList)
       requires '==K('lookup(M, A), 'none(.KList))
  rule 'infer('eval(A:Id, M:Map), B:K, 'var(.KList)) => 'error("Wrong inference result.")
       requires 'andBool('==K('lookup(M, A), 'none(.KList)), '=/=K(B, 'undef(.KList)))
  rule 'infer('eval(A:Id, M:Map), B:K, 'var(.KList)) => 'error("Wrong inference result.")
       requires '=/=K('lookup(M, A), 'some(B))
  rule 'infer('eval(A:Id, M:Map), B:K, X:Name) => 'error("Wrong inference rule name.")
       requires '=/=K(X, 'var(.KList))

  rule 'infer('eval('plus(A:Exp, B:Exp), M:Map), X:K, 'plusrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('plus(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('plus(A:Exp, B:Exp), M:Map), X:K, 'plusrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('plus(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('plus(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'plusrule(.KList))

  rule 'infer('eval('minus(A:Exp, B:Exp), M:Map), X:K, 'minusrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('minus(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('minus(A:Exp, B:Exp), M:Map), X:K, 'minusrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('minus(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('minus(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'minusrule(.KList))

  rule 'infer('eval('times(A:Exp, B:Exp), M:Map), X:K, 'timesrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('times(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('times(A:Exp, B:Exp), M:Map), X:K, 'timesrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('times(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('times(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'timesrule(.KList))

  rule 'infer('eval('div(A:Exp, B:Exp), M:Map), X:K, 'divrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('div(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('div(A:Exp, B:Exp), M:Map), X:K, 'divrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('div(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('div(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'divrule(.KList))

  rule 'infer('eval('mod(A:Exp, B:Exp), M:Map), X:K, 'modrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('mod(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('mod(A:Exp, B:Exp), M:Map), X:K, 'modrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('mod(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('mod(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'modrule(.KList))

  rule 'infer('eval('dplus(A:Exp, B:Exp), M:Map), X:K, 'dplusrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('dplus(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('dplus(A:Exp, B:Exp), M:Map), X:K, 'dplusrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('dplus(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('dplus(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'dplusrule(.KList))

  rule 'infer('eval('dminus(A:Exp, B:Exp), M:Map), X:K, 'dminusrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('dminus(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('dminus(A:Exp, B:Exp), M:Map), X:K, 'dminusrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('dminus(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('dminus(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'dminusrule(.KList))

  rule 'infer('eval('dtimes(A:Exp, B:Exp), M:Map), X:K, 'dtimesrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('dtimes(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('dtimes(A:Exp, B:Exp), M:Map), X:K, 'dtimesrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('dtimes(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('dtimes(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'dtimesrule(.KList))

  rule 'infer('eval('ddiv(A:Exp, B:Exp), M:Map), X:K, 'ddivrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('ddiv(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('ddiv(A:Exp, B:Exp), M:Map), X:K, 'ddivrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('ddiv(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('ddiv(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'ddivrule(.KList))

  rule 'infer('eval('equal(A:Exp, B:Exp), M:Map), X:K, 'equalrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('equal(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('equal(A:Exp, B:Exp), M:Map), X:K, 'equalrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('equal(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('equal(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'equalrule(.KList))

  rule 'infer('eval('less(A:Exp, B:Exp), M:Map), X:K, 'lessrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('less(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('less(A:Exp, B:Exp), M:Map), X:K, 'lessrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('less(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('less(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'lessrule(.KList))

  rule 'infer('eval('leq(A:Exp, B:Exp), M:Map), X:K, 'leqrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('leq(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('leq(A:Exp, B:Exp), M:Map), X:K, 'leqrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('leq(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('leq(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'leqrule(.KList))

  rule 'infer('eval('greater(A:Exp, B:Exp), M:Map), X:K, 'greaterrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('greater(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('greater(A:Exp, B:Exp), M:Map), X:K, 'greaterrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('greater(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('greater(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'greaterrule(.KList))

  rule 'infer('eval('geq(A:Exp, B:Exp), M:Map), X:K, 'geqrule(.KList))
          => 'success(.KList)
       requires '==K('calEval('geq(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('geq(A:Exp, B:Exp), M:Map), X:K, 'geqrule(.KList))
          => 'error("Wrong inference result.")
       requires '=/=K('calEval('geq(A:Exp, B:Exp), M:Map), X)
  rule 'infer('eval('geq(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'geqrule(.KList))

  rule 'infer('eval('appop(A:Exp, B:Exp), M:Map), X:K, 'appfirst(.KList))
          => 'success(.KList)
       requires 'equalExp('app('calEval(A, M:Map), 'calEval(B, M)), X)
  rule 'infer('eval('appop(A:Exp, B:Exp), M:Map), X:K, 'appfirst(.KList))
          => 'error("Wrong inference result.")
       requires 'notBool('equalExp('app('calEval(A, M:Map), 'calEval(B, M)), X))
  rule 'infer('eval('appop(A:Exp, B:Exp), M:Map), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'appfirst(.KList))

  rule 'infer('app('closure(A:Id, E:Exp, M1:Map), B:Exp), X:K, 'appfinal(.KList))
          => 'success(.KList)
       requires 'equalExp('calEval(E, 'mapUpdate(M1, A, B)), X)
  rule 'infer('app('closure(A:Id, E:Exp, M1:Map), B:Exp), X:K, 'appfinal(.KList))
          => 'error("Wrong inference result.")
       requires 'notBool('equalExp('calEval(E, 'mapUpdate(M1, A, B)), X))
  rule 'infer('app('closure(A:Id, E:Exp, M1:Map), B:Exp), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'appfinal(.KList))

  rule 'infer('eval('if(A:Exp, B:Exp, C:Exp), M:Exp), X:K, 'ifrule(.KList))
          => 'success(.KList)
       requires 'andBool('==K('calEval(A, M), 'true(.KList)),
                  'equalExp('eval(B, M), X))
  rule 'infer('eval('if(A:Exp, B:Exp, C:Exp), M:Exp), X:K, 'ifrule(.KList))
          => 'error("Wrong inference result.")
       requires 'andBool('==K('calEval(A, M), 'true(.KList)),
                  'notBool('equalExp('eval(B, M), X)))
  rule 'infer('eval('if(A:Exp, B:Exp, C:Exp), M:Exp), X:K, 'ifrule(.KList))
          => 'success(.KList)
       requires 'andBool('==K('calEval(A, M), 'false(.KList)),
                  'equalExp('eval(C, M), X))
  rule 'infer('eval('if(A:Exp, B:Exp, C:Exp), M:Exp), X:K, 'ifrule(.KList))
          => 'error("Wrong inference result.")
       requires 'andBool('==K('calEval(A, M), 'false(.KList)),
                  'notBool('equalExp('eval(C, M), X)))
  rule 'infer('eval('if(A:Exp, B:Exp, C:Exp), M:Exp), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'ifrule(.KList))

  rule 'infer('eval('fun(A:Id, B:Exp), M:Exp), X:K, 'funrule(.KList))
          => 'success(.KList)
       requires 'equalExp('calEval('fun(A, B), M), X)
  rule 'infer('eval('fun(A:Id, B:Exp), M:Exp), X:K, 'funrule(.KList))
          => 'error("Wrong inference result in fun rule.")
       requires 'notBool('equalExp('calEval('fun(A, B), M), X))
  rule 'infer('eval('fun(A:Id, B:Exp), M:Exp), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'funrule(.KList))

  rule 'infer('eval('let(A:Id, B:Exp, C:Exp), M:Exp), X:K, 'letrule(.KList))
          => 'success(.KList)
       requires 'equalExp('eval(C, 'mapUpdate(M, A, 'calEval(B, M))), X)
  rule 'infer('eval('let(A:Id, B:Exp, C:Exp), M:Exp), X:K, 'letrule(.KList))
          => 'error("Wrong inference result in let rule.")
       requires 'notBool('equalExp('eval(C, 'mapUpdate(M, A, 'calEval(B, M))), X))
  rule 'infer('eval('let(A:Id, B:Exp, C:Exp), M:Exp), X:K, Name:K)
          => 'error("Wrong inference rule name.")
       requires '=/=K(Name, 'letrule(.KList))


  rule 'infer('eval('match(E:Exp, Ps:Pats), M:Map), X:K, 'matchrule(.KList))
          => 'success(.KList)






