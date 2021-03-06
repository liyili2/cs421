
  syntax KItem ::= 'some(K) [klabel('some)]
  syntax KItem ::= "none" [klabel('none)]
  syntax KItem ::= "ok" [klabel('ok)]
  syntax KItem ::= 'success(Bool, Exp) [klabel('success)]
  syntax KItem ::= 'badState(Int, String) [klabel('badState)]
  syntax KItem ::= 'error(Int, String, Exp) [klabel('error)]

  syntax Op ::= "+" [klabel('plus)]
              | "-" [klabel('minus)]
              | "*" [klabel('times)]
              | "/" [klabel('div)]
              | "mod" [klabel('mod)]
              | "+." [klabel('dplus)]
              | "-." [klabel('dminus)]
              | "*." [klabel('dtimes)]
              | "/." [klabel('ddiv)]
              | "<" [klabel('lt)]
              | "<=" [klabel('leq)]
              | ">"  [klabel('gt)]
              | ">=" [klabel('geq)]
              | "="  [klabel('equal)]

  syntax Atomic ::= Id | Int | Float

  syntax Exps ::= List{Atomic,","} [klabel('listCon)]

  syntax Sub ::= Exps | Atomic

  syntax Undef ::= "undef" [klabel('undef)]

  syntax Exp ::= Sub | Undef
                 | 'if(Exp, Exp, Exp)  [klabel('if)]
                 | 'bigIf(Exp, Exp, Exp)  [klabel('bigIf)]
                 | 'app(Exp, Exp) [klabel('app)]
                 | 'bin(Op, Exp, Exp)  [klabel('bin)]
                 | 'unary(Op, Exp)    [klabel('unary)]
                 | 'fun(Id, Exp)      [klabel('fun)]
                 | 'fn(Id, Exp)      [klabel('fn)]
                 | 'bigFun(Id, Exp, Exp)      [klabel('bigFun)]
                 | 'let(Id, Exp, Exp) [klabel('let)]
                 | 'trans(Exp, Exp) [klabel('trans)]
                 | 'match(Exp, Pats) [klabel('match)]

  syntax Pats ::= List{Pat, "|"} [klabel('patCon)]
  syntax Pat ::= 'pat(Sub, Exp) [klabel('patPair)]

  syntax Rule ::= "var"        [klabel('var)] | "const" [klabel('const)]
                | "ifrule"     [klabel('ifrule)]
                | "apprule"    [klabel('apprule)]
                | "oprule"     [klabel('oprule)]
                | "unaryrule"  [klabel('unaryrule)]
                | "funrule"    [klabel('funrule)]
                | "letrule"    [klabel('letrule)]
                | Undef

  syntax Exp ::= 'number(Int, Exp) [klabel('number)]

  syntax Id ::= 'genId(Int) [klabel('genId)]

  syntax KItem ::= 'result(Int, Exp) [klabel('result)]

  syntax Term ::= 'pair(Exp, Rule) [klabel('pair)]

  syntax Bool ::= 'isGenId(K) [function, klabel('isGenId)]
  rule 'isGenId('genId(A:Int)) => 'true(.KList)
  rule 'isGenId(A:K) => 'false(.KList) [owise]

  syntax Set ::= 'minusSet(Set, K) [function, klabel('minusSet)]
  rule 'minusSet(SetCon(SetItem(A:K), S:Set), A:K) => S
  rule 'minusSet(S:Set, A:K) => S [owise]

  syntax Set ::= 'getGenIds(Exp) [function, klabel('getGenIds)]
  rule 'getGenIds('genId(A:Int)) => SetItem(A)
  rule 'getGenIds(A:Id) => .Set
       requires 'notBool('isGenId(A))
  rule 'getGenIds(.Exps) => .Set
  rule 'getGenIds('listCon(A:Exp, B:Exps)) => SetCon('getGenIds(A), 'getGenIds(B))
  rule 'getGenIds('if(A:Exp, B:Exp, C:Exp))
             => SetCon('getGenIds(A), SetCon('getGenIds(B), 'getGenIds(C)))
  rule 'getGenIds('app(A:Exp, B:Exp))
             => SetCon('getGenIds(A), 'getGenIds(B))
  rule 'getGenIds('trans(A:Exp, B:Exp))
             => SetCon('getGenIds(A), 'getGenIds(B))
  rule 'getGenIds('bin(O:Op, A:Exp, B:Exp))
             => SetCon('getGenIds(A), 'getGenIds(B))
  rule 'getGenIds('unary(O:Op, B:Exp)) => 'getGenIds(B)
  rule 'getGenIds('fun(A:Id, B:Exp)) => 'minusSet('getGenIds(B), A)
  rule 'getGenIds('fn(A:Id, B:Exp)) => 'minusSet('getGenIds(B), A)
  rule 'getGenIds('let(A:Id, B:Exp, C:Exp))
               => SetCon('getGenIds(B), 'minusSet('getGenIds(C), A))
  rule 'getGenIds(E:Exp) => .Set [owise]

  syntax Int ::= 'maxInt(Int, Set) [function, klabel('maxInt)]
  rule 'maxInt(A:Int, .Set) => A
  rule 'maxInt(A:Int, SetCon(SetItem(B:Int), S:Set))
             => 'maxInt(B, S)
       requires '>Int(B, A)
  rule 'maxInt(A:Int, SetCon(SetItem(B:Int), S:Set))
             => 'maxInt(A, S) [owise]

  syntax Id ::= 'freshId(Exp) [function, klabel('freshId)]
              | 'freshIdAux(Int) [function, klabel('freshIdAux)]
  rule 'freshId(A:Exp) => 'freshIdAux('maxInt('0(.KList), 'getGenIds(A)))
  rule 'freshIdAux(A:Int) => 'genId('+Int('1(.KList), A))

  syntax KItem ::= 'applyRule(Rule, Exp, Exp) [function, klabel('applyRule)]
                 | 'applyRuleIf(Exp, Exp, Exp, Exp, Id) [function, klabel('applyRuleIf)]
                 | 'applyRuleApp(Exp, Exp, Exp, Id) [function, klabel('applyRuleApp)]
                 | 'applyRuleAppAux(Exp, Exp, Exp, Id, Id) [function, klabel('applyRuleAppAux)]
                 | 'applyRuleBin(Op, Exp, Exp, Exp, Id) [function, klabel('applyRuleBin)]
                 | 'applyRuleBinAux(Op, Exp, Exp, Exp, Id, Id) [function, klabel('applyRuleBinAux)]
                 | 'applyRuleUnary(Op, Exp, Exp, Id) [function, klabel('applyRuleUnary)]

  rule 'applyRule('var(.KList), A:Id, K:Exp) => 'app(K, A)
  rule 'applyRule('const(.KList), A:Int, K:Exp) => 'app(K, A)
  rule 'applyRule('const(.KList), A:Float, K:Exp) => 'app(K, A)
  rule 'applyRule('const(.KList), .Exps, K:Exp) => 'app(K, .Exps)

  rule 'applyRule('ifrule(.KList), 'if(E1:Exp, E2:Exp, E3:Exp), K:Exp)
            => 'applyRuleIf(E1, E2, E3, K,
                'freshId('trans('if(E1:Exp, E2:Exp, E3:Exp), K)))
  rule 'applyRuleIf(E1:Exp, E2:Exp, E3:Exp, K:Exp, A:Id)
         => 'trans(E1, 'fn(A, 'bigIf(A, 'trans(E2, K), 'trans(E3, K))))

  rule 'applyRule('apprule(.KList), 'app(E1:Exp, E2:Exp), K:Exp)
            => 'applyRuleApp(E1, E2, K, 'freshId(K))
  rule 'applyRuleApp(E1:Exp, E2:Exp, K:Exp, A:Id)
         => 'applyRuleAppAux(E1, E2, K, A, 'freshId('trans('app(A, E1), K)))
  rule 'applyRuleAppAux(E1:Exp, E2:Exp, K:Exp, A:Id, B:Id)
          => 'trans(E2, 'fn(B, 'trans(E1, 'fn(A, 'app('app(A, B),K)))))

  rule 'applyRule('oprule(.KList), 'bin(A:Op, E1:Exp, E2:Exp), K:Exp)
          => 'applyRuleBin(A, E1, E2, K, 'freshId(K))
  rule 'applyRuleBin(A:Op, E1:Exp, E2:Exp, K:Exp, B:Id)
         => 'applyRuleBinAux(A:Op, E1, E2, K, B, 'freshId('trans('app(B, E1), K)))
  rule 'applyRuleBinAux(A:Op, E1:Exp, E2:Exp, K:Exp, B:Id, C:Id)
          => 'trans(E2, 'fn(C, 'trans(E1, 'fn(B, 'app(K, 'bin(A:Op, B, C))))))

  rule 'applyRule('unaryrule(.KList), 'unary(A:Op, E1:Exp), K:Exp)
          => 'applyRuleUnary(A, E1, K, 'freshId(K))
  rule 'applyRuleUnary(A:Op, E:Exp, K:Exp, X:Id)
          => 'trans(E, 'fn(X, 'app(K, 'unary(A, X))))

  rule 'applyRule('funrule(.KList), 'fun(X:Id, E:Exp) , K:Exp)
       => 'app(K, 'bigFun(X, K, 'trans(E, K)))
  rule 'applyRule('letrule(.KList), 'let(X:Id, E1:Exp, E2:Exp), K:Exp)
           => 'trans(E1, 'fn(X, 'trans(E2, K)))
  rule 'applyRule('undef(.KList), B:Exp, C:Exp) => 'undef(.KList)
  rule 'applyRule(A:Rule, B:Exp, C:Exp) => 'none(.KList) [owise]

  syntax Exp ::= 'nextStep(Exp, Exp) [function, klabel('nextStep)]

  rule 'nextStep(A:Id, K:Exp) => 'app(K, A)
  rule 'nextStep(A:Int, K:Exp) => 'app(K, A)
  rule 'nextStep(A:Float, K:Exp) => 'app(K, A)
  rule 'nextStep(.Exps, K:Exp) => 'app(K, .Exps)
  rule 'nextStep('if(E1:Exp, E2:Exp, E3:Exp), K:Exp)
           => 'applyRuleIf(E1, E2, E3, K,
                'freshId('trans('if(E1:Exp, E2:Exp, E3:Exp), K)))
  rule 'nextStep('app(E1:Exp, E2:Exp), K:Exp)
            => 'applyRuleApp(E1, E2, K, 'freshId(K))

  rule 'nextStep('bin(A:Op, E1:Exp, E2:Exp), K:Exp)
          => 'applyRuleBin(A, E1, E2, K, 'freshId(K))

  rule 'nextStep('unary(A:Op, E1:Exp), K:Exp)
          => 'applyRuleUnary(A, E1, K, 'freshId(K))

  rule 'nextStep('fun(X:Id, E:Exp) , K:Exp)
       => 'app(K, 'bigFun(X, K, 'trans(E, K)))
  rule 'nextStep('let(X:Id, E1:Exp, E2:Exp), K:Exp)
           => 'trans(E1, 'fn(X, 'trans(E2, K)))
  rule 'nextStep(B:Exp, C:Exp) => 'undef(.KList) [owise]

  syntax KItem ::= 'nop(K) [klabel('nop)]

  syntax KItem ::= 'searchNextStep(Exp) [function, klabel('searchNextStep)]
                 | 'searchNextStepTrans(Exp) [function, klabel('searchNextStepTrans)]
                 | 'searchNextStepIf(K, Exp, Exp) [function, klabel('searchNextStepIf)]
                 | 'searchNextStepIfAux(Exp, K, Exp) [function, klabel('searchNextStepIfAux)]
                 | 'searchNextStepIfNext(Exp, Exp, K) [function, klabel('searchNextStepIfNext)]
                 | 'searchNextStepBigIf(K, Exp, Exp) [function, klabel('searchNextStepBigIf)]
                 | 'searchNextStepBigIfAux(Exp, K, Exp) [function, klabel('searchNextStepBigIfAux)]
                 | 'searchNextStepBigIfNext(Exp, Exp, K) [function, klabel('searchNextStepBigIfNext)]
                 | 'searchNextStepApp(K, Exp) [function, klabel('searchNextStepApp)]
                 | 'searchNextStepAppAux(Exp, K) [function, klabel('searchNextStepAppAux)]
                 | 'searchNextStepBin(Op, K, Exp) [function, klabel('searchNextStepBin)]
                 | 'searchNextStepBinAux(Op, Exp, K) [function, klabel('searchNextStepBinAux)]
                 | 'searchNextStepUnary(Op, K) [function, klabel('searchNextStepUnary)]
                 | 'searchNextStepFun(Id, K) [function, klabel('searchNextStepFun)]
                 | 'searchNextStepFn(Id, K) [function, klabel('searchNextStepFn)]
                 | 'searchNextStepBigFun(Id, K, Exp) [function, klabel('searchNextStepBigFun)]
                 | 'searchNextStepBigFunAux(Id, Exp, K) [function, klabel('searchNextStepBigFunAux)]
                 | 'searchNextStepLet(Id, K, Exp) [function, klabel('searchNextStepLet)]
                 | 'searchNextStepLetAux(Id, Exp, K) [function, klabel('searchNextStepLetAux)]

  rule 'searchNextStep('trans(E1:Exp, E2:Exp))
     => 'searchNextStepTrans('nextStep(E1, E2))
  rule 'searchNextStepTrans('undef(.KList)) => 'undef(.KList)
  rule 'searchNextStepTrans(A:Exp) => 'some(A)
       requires '=/=K(A, 'undef(.KList))
  rule 'searchNextStep(A:Sub) => 'nop(A)
  rule 'searchNextStep('undef(.KList)) => 'undef(.KList)
  rule 'searchNextStep('if(E1:Exp, E2:Exp, E3:Exp))
          => 'searchNextStepIf('searchNextStep(E1), E2, E3)
  rule 'searchNextStepIf('nop(E1:Exp), E2:Exp, E3:Exp)
           => 'searchNextStepIfAux(E1, 'searchNextStep(E2), E3)
  rule 'searchNextStepIf('some(E1:Exp), E2:Exp, E3:Exp) => 'some('if(E1, E2, E3))
  rule 'searchNextStepIf('undef(.KList), E2:Exp, E3:Exp) => 'undef(.KList)
  rule 'searchNextStepIfAux(E1:Exp, 'nop(E2:Exp), E3:Exp)
          => 'searchNextStepIfNext(E1, E2, 'searchNextStep(E3))
  rule 'searchNextStepIfAux(E1:Exp, 'some(E2:Exp), E3:Exp) => 'some('if(E1, E2,E3))
  rule 'searchNextStepIfAux(E1:Exp, 'undef(.KList), E3:Exp) => 'undef(.KList)
  rule 'searchNextStepIfNext(E1:Exp, E2:Exp, 'nop(E3:Exp)) => 'nop('if(E1,E2,E3))
  rule 'searchNextStepIfNext(E1:Exp, E2:Exp, 'some(E3:Exp)) => 'some('if(E1,E2,E3))
  rule 'searchNextStepIfNext(E1:Exp, E2:Exp, 'undef(.KList)) => 'undef(.KList)

  rule 'searchNextStep('bigIf(E1:Exp, E2:Exp, E3:Exp))
          => 'searchNextStepBigIf('searchNextStep(E1), E2, E3)
  rule 'searchNextStepBigIf('nop(E1:Exp), E2:Exp, E3:Exp)
           => 'searchNextStepBigIfAux(E1, 'searchNextStep(E2), E3)
  rule 'searchNextStepBigIf('some(E1:Exp), E2:Exp, E3:Exp) => 'some('bigIf(E1, E2, E3))
  rule 'searchNextStepBigIf('undef(.KList), E2:Exp, E3:Exp) => 'undef(.KList)
  rule 'searchNextStepBigIfAux(E1:Exp, 'nop(E2:Exp), E3:Exp)
          => 'searchNextStepBigIfNext(E1, E2, 'searchNextStep(E3))
  rule 'searchNextStepBigIfAux(E1:Exp, 'some(E2:Exp), E3:Exp) => 'some('bigIf(E1, E2,E3))
  rule 'searchNextStepBigIfAux(E1:Exp, 'undef(.KList), E3:Exp) => 'undef(.KList)
  rule 'searchNextStepBigIfNext(E1:Exp, E2:Exp, 'nop(E3:Exp)) => 'nop('bigIf(E1,E2,E3))
  rule 'searchNextStepBigIfNext(E1:Exp, E2:Exp, 'some(E3:Exp)) => 'some('bigIf(E1,E2,E3))
  rule 'searchNextStepBigIfNext(E1:Exp, E2:Exp, 'undef(.KList)) => 'undef(.KList)
  rule 'searchNextStep('app(E1:Exp, E2:Exp))
          => 'searchNextStepApp('searchNextStep(E1), E2)
  rule 'searchNextStepApp('nop(E1:Exp), E2:Exp)
          => 'searchNextStepAppAux(E1, 'searchNextStep(E2))
  rule 'searchNextStepApp('some(E1:Exp), E2:Exp) => 'some('app(E1, E2))
  rule 'searchNextStepApp('undef(.KList), E2:Exp) => 'undef(.KList)
  rule 'searchNextStepAppAux(E1:Exp, 'nop(E2:Exp)) => 'nop('app(E1, E2))
  rule 'searchNextStepAppAux(E1:Exp, 'some(E2:Exp)) => 'some('app(E1, E2))
  rule 'searchNextStepAppAux(E1:Exp, 'undef(.KList)) => 'undef(.KList)
  rule 'searchNextStep('bin(A:Op, E1:Exp, E2:Exp))
           => 'searchNextStepBin(A, 'searchNextStep(E1), E2)
  rule 'searchNextStepBin(A:Op, 'nop(E1:Exp), E2:Exp)
          => 'searchNextStepBinAux(A, E1, 'searchNextStep(E2))
  rule 'searchNextStepBin(A:Op, 'some(E1:Exp), E2:Exp) => 'some('bin(A, E1, E2))
  rule 'searchNextStepBin(A:Op, 'undef(.KList), E2:Exp) => 'undef(.KList)
  rule 'searchNextStepBinAux(A:Op, E1:Exp, 'nop(E2:Exp)) => 'some('bin(A, E1, E2))
  rule 'searchNextStepBinAux(A:Op, E1:Exp, 'some(E2:Exp)) => 'some('bin(A, E1, E2))
  rule 'searchNextStepBinAux(A:Op, E1:Exp, 'undef(.KList)) => 'undef(.KList)
  rule 'searchNextStep('unary(A:Op, E1:Exp))
           => 'searchNextStepUnary(A, 'searchNextStep(E1))
  rule 'searchNextStepUnary(A:Op, 'undef(.KList)) => 'undef(.KList)
  rule 'searchNextStepUnary(A:Op, 'some(E1:Exp)) => 'some('unary(A, E1))
  rule 'searchNextStepUnary(A:Op, 'nop(E1:Exp)) => 'nop('unary(A, E1))
  rule 'searchNextStep('fun(A:Id, E:Exp)) => 'searchNextStepFun(A, 'searchNextStep(E))
  rule 'searchNextStepFun(A:Id, 'nop(E:Exp)) => 'nop('fun(A, E))
  rule 'searchNextStepFun(A:Id, 'some(E:Exp)) => 'some('fun(A, E))
  rule 'searchNextStepFun(A:Id, 'undef(.KList)) => 'undef(.KList)
  rule 'searchNextStepFn(A:Id, 'nop(E:Exp)) => 'nop('fn(A, E))
  rule 'searchNextStepFn(A:Id, 'some(E:Exp)) => 'some('fn(A, E))
  rule 'searchNextStepFn(A:Id, 'undef(.KList)) => 'undef(.KList)
  rule 'searchNextStep('bigFun(A:Id, E1:Exp, E2:Exp))
            => 'searchNextStepBigFun(A, 'searchNextStep(E1), E2)
  rule 'searchNextStepBigFun(A:Id, 'some(E1:Exp), E2:Exp) => 'some('bigFun(A, E1, E2))
  rule 'searchNextStepBigFun(A:Id, 'undef(.KList), E2:Exp) => 'undef(.KList)
  rule 'searchNextStepBigFun(A:Id, 'nop(E1:Exp), E2:Exp)
           => 'searchNextStepBigFunAux(A, E1, 'searchNextStep(E2))
  rule 'searchNextStepBigFunAux(A:Id, E1:Exp, 'nop(E2:Exp)) => 'nop('bigFun(A, E1, E2))
  rule 'searchNextStepBigFunAux(A:Id, E1:Exp, 'some(E2:Exp)) => 'some('bigFun(A, E1, E2))
  rule 'searchNextStepBigFunAux(A:Id, E1:Exp, 'undef(.KList)) => 'undef(.KList)

  rule 'searchNextStep('let(A:Id, E1:Exp, E2:Exp))
            => 'searchNextStepLet(A, 'searchNextStep(E1), E2)
  rule 'searchNextStepLet(A:Id, 'some(E1:Exp), E2:Exp) => 'some('let(A, E1, E2))
  rule 'searchNextStepLet(A:Id, 'undef(.KList), E2:Exp) => 'undef(.KList)
  rule 'searchNextStepLet(A:Id, 'nop(E1:Exp), E2:Exp)
           => 'searchNextStepLetAux(A, E1, 'searchNextStep(E2))
  rule 'searchNextStepLetAux(A:Id, E1:Exp, 'nop(E2:Exp)) => 'nop('let(A, E1, E2))
  rule 'searchNextStepLetAux(A:Id, E1:Exp, 'some(E2:Exp)) => 'some('let(A, E1, E2))
  rule 'searchNextStepLetAux(A:Id, E1:Exp, 'undef(.KList)) => 'undef(.KList)

  syntax Exp ::= 'getOneStep(Exp) [function, klabel('getOneStep)]
               | 'getOneStepAux(K) [function, klabel('getOneStepAux)]
  rule 'getOneStep(E:Exp) => 'getOneStepAux('searchNextStep(E))
  rule 'getOneStepAux('nop(E:Exp)) => 'undef(.KList)
  rule 'getOneStepAux('undef(.KList)) => 'undef(.KList)
  rule 'getOneStepAux('some(E:Exp)) => E

  syntax KItem ::= 'giveNum(Int, Exp) [function, klabel('giveNum)]
               | 'giveNumExps(K, Exps) [function, klabel('giveNumExps)]
               | 'giveNumExpsAux(Exp, K) [function, klabel('giveNumExpsAux)]
               | 'giveNumIf(K, Exp, Exp) [function, klabel('giveNumIf)]
               | 'giveNumIfAux(Exp, K, Exp) [function, klabel('giveNumIfAux)]
               | 'giveNumIfNext(Exp, Exp, K) [function, klabel('giveNumIfNext)]
               | 'giveNumBigIf(K, Exp, Exp) [function, klabel('giveNumBigIf)]
               | 'giveNumBigIfAux(Exp, K, Exp) [function, klabel('giveNumBigIfAux)]
               | 'giveNumBigIfNext(Exp, Exp, K) [function, klabel('giveNumBigIfNext)]
               | 'giveNumApp(K, Exp) [function, klabel('giveNumApp)]
               | 'giveNumAppAux(Exp, K) [function, klabel('giveNumAppAux)]
               | 'giveNumBin(Op, K, Exp) [function, klabel('giveNumBin)]
               | 'giveNumBinAux(Op, Exp, K) [function, klabel('giveNumBinAux)]
               | 'giveNumUnary(Op, K) [function, klabel('giveNumUnary)]
               | 'giveNumContinue(Id, K) [function, klabel('giveNumContinue)]
               | 'giveNumFun(Id, K) [function, klabel('giveNumFun)]
               | 'giveNumBigFun(Id, K, Exp) [function, klabel('giveNumBigFun)]
               | 'giveNumBigFunAux(Id, Exp, K) [function, klabel('giveNumBigFunAux)]
               | 'giveNumLet(Id, K, Exp) [function, klabel('giveNumLet)]
               | 'giveNumLetAux(Id, Exp, K) [function, klabel('giveNumLetAux)]
               | 'giveNumTrans(Int, K, Exp) [function, klabel('giveNumTrans)]
               | 'giveNumTransAux(Int, Exp, K) [function, klabel('giveNumTransAux)]

  rule 'giveNum(A:Int, B:Undef) => 'result(A, B)
  rule 'giveNum(A:Int, B:Atomic) => 'result(A, B)
  rule 'giveNum(A:Int, .Exps) => 'result(A, .Exps)
  rule 'giveNum(A:Int, 'listCon(B:Exp, C:Exps))
          => 'giveNumExps('giveNum(A, B), C)
  rule 'giveNumExps('result(A:Int, B:Exp), C:Exps)
          => 'giveNumExpsAux(B, 'giveNum(A, C))
  rule 'giveNumExpsAux(B:Exp, 'result(A:Int, C:Exps))
             => 'result(A, 'listCon(B, C))

  rule 'giveNum(A:Int, 'if(B:Exp, E1:Exp, E2:Exp))
          => 'giveNumIf('giveNum(A, B), E1, E2)
  rule 'giveNumIf('result(A:Int, B:Exp), E1:Exp, E2:Exp)
          => 'giveNumIfAux(B, 'giveNum(A, E1), E2)
  rule 'giveNumIfAux(B:Exp, 'result(A:Int, E1:Exp), E2:Exp)
          => 'giveNumIfNext(B, E1, 'giveNum(A, E2))
  rule 'giveNumIfNext(B:Exp, E1:Exp, 'result(A:Int, E2:Exp))
          => 'result(A, 'if(B, E1, E2))

  rule 'giveNum(A:Int, 'bigIf(B:Exp, E1:Exp, E2:Exp))
          => 'giveNumBigIf('giveNum(A, B), E1, E2)
  rule 'giveNumBigIf('result(A:Int, B:Exp), E1:Exp, E2:Exp)
          => 'giveNumBigIfAux(B, 'giveNum(A, E1), E2)
  rule 'giveNumBigIfAux(B:Exp, 'result(A:Int, E1:Exp), E2:Exp)
          => 'giveNumBigIfNext(B, E1, 'giveNum(A, E2))
  rule 'giveNumBigIfNext(B:Exp, E1:Exp, 'result(A:Int, E2:Exp))
          => 'result(A, 'bigIf(B, E1, E2))

  rule 'giveNum(A:Int, 'app(E1:Exp, E2:Exp))
          => 'giveNumApp('giveNum(A, E1), E2)
  rule 'giveNumApp('result(A:Int, E1:Exp),E2:Exp)
          => 'giveNumAppAux(E1, 'giveNum(A, E2))
  rule 'giveNumAppAux(E1:Exp, 'result(A:Int, E2:Exp))
          => 'result(A, 'app(E1, E2))

  rule 'giveNum(A:Int, 'bin(X:Op, E1:Exp, E2:Exp))
          => 'giveNumBin(X, 'giveNum(A, E1), E2)
  rule 'giveNumBin(X:Op, 'result(A:Int, E1:Exp), E2:Exp)
         => 'giveNumBinAux(X, E1, 'giveNum(A, E2))
  rule 'giveNumBinAux(X:Op, E1:Exp, 'result(A:Int, E2:Exp))
         => 'result(A, 'bin(X, E1, E2))

  rule 'giveNum(A:Int, 'unary(X:Op, E1:Exp))
          => 'giveNumUnary(X, 'giveNum(A, E1))
  rule 'giveNumUnary(X:Op, 'result(A:Int, E1:Exp))
          => 'result(A, 'unary(X, E1))

  rule 'giveNum(A:Int, 'fun(X:Id, E:Exp))
           => 'giveNumFun(X, 'giveNum(A, E))
  rule 'giveNumFun(X:Id, 'result(A:Int, E:Exp))
          => 'result(A, 'fun(X, E))

  rule 'giveNum(A:Int, 'bigFun(X:Id, Y:Exp, E:Exp))
           => 'giveNumBigFun(X, 'giveNum(A, Y), E)
  rule 'giveNumBigFun(X:Id, 'result(A:Int, Y:Exp), E:Exp)
          => 'giveNumBigFunAux(X, Y, 'giveNum(A, E))
  rule 'giveNumBigFunAux(X:Id, Y:Exp, 'result(A:Int, E:Exp))
          => 'result(A, 'bigFun(X, Y, E))

  rule 'giveNum(A:Int, 'fn(X:Id, E:Exp))
           => 'giveNumContinue(X, 'giveNum(A, E))
  rule 'giveNumContinue(X:Id, 'result(A:Int, E:Exp))
          => 'result(A, 'fn(X, E))

  rule 'giveNum(A:Int, 'let(X:Id, E1:Exp, E2:Exp))
         => 'giveNumLet(X, 'giveNum(A, E1), E2)
  rule 'giveNumLet(X:Id, 'result(A:Int, E1:Exp), E2:Exp)
          => 'giveNumLetAux(X, E1, 'giveNum(A,E2))
  rule 'giveNumLetAux(X:Id, E1:Exp, 'result(A:Int, E2:Exp))
         => 'result(A, 'let(X, E1, E2))

  rule 'giveNum(A:Int, 'trans(E1:Exp, E2:Exp))
         => 'giveNumTrans(A, 'giveNum('+Int(A, '1(.KList)), E1), E2)
  rule 'giveNumTrans(A:Int, 'result(B:Int, E1:Exp), E2:Exp)
          => 'giveNumTransAux(A, E1, 'giveNum(B,E2))
  rule 'giveNumTransAux(A:Int, E1:Exp, 'result(B:Int, E2:Exp))
         => 'result(B, 'number(A, 'trans(E1, E2)))

  syntax Exp ::= 'removeNum(Exp) [function, klabel('removeNum)]
  rule 'removeNum(A:Atomic) => A
  rule 'removeNum(.Exps) => .Exps
  rule 'removeNum('listCon(A:Exp, B:Exps))
               => 'listCon('removeNum(A), 'removeNum(B))
  rule 'removeNum('undef(.KList)) => 'undef(.KList)
  rule 'removeNum('if(E1:Exp, E2:Exp, E3:Exp))
          => 'if('removeNum(E1), 'removeNum(E2), 'removeNum(E3))
  rule 'removeNum('bigIf(E1:Exp, E2:Exp, E3:Exp))
          => 'bigIf('removeNum(E1), 'removeNum(E2), 'removeNum(E3))
  rule 'removeNum('app(E1:Exp, E2:Exp))
         => 'app('removeNum(E1), 'removeNum(E2))
  rule 'removeNum('bin(A:Op, E1:Exp, E2:Exp))
         => 'bin(A, 'removeNum(E1), 'removeNum(E2))
  rule 'removeNum('unary(A:Op, E1:Exp))
         => 'unary(A, 'removeNum(E1))
  rule 'removeNum('fun(A:Id, E1:Exp))
         => 'fun(A, 'removeNum(E1))
  rule 'removeNum('bigFun(A:Id, B:Exp, E1:Exp))
         => 'bigFun(A, 'removeNum(B), 'removeNum(E1))
  rule 'removeNum('fn(A:Id, E1:Exp))
         => 'fn(A, 'removeNum(E1))
  rule 'removeNum('let(A:Id, E1:Exp, E2:Exp))
         => 'let(A, 'removeNum(E1), 'removeNum(E2))
  rule 'removeNum('trans(E1:Exp, E2:Exp))
         => 'trans('removeNum(E1), 'removeNum(E2))
  rule 'removeNum('number(A:Int, E2:Exp)) => 'removeNum(E2)

  syntax List ::= 'removeNums(List) [function, klabel('removeNums)]
  rule 'removeNums(.List) => .List
  rule 'removeNums(ListCon(ListItem(A:K), L:List))
            => ListCon(ListItem('removeNum(A)), 'removeNums(L))

  syntax Map ::= 'applyRules(Rule, Exp) [function, klabel('applyRules)]
  rule 'applyRules(A:Rule, B:Sub) => .Map
  rule 'applyRules(A:Rule, B:Undef) => .Map
  rule 'applyRules(A:Rule, 'if(E1:Exp, E2:Exp, E3:Exp))
            => MapCon('applyRules(A, E1), MapCon('applyRules(A, E2), 'applyRules(A, E3)))
  rule 'applyRules(A:Rule, 'bigIf(E1:Exp, E2:Exp, E3:Exp))
            => MapCon('applyRules(A, E1), MapCon('applyRules(A, E2), 'applyRules(A, E3)))
  rule 'applyRules(A:Rule, 'app(E1:Exp, E2:Exp))
           => MapCon('applyRules(A, E1), 'applyRules(A, E2))
  rule 'applyRules(A:Rule, 'bin(B:Op, E1:Exp, E2:Exp))
           => MapCon('applyRules(A, E1), 'applyRules(A, E2))
  rule 'applyRules(A:Rule, 'unary(B:Op, E1:Exp))
           => 'applyRules(A, E1)
  rule 'applyRules(A:Rule, 'fun(B:Id, E1:Exp))
           => 'applyRules(A, E1)
  rule 'applyRules(A:Rule, 'bigFun(B:Id, C:Exp, E1:Exp))
           => MapCon('applyRules(A, C), 'applyRules(A, E1))
  rule 'applyRules(A:Rule, 'fn(B:Id, E1:Exp))
           => 'applyRules(A, E1)
  rule 'applyRules(A:Rule, 'let(B:Id, E1:Exp, E2:Exp))
           => MapCon('applyRules(A, E1), 'applyRules(A, E2))
  rule 'applyRules(A:Rule, 'number(X:Int, 'trans(E1:Exp, E2:Exp)))
           => MapCon(MapItem(X, 'applyRule(A, E1, E2)),
               MapCon('applyRules(A, E1), 'applyRules(A, E2)))
       requires '=/=K('applyRule(A, E1, E2), 'none(.KList))
  rule 'applyRules(A:Rule, 'number(X:Int, 'trans(E1:Exp, E2:Exp)))
             => MapCon('applyRules(A, E1), 'applyRules(A, E2))
       requires '==K('applyRule(A, E1, E2), 'none(.KList))

  syntax Exp ::= 'subst(Exp, Int, Exp) [function, klabel('subst)]
  rule 'subst(E1:Sub, A:Int, E2:Exp) => E1
  rule 'subst(E1:Undef, A:Int, E2:Exp) => E1
  rule 'subst('if(E1:Exp, E2:Exp, E3:Exp), A:Int, D:Exp)
             => 'if('subst(E1, A, D), 'subst(E2, A, D), 'subst(E3, A, D))
  rule 'subst('bigIf(E1:Exp, E2:Exp, E3:Exp), A:Int, D:Exp)
             => 'bigIf('subst(E1, A, D), 'subst(E2, A, D), 'subst(E3, A, D))
  rule 'subst('app(E1:Exp, E2:Exp), A:Int, D:Exp)
            => 'app('subst(E1, A, D), 'subst(E2, A, D))
  rule 'subst('bin(X:Op, E1:Exp, E2:Exp), A:Int, D:Exp)
            => 'bin(X, 'subst(E1, A, D), 'subst(E2, A, D))
  rule 'subst('unary(X:Op, E1:Exp), A:Int, D:Exp)
            => 'unary(X, 'subst(E1, A, D))
  rule 'subst('fun(X:Id, E1:Exp), A:Int, D:Exp)
            => 'fun(X, 'subst(E1, A, D))
  rule 'subst('bigFun(X:Id, Y:Exp, E1:Exp), A:Int, D:Exp)
            => 'bigFun(X, 'subst(Y, A, D), 'subst(E1, A, D))
  rule 'subst('fn(X:Id, E1:Exp), A:Int, D:Exp)
            => 'fn(X, 'subst(E1, A, D))
  rule 'subst('let(X:Id, E1:Exp, E2:Exp), A:Int, D:Exp)
            => 'let(X, 'subst(E1, A, D), 'subst(E2, A, D))
  rule 'subst('trans(E1:Exp, E2:Exp), A:Int, D:Exp)
            => 'trans('subst(E1, A, D), 'subst(E2, A, D))
  rule 'subst('number(A:Int, E:Exp), A:Int, D:Exp) => D
  rule 'subst('number(A':Int, E:Exp), A:Int, D:Exp)
                => 'number(A', 'subst(E, A, D))
        requires '=/=K(A, A')

  syntax List ::= 'substAll(Exp, Map) [function, klabel('substAll)]
  rule 'substAll(E:Exp, .Map) => .List
  rule 'substAll(E:Exp, MapCon(MapItem(A:Int, B:Exp), M:Map))
            => ListCon(ListItem('subst(E, A, B)), 'substAll(E, M))

  syntax Exp ::= 'alphaSubst(Exp, Id, Id) [function, klabel('alphaSubst)]
  rule 'alphaSubst(A:Id, A:Id, B:Id) => B
  rule 'alphaSubst(A:Id, A':Id, B:Id) => A
        requires '=/=K(A, A')
  rule 'alphaSubst(A:Int, A':Id, B:Id) => A
  rule 'alphaSubst(A:Float, A':Id, B:Id) => A
  rule 'alphaSubst(.Exps, A':Id, B:Id) => .Exps
  rule 'alphaSubst('listCon(A:Exp, C:Exps), A':Id, B:Id)
           => 'listCon('alphaSubst(A, A', B), 'alphaSubst(C, A', B))
  rule 'alphaSubst('undef(.KList), A:Id, B:Id) => 'undef(.KList)
  rule 'alphaSubst('if(E1:Exp, E2:Exp, E3:Exp), A:Id, B:Id)
              => 'if('alphaSubst(E1,A, B),
                'alphaSubst(E2, A, B), 'alphaSubst(E3, A, B))
  rule 'alphaSubst('bigIf(E1:Exp, E2:Exp, E3:Exp), A:Id, B:Id)
              => 'bigIf('alphaSubst(E1,A, B),
                'alphaSubst(E2, A, B), 'alphaSubst(E3, A, B))
  rule 'alphaSubst('app(E1:Exp, E2:Exp), A:Id, B:Id)
           => 'app('alphaSubst(E1, A, B), 'alphaSubst(E2, A, B))
  rule 'alphaSubst('bin(X:Op, E1:Exp, E2:Exp), A:Id, B:Id)
           => 'bin(X, 'alphaSubst(E1, A, B), 'alphaSubst(E2, A, B))
  rule 'alphaSubst('unary(X:Op, E1:Exp), A:Id, B:Id)
           => 'unary(X, 'alphaSubst(E1, A, B))
  rule 'alphaSubst('fun(A:Id, E1:Exp), A:Id, B:Id) => 'fun(A, E1)
  rule 'alphaSubst('fun(A':Id, E1:Exp), A:Id, B:Id)
            => 'fun(A', 'alphaSubst(E1, A, B))
        requires '=/=K(A, A')
  rule 'alphaSubst('bigFun(A:Id, Y:Exp, E1:Exp), A:Id, B:Id)
             =>'bigFun(A, 'alphaSubst(Y, A, B), E1)
  rule 'alphaSubst('bigFun(A':Id, Y:Exp, E1:Exp), A:Id, B:Id)
            => 'bigFun(A', 'alphaSubst(Y, A, B), 'alphaSubst(E1, A, B))
        requires '=/=K(A, A')

  rule 'alphaSubst('fn(A:Id, E1:Exp), A:Id, B:Id) => 'fn(A, E1)
  rule 'alphaSubst('fn(A':Id, E1:Exp), A:Id, B:Id)
            => 'fn(A', 'alphaSubst(E1, A, B))
        requires '=/=K(A, A')

  rule 'alphaSubst('let(A:Id, E1:Exp, E2:Exp), A:Id, B:Id)
            => 'let(A, 'alphaSubst(E1, A, B), E2)
  rule 'alphaSubst('let(A':Id, E1:Exp, E2:Exp), A:Id, B:Id)
            => 'let(A', 'alphaSubst(E1, A, B), 'alphaSubst(E2, A, B))
        requires '=/=K(A, A')
  rule 'alphaSubst('trans(E1:Exp, E2:Exp), A:Id, B:Id)
            => 'trans('alphaSubst(E1, A, B), 'alphaSubst(E2, A, B))

  syntax Bool ::= 'equalExp(Exp, Exp) [function, klabel('equalExp)]
  rule 'equalExp(A:Sub, A) => 'true(.KList)
  rule 'equalExp(A:Undef, A) => 'true(.KList)
  rule 'equalExp('if(E1:Exp, E2:Exp, E3:Exp), 'if(D1:Exp,D2:Exp, D3:Exp))
          => 'andBool('equalExp(E1, D1), 'andBool('equalExp(E2, D2), 'equalExp(E3, D3)))
  rule 'equalExp('bigIf(E1:Exp, E2:Exp, E3:Exp), 'bigIf(D1:Exp,D2:Exp, D3:Exp))
          => 'andBool('equalExp(E1, D1), 'andBool('equalExp(E2, D2), 'equalExp(E3, D3)))
  rule 'equalExp('app(E1:Exp, E2:Exp), 'app(D1:Exp,D2:Exp))
          => 'andBool('equalExp(E1, D1), 'equalExp(E2, D2))
  rule 'equalExp('bin(A:Op, E1:Exp, E2:Exp), 'bin(A:Op, D1:Exp,D2:Exp))
          => 'andBool('equalExp(E1, D1), 'equalExp(E2, D2))
  rule 'equalExp('unary(A:Op, E1:Exp), 'unary(A:Op, D1:Exp))
          => 'equalExp(E1, D1)
  rule 'equalExp('trans(E1:Exp, E2:Exp), 'trans(D1:Exp, D2:Exp))
          => 'andBool('equalExp(E1, D1), 'equalExp(E2, D2))
  rule 'equalExp('fun(X:Id, E1:Exp), 'fun(X:Id, D1:Exp))
          => 'equalExp(E1, D1)
  rule 'equalExp('fun(X:Id, E1:Exp), 'fun(Y:Id, D1:Exp))
          => 'equalExp('alphaSubst(E1, X, Y), D1)
       requires '=/=K(X, Y)

  rule 'equalExp('bigFun(X:Id, Y:Exp, E1:Exp), 'bigFun(X:Id, Y1:Exp, D1:Exp))
          => 'andBool('equalExp(Y, Y1), 'equalExp(E1, D1))
  rule 'equalExp('bigFun(X:Id, Y:Exp, E1:Exp), 'bigFun(X':Id, Y1:Exp, D1:Exp))
          => 'andBool('equalExp(Y, Y1),'equalExp('alphaSubst(E1, X, X'), D1))
       requires '=/=K(X, X')

  rule 'equalExp('fn(X:Id, E1:Exp), 'fn(X:Id, D1:Exp))
          => 'equalExp(E1, D1)
  rule 'equalExp('fn(X:Id, E1:Exp), 'fn(Y:Id, D1:Exp))
          => 'equalExp('alphaSubst(E1, X, Y), D1)
       requires '=/=K(X, Y)
  rule 'equalExp('let(X:Id, E1:Exp, E2:Exp), 'let(X:Id, D1:Exp, D2:Exp))
          => 'andBool('equalExp(E1, D1), 'equalExp(E2, D2))
  rule 'equalExp('let(X:Id, E1:Exp, E2:Exp), 'let(Y:Id, D1:Exp, D2:Exp))
          => 'andBool('equalExp(E1, D1), 'equalExp('alphaSubst(E2, X, Y), D2))
       requires '=/=K(X, Y)
  rule 'equalExp(A:Exp, B:Exp) => 'false(.KList) [owise]

  syntax Bool ::= 'equalExps(Exp, List) [function, klabel('equalExps)]
  rule 'equalExps(E:Exp, .List) => 'false(.KList)
  rule 'equalExps(E:Exp, ListCon(ListItem(A:K), L:List))
            => 'orBool('equalExp(E, A), 'equalExps(E, L))

  syntax Bool ::= 'existTrans(Exp) [function, klabel('existTrans)]
  rule 'existTrans(A:Sub) => 'false(.KList)
  rule 'existTrans('undef(.KList)) => 'false(.KList)
  rule 'existTrans('if(E1:Exp, E2:Exp, E3:Exp))
            => 'orBool('existTrans(E1), 'orBool('existTrans(E2), 'existTrans(E3)))
  rule 'existTrans('bigIf(E1:Exp, E2:Exp, E3:Exp))
            => 'orBool('existTrans(E1), 'orBool('existTrans(E2), 'existTrans(E3)))
  rule 'existTrans('app(E1:Exp, E2:Exp))
            => 'orBool('existTrans(E1), 'existTrans(E2))
  rule 'existTrans('bin(A:Op, E1:Exp, E2:Exp))
            => 'orBool('existTrans(E1), 'existTrans(E2))
  rule 'existTrans('unary(A:Op, E1:Exp))
            => 'existTrans(E1)
  rule 'existTrans('fun(A:Id, E1:Exp))
            => 'existTrans(E1)
  rule 'existTrans('fn(A:Id, E1:Exp))
            => 'existTrans(E1)
  rule 'existTrans('bigFun(A:Id, E1:Exp, E2:Exp))
            => 'orBool('existTrans(E1), 'existTrans(E2))
  rule 'existTrans('let(A:Id, E1:Exp, E2:Exp))
            => 'orBool('existTrans(E1), 'existTrans(E2))
  rule 'existTrans('trans(E1:Exp, E2:Exp)) => 'true(.KList)
  rule 'existTrans('match(E1:Exp, E2:Pats)) => 'existTrans(E1)
  rule 'existTrans('number(A:Int, E:Exp)) => 'existTrans(E)

  syntax KItem ::= 'stepEval(Exp, Exp, Rule) [function, klabel('stepEval)]
                 | 'stepEvalAux(K, Exp, Exp, Rule) [function, klabel('stepEvalAux)]
                 | 'stepEvalAux1(Map, Exp, Exp) [function, klabel('stepEvalAux1)]
                 | 'stepEvalAux2(List, Exp) [function, klabel('stepEvalAux2)]
  rule 'stepEval(E:Exp, D:Exp, R:Rule)
         => 'stepEvalAux('giveNum('0(.KList), E), E, D, R)
  rule 'stepEvalAux('result(A:Int, E:Exp), E:Exp, D:Exp, R:Rule)
                => 'badState('0(.KList), "Nothing can be transformed.")
  rule 'stepEvalAux('result(A:Int, E':Exp), E:Exp, D:Exp, R:Rule)
         => 'stepEvalAux1('applyRules(R, E'),E', D) [owise]
  rule 'stepEvalAux1(.Map, E:Exp, D:Exp) => 'badState('2(.KList), "The input rule name is incorrect.")
  rule 'stepEvalAux1(M:Map, E:Exp, D:Exp) => 'stepEvalAux2('removeNums('substAll(E, M)),D) [owise]
  rule 'stepEvalAux2(L:List, D:Exp) => 'ok(.KList)
        requires 'equalExps(D, L)
  rule 'stepEvalAux2(L:List, D:Exp)
                => 'badState('1(.KList), "Student wrongly transforms the CPS according to the rule.") [owise]

  syntax KItem ::= 'eval(Int, Exp, List) [function, klabel('eval)]
                 | 'evalAux(Int, K, Exp, Exp, List) [function, klabel('evalAux)]
                 | 'output(Int, K) [klabel('output)]
  rule 'eval(I:Int, E:Exp, .List) => 'output(I, 'success('existTrans(E), E))
  rule 'eval(I:Int, E:Exp, ListCon(ListItem('pair(E1:Exp, R:Rule)), L:List))
               => 'evalAux(I, 'stepEval(E, E1, R), E, E1, L)
  rule 'evalAux(I:Int, 'ok(.KList), E:Exp, E1:Exp, L:List) => 'eval('+Int(I, '1(.KList)), E1, L) 
  rule 'evalAux(I:Int, 'badState(X:Int, S:String), E:Exp, E1:Exp, L:List)
                  => 'output(I, 'error(X, S:String, E1))

  configuration <k> PGM:KItem </k>

  program 'eval('0(.KList), 'trans('let($x(.KList),
            'bin('plus(.KList), $y(.KList), '1(.KList)), 'bin('times(.KList), $x(.KList), '2(.KList))), $k(.KList)), ListItem('pair('trans('bin('plus(.KList), $y(.KList), '1(.KList)),
            'fn($x(.KList), 'trans('bin('times(.KList), $x(.KList), '2(.KList)), $k(.KList)))), 'letrule(.KList))))
          


