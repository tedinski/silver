grammar silver:compiler:extension:strategyattr;

import silver:compiler:metatranslation;
import silver:compiler:definition:flow:syntax;
import silver:compiler:definition:flow:ast only lhsVertexType;

import silver:compiler:definition:flow:driver only ProductionGraph, FlowType, constructAnonymousGraph;
import silver:compiler:driver:util;

annotation genName::String; -- Used to generate the names of lifted strategy attributes

inherited attribute recVarNameEnv::[Pair<String String>]; -- name, (isTotal, genName)
inherited attribute recVarTotalEnv::[Pair<String Boolean>]; -- name, (isTotal, genName)
inherited attribute recVarTotalNoEnvEnv::[Pair<String Boolean>]; -- same as above but doesn't depend on env
inherited attribute isOutermost::Boolean;
inherited attribute outerAttr::String;
inherited attribute inlinedStrategies::[String];
type LiftedInhs = {recVarNameEnv, recVarTotalNoEnvEnv, outerAttr, isOutermost};
monoid attribute liftedStrategies::[(String, Decorated StrategyExpr with LiftedInhs)];
synthesized attribute attrRefName::Maybe<String>;
synthesized attribute isId::Boolean;
synthesized attribute isFail::Boolean;
synthesized attribute isTotal::Boolean;
synthesized attribute isTotalNoEnv::Boolean; -- same as above but doesn't depend on env
synthesized attribute isTotalInProd::Boolean; -- can use env and frame
inherited attribute givenInputElements::[NamedSignatureElement];
synthesized attribute attrRefNames::[Maybe<String>];
monoid attribute containsFail::Boolean with false, ||;
monoid attribute allId::Boolean with true, &&;
monoid attribute allTotal::Boolean with true, &&;
monoid attribute freeRecVars::[String];
monoid attribute partialRefs::[String];
monoid attribute totalRefs::[String];
monoid attribute matchesFrame::Boolean with false, ||;
monoid attribute containsTraversal::Boolean with false, ||;

-- TODO: Merge these into a translation attribute
synthesized attribute partialTranslation<a>::a; -- Maybe<a> on a
synthesized attribute totalTranslation<a>::a; -- a on a, can raise a runtime error if demanded on partial strategy expression

-- Nonterminal-independent algebraic simplifications
-- Theoretically these could be applied to the strategy before lifting/propagation,
-- but probably not much of an improvement.
partial strategy attribute genericStep =
  rule on top::StrategyExpr of
  | sequence(fail(), _) -> fail(genName=top.genName)
  | sequence(_, fail()) -> fail(genName=top.genName)
  | sequence(id(), s) -> ^s
  | sequence(s, id()) -> ^s
  | choice(fail(), s) -> ^s
  | choice(s, fail()) -> ^s
  | choice(s, _) when s.isTotal -> ^s
  | allTraversal(id()) -> id(genName=top.genName)
  | someTraversal(fail()) -> fail(genName=top.genName)
  | oneTraversal(fail()) -> fail(genName=top.genName)
  | prodTraversal(_, ss) when ss.containsFail -> fail(genName=top.genName)
  | recComb(n, s) when !contains(n.name, s.freeRecVars) -> ^s
  | inlined(_, fail()) -> fail(genName=top.genName)
  end;
-- Nonterminal-dependent, production-independent optimizations
partial strategy attribute ntStep =
  rule on top::StrategyExpr of
  -- Only inline references to partial strategies, as inlining total
  -- strategies would not permit any additional simplification.
  | partialRef(n) when
      n.matchesFrame && n.attrDcl.isStrategy &&
      !contains(n.attrDcl.fullName, top.inlinedStrategies) &&
      null(n.attrDcl.givenRecVarNameEnv) &&
      !n.attrDcl.containsTraversal ->
    inlined(n, n.attrDcl.strategyExpr, genName=top.genName)
  | partialRef(n) when !n.matchesFrame -> fail(genName=top.genName)
  | inlined(n, _) when !n.matchesFrame -> fail(genName=top.genName)
  | inlined(n, id()) when n.matchesFrame -> id(genName=top.genName)
  | inlined(n1, totalRef(n2)) when n1.matchesFrame -> totalRef(^n2, genName=top.genName)
  end;
-- Production-dependent optimizations
partial strategy attribute prodStep =
  rule on top::StrategyExpr of
  | choice(s, _) when s.isTotalInProd -> ^s
  | allTraversal(s) when !attrMatchesChild(top.env, fromMaybe(s.genName, s.attrRefName), top.frame) -> id(genName=top.genName)
  | someTraversal(s) when !attrMatchesChild(top.env, fromMaybe(s.genName, s.attrRefName), top.frame) -> fail(genName=top.genName)
  | oneTraversal(s) when !attrMatchesChild(top.env, fromMaybe(s.genName, s.attrRefName), top.frame) -> fail(genName=top.genName)
  | prodTraversal(p, s) when p.lookupValue.fullName != top.frame.fullName -> fail(genName=top.genName)
  | rewriteRule(_, _, ml) when !ml.matchesFrame -> fail(genName=top.genName)
  end <+
  rewriteRule(id, id, elimInfeasibleMRules);
partial strategy attribute elimInfeasibleMRules =
  onceBottomUp(
    rule on top::MRuleList of
    | mRuleList_cons(h, _, t) when !h.matchesFrame -> ^t
    | mRuleList_cons(h, _, mRuleList_one(t)) when !t.matchesFrame -> mRuleList_one(^h)
    end);
attribute elimInfeasibleMRules occurs on MRuleList;

strategy attribute genericSimplify = innermost(genericStep);
strategy attribute ntSimplify =
  (sequence(ntSimplify, ntSimplify) <+
   choice(ntSimplify, ntSimplify) <+
   allTraversal(genericSimplify) <+
   someTraversal(genericSimplify) <+
   oneTraversal(genericSimplify) <+
   prodTraversal(id, genericSimplify) <+
   recComb(id, ntSimplify) <+
   inlined(id, ntSimplify) <+
   id) <*
  try((genericStep <+ ntStep) <* ntSimplify);
strategy attribute optimize =
  (sequence(optimize, ntSimplify) <+
   choice(optimize, optimize) <+
   allTraversal(genericSimplify) <+
   someTraversal(genericSimplify) <+
   oneTraversal(genericSimplify) <+
   prodTraversal(id, genericSimplify) <+
   recComb(id, optimize) <+
   inlined(id, optimize) <+
   id) <*
  try((genericStep <+ ntStep <+ prodStep) <* optimize);

tracked nonterminal StrategyExpr with
  config, grammarName, env, unparse, errors, frame, compiledGrammars, flowEnv, -- Normal expression stuff
  genName, outerAttr, isOutermost, recVarNameEnv, recVarTotalEnv, recVarTotalNoEnvEnv, liftedStrategies, attrRefName,
  isId, isFail, isTotal, isTotalNoEnv, freeRecVars, partialRefs, totalRefs, containsTraversal, -- Frame-independent attrs
  partialTranslation<Expr>, totalTranslation<Expr>, matchesFrame, isTotalInProd, -- Frame-dependent attrs
  inlinedStrategies, genericStep, ntStep, prodStep, genericSimplify, ntSimplify, optimize; -- Optimization stuff

tracked nonterminal StrategyExprs with
  config, grammarName, env, unparse, errors, compiledGrammars, flowEnv, -- Normal expression stuff
  outerAttr, recVarNameEnv, recVarTotalEnv, recVarTotalNoEnvEnv, givenInputElements, liftedStrategies, attrRefNames,
  containsFail, allId, allTotal, freeRecVars, partialRefs, totalRefs, containsTraversal, -- Frame-independent attrs
  inlinedStrategies, genericSimplify; -- Optimization stuff

flowtype StrategyExpr =
  decorate {env, grammarName, config, recVarNameEnv, recVarTotalEnv, outerAttr, isOutermost}, -- NOT frame
  forward {decorate},
  -- Normal expression stuff
  unparse {}, errors {decorate, compiledGrammars, flowEnv},
  -- Frame-independent attrs
  liftedStrategies {recVarNameEnv, recVarTotalNoEnvEnv, outerAttr, isOutermost}, isTotalNoEnv {recVarNameEnv, recVarTotalNoEnvEnv, outerAttr, isOutermost},
  attrRefName {recVarNameEnv}, isId {}, isFail {},
  isTotal {decorate}, freeRecVars {decorate}, partialRefs {decorate}, totalRefs {decorate}, containsTraversal {decorate, flowEnv},
  genericStep {decorate, inlinedStrategies}, genericSimplify {decorate, inlinedStrategies},
  -- Frame-dependent attrs
  partialTranslation {decorate, flowEnv, frame}, totalTranslation {decorate, flowEnv, frame}, matchesFrame {decorate, frame}, isTotalInProd {decorate, frame},
  ntStep {decorate, inlinedStrategies, frame}, prodStep {decorate, inlinedStrategies, frame},
  ntSimplify {decorate, inlinedStrategies, frame}, optimize {decorate, inlinedStrategies, frame};

flowtype StrategyExprs =
  decorate {env, grammarName, config, recVarNameEnv, recVarTotalEnv, outerAttr}, -- NOT frame
  forward {},
  -- Normal expression stuff
  -- Frame-independent attrs
  liftedStrategies {recVarNameEnv, recVarTotalNoEnvEnv, outerAttr},
  attrRefNames {env, recVarNameEnv, givenInputElements},
  containsFail {}, allId {}, allTotal {decorate, givenInputElements}, freeRecVars {decorate}, partialRefs {decorate}, totalRefs {decorate};

propagate grammarName, config, compiledGrammars, env, flowEnv, outerAttr, partialRefs, totalRefs, containsTraversal on StrategyExpr, StrategyExprs;
propagate errors on StrategyExpr, StrategyExprs excluding partialRef, totalRef, rewriteRule;
propagate containsFail, allId, allTotal on StrategyExprs;
propagate recVarNameEnv, recVarTotalEnv, recVarTotalNoEnvEnv, freeRecVars on StrategyExpr, StrategyExprs excluding recComb;
propagate inlinedStrategies on StrategyExpr, StrategyExprs excluding inlined;
propagate genericSimplify on StrategyExprs;
propagate genericStep, ntStep, prodStep, genericSimplify, ntSimplify, optimize on StrategyExpr;
propagate elimInfeasibleMRules on MRuleList;

-- Convert an expression of type a to Maybe<a>
fun asPartial Expr ::= e::Expr = Silver_Expr { silver:core:just($Expr{e}) };

-- Convert an expression of type Maybe<a> to a
fun asTotal Expr ::= t::Type e::Expr =
  Silver_Expr {
    let res::$TypeExpr{typerepTypeExpr(t)} =
        silver:core:error("Total result demanded when partial strategy failed")
    in silver:core:fromMaybe(res, $Expr{e})
    end
  };

aspect default production
top::StrategyExpr ::=
{
  -- At least 1 of these should be defined for every production:
  top.partialTranslation = asPartial(top.totalTranslation);
  top.totalTranslation = asTotal(top.frame.signature.outputElement.typerep, top.partialTranslation);
  
  top.attrRefName = nothing();
  top.matchesFrame := true; -- Consulted only when attrRefName is just(...)
  top.isId = false;
  top.isFail = false;
  top.isTotal = false;
  top.isTotalNoEnv = false;
  top.isTotalInProd = false;
}

-- Basic combinators
abstract production id
top::StrategyExpr ::=
{
  top.unparse = "id";
  propagate liftedStrategies;
  top.isId = true;
  top.isTotal = true;
  top.isTotalNoEnv = true;
  top.isTotalInProd = true;
  top.totalTranslation =
    if top.frame.signature.outputElement.typerep.isData
    then Silver_Expr { $name{top.frame.signature.outputElement.elementName} }
    else Silver_Expr { silver:core:new($name{top.frame.signature.outputElement.elementName}) };
}

abstract production fail
top::StrategyExpr ::=
{
  top.unparse = "fail";
  propagate liftedStrategies;
  top.isFail = true;
  top.partialTranslation = Silver_Expr { silver:core:nothing() };
}

abstract production sequence
top::StrategyExpr ::= s1::StrategyExpr s2::StrategyExpr
{
  top.unparse = s"(${s1.unparse} <* ${s2.unparse})";

  s1.frame = top.frame;
  s2.frame = top.frame;  -- CAUTION when using s2.frame: wrong prod, but same nt
  
  local s2Name::String = fromMaybe(top.genName ++ "_snd", s2.attrRefName);
  local s2Total::Boolean = attrIsTotal(top.env, s2Name); -- Can differ from s2.isTotal because we lift without env
  top.liftedStrategies :=
    s1.liftedStrategies ++
    if s2.attrRefName.isJust
    then []
    else [(s2Name, s2)];
  top.isTotal = s1.isTotal && s2.isTotal;
  top.isTotalNoEnv = s1.isTotalNoEnv && s2.isTotalNoEnv;
  top.isTotalInProd = s1.isTotalInProd && s2.isTotal;
  
  s1.isOutermost = false;
  s2.isOutermost = false;
  
  -- Equations for all inh attributes on the nt that we know about.
  -- This is safe because the MWDA requires that all inh dependencies of a syn attribute
  -- be exported by the syn occurence anyway.
  -- TODO - future optimization potential: this is where common sub-trees shared between
  -- the incoming tree and the result of s1 get re-decorated.
  nondecorated local allInhs::ExprInhs =
    foldr(
      exprInhsCons(_, _),
      exprInhsEmpty(),
      map(
        \ attr::String ->
          -- TODO: translation attributes!
          Silver_ExprInh {
            $name{attr} = $name{top.frame.signature.outputElement.elementName}.$name{attr};
          },
        getInhAttrsOn(top.frame.lhsNtName, top.env)));
  top.partialTranslation =
    -- Optimizations when one or both of these is total, in this case a
    -- monadic bind may not be required.
    case s1.isTotalInProd, s2Total of
    | true, true ->
      Silver_Expr {
        silver:core:just(decorate $Expr{s1.totalTranslation} with { $ExprInhs{allInhs} }.$name{s2Name})
      }
    | true, false ->
      Silver_Expr {
        decorate $Expr{s1.totalTranslation} with { $ExprInhs{allInhs} }.$name{s2Name}
      }
    | false, true ->
      Silver_Expr {
        silver:core:map(
          \ res::$TypeExpr{typerepTypeExpr(top.frame.signature.outputElement.typerep)} ->
            decorate res with { $ExprInhs{allInhs} }.$name{s2Name},
          $Expr{s1.partialTranslation})
      }
    | false, false ->
      Silver_Expr {
        silver:core:bind(
          $Expr{s1.partialTranslation},
          \ res::$TypeExpr{typerepTypeExpr(top.frame.signature.outputElement.typerep)} ->
            decorate res with { $ExprInhs{allInhs} }.$name{s2Name})
      }
    end;
  nondecorated local totalTrans::Expr =
    Silver_Expr {
      decorate $Expr{s1.totalTranslation} with { $ExprInhs{allInhs} }.$name{s2Name}
    };
  top.totalTranslation = if s2Total then totalTrans else asTotal(top.frame.signature.outputElement.typerep, totalTrans);
}

abstract production choice
top::StrategyExpr ::= s1::StrategyExpr s2::StrategyExpr
{
  top.unparse = s"(${s1.unparse} <+ ${s2.unparse})";
  propagate frame, liftedStrategies;
  top.isTotal = s1.isTotal || s2.isTotal;
  top.isTotalNoEnv = s1.isTotalNoEnv || s2.isTotalNoEnv;
  top.isTotalInProd = s1.isTotalInProd || s2.isTotalInProd;
  
  s1.isOutermost = false;
  s2.isOutermost = false;
  
  top.partialTranslation =
    Silver_Expr {
      silver:core:orElse($Expr{s1.partialTranslation}, $Expr{s2.partialTranslation})
    };
  top.totalTranslation =
    if s1.isTotalInProd
    then s1.totalTranslation
    else 
      Silver_Expr {
        silver:core:fromMaybe($Expr{s2.totalTranslation}, $Expr{s1.partialTranslation})
      };
}

-- Traversals
abstract production allTraversal
top::StrategyExpr ::= s::StrategyExpr
{
  top.unparse = s"all(${s.unparse})";
  
  local sName::String = fromMaybe(top.genName ++ "_all_arg", s.attrRefName);
  local sTotal::Boolean = attrIsTotal(top.env, sName); -- Can differ from s.isTotal because we lift without env
  top.liftedStrategies :=
    if s.attrRefName.isJust
    then []
    else [(sName, s)];
  top.isTotal = s.isTotal;
  top.isTotalNoEnv = s.isTotalNoEnv;
  top.isTotalInProd = s.isTotal;

  top.containsTraversal <- true;

  s.isOutermost = false;
  
  local sBaseName::String = last(explode(":", sName));
  -- (child name, child decorable, attr occurs on child)
  local childAccesses::[(String, Boolean, Boolean)] =
    map(
      \ e::NamedSignatureElement ->
        (e.elementName, isDecorable(e.typerep, top.env), attrMatchesFrame(top.env, sName, e.typerep)),
      top.frame.signature.inputElements);
  top.partialTranslation =
    if sTotal
    then asPartial(top.totalTranslation)
    else
      {- Translation of all(s) for prod::(Foo ::= a::Foo b::Integer c::Bar):
           case a.s, c.s of
           | just(a_s), just(c_s) -> just(prod(a_s, b, c_s))
           | _, _ -> nothing()
           end
         Could also be implemented as chained monadic binds.  Maybe more efficient this way? -}
      caseExpr(
        flatMap(
          \ a::(String, Boolean, Boolean) ->
            if a.3 then [Silver_Expr { $name{a.1}.$name{sName} }] else [],
          childAccesses),
        [matchRule(
           flatMap(
             \ a::(String, Boolean, Boolean) ->
               if a.3
               then
                 [decorate Silver_Pattern { silver:core:just($name{a.1 ++ "_" ++ sBaseName}) }
                  with { grammarName = top.grammarName; config = top.config; env = top.env; frame = top.frame; patternVarEnv = []; }]
               else [],
             childAccesses),
           nothing(),
           Silver_Expr {
             silver:core:just(
               $Expr{
                 mkFullFunctionInvocation(
                   baseExpr(qName(top.frame.fullName)),
                   map(
                     \ a::(String, Boolean, Boolean) ->
                       if a.3
                       then Silver_Expr { $name{a.1 ++ "_" ++ sBaseName} }
                       else if a.2
                       then Silver_Expr { silver:core:new($name{a.1}) }
                       else Silver_Expr { $name{a.1} },
                     childAccesses),
                   map(
                     makeAnnoArg(top.frame.signature.outputElement.elementName, _),
                     top.frame.signature.namedInputElements))})
           })],
        false,
        Silver_Expr { silver:core:nothing() },
        appType(nonterminalType("silver:core:Maybe", [starKind()], true, false), top.frame.signature.outputElement.typerep));
  top.totalTranslation =
    if sTotal
    then
      {- When s is total, optimized translation of all(s) for prod::(Foo ::= a::Foo b::Integer c::Bar):
           prod(a.s, b, c.s) -}
       mkFullFunctionInvocation(
         baseExpr(qName(top.frame.fullName)),
         map(
           \ a::(String, Boolean, Boolean) ->
             if a.3
             then Silver_Expr { $name{a.1}.$name{sName} }
             else if a.2
             then Silver_Expr { silver:core:new($name{a.1}) }
             else Silver_Expr { $name{a.1} },
           childAccesses),
         map(
           makeAnnoArg(top.frame.signature.outputElement.elementName, _),
           top.frame.signature.namedInputElements))
    else asTotal(top.frame.signature.outputElement.typerep, top.partialTranslation);
}

abstract production someTraversal
top::StrategyExpr ::= s::StrategyExpr
{
  top.unparse = s"some(${s.unparse})";
  
  local sName::String = fromMaybe(top.genName ++ "_some_arg", s.attrRefName);
  local sTotal::Boolean = attrIsTotal(top.env, sName); -- Can differ from s.isTotal because we lift without env
  top.liftedStrategies :=
    if s.attrRefName.isJust
    then []
    else [(sName, s)];
  top.isTotalInProd = s.isTotal && !null(matchingChildren);
  
  top.containsTraversal <- true;

  s.isOutermost = false;
  
  -- (child name, child decorable, attr occurs on child)
  local childAccesses::[(String, Boolean, Boolean)] =
    map(
      \ e::NamedSignatureElement ->
        (e.elementName, isDecorable(e.typerep, top.env), attrMatchesFrame(top.env, sName, e.typerep)),
      top.frame.signature.inputElements);
  local matchingChildren::[String] = map(fst, filter(\ a::(String, Boolean, Boolean) -> a.3, childAccesses));
  top.partialTranslation =
    if sTotal
    then
      if !null(matchingChildren)
      then asPartial(top.totalTranslation)
      else Silver_Expr { silver:core:nothing() }
    else
      {- Translation of some(s) for prod::(Foo ::= a::Foo b::Integer c::Bar):
           if a.s.isJust || c.s.isJust
           then just(prod(fromMaybe(a, a.s), b, fromMaybe(c, c.s)))
           else nothing()
         Not sure of a clean way to do this with monads -}
      Silver_Expr {
        if $Expr{
          foldr(
            or(_, '||', _),
            falseConst('false'),
            map(
              \ a::String -> Silver_Expr { $name{a}.$name{sName}.isJust },
              matchingChildren))}
        then
          silver:core:just(
            $Expr{
              mkFullFunctionInvocation(
                baseExpr(qName(top.frame.fullName)),
                map(
                  \ a::(String, Boolean, Boolean) ->
                    let defaultRes::Expr =
                      if a.2
                      then Silver_Expr { silver:core:new($name{a.1}) }
                      else Silver_Expr { $name{a.1} }
                    in
                      if a.3
                      then Silver_Expr { silver:core:fromMaybe($Expr{defaultRes}, $name{a.1}.$name{sName}) }
                      else defaultRes
                    end,
                  childAccesses),
                map(
                  makeAnnoArg(top.frame.signature.outputElement.elementName, _),
                  top.frame.signature.namedInputElements))})
        else silver:core:nothing()
      };
  top.totalTranslation =
    if sTotal && !null(matchingChildren)
    then
      {- When s is total, optimized translation of all(s) for prod::(Foo ::= a::Foo b::Integer c::Bar):
           prod(a.s, b, c.s) -}
       mkFullFunctionInvocation(
         baseExpr(qName(top.frame.fullName)),
         map(
           \ a::(String, Boolean, Boolean) ->
             if a.3
             then Silver_Expr { $name{a.1}.$name{sName} }
             else if a.2
             then Silver_Expr { silver:core:new($name{a.1}) }
             else Silver_Expr { $name{a.1} },
           childAccesses),
         map(
           makeAnnoArg(top.frame.signature.outputElement.elementName, _),
           top.frame.signature.namedInputElements))
    else asTotal(top.frame.signature.outputElement.typerep, top.partialTranslation);
}

abstract production oneTraversal
top::StrategyExpr ::= s::StrategyExpr
{
  top.unparse = s"one(${s.unparse})";
  
  local sName::String = fromMaybe(top.genName ++ "_one_arg", s.attrRefName);
  local sTotal::Boolean = attrIsTotal(top.env, sName); -- Can differ from s.isTotal because we lift without env
  top.liftedStrategies :=
    if s.attrRefName.isJust
    then []
    else [(sName, s)];
  top.isTotalInProd = s.isTotal && !null(matchingChildren);

  top.containsTraversal <- true;
  
  s.isOutermost = false;
  
  local sBaseName::String = last(explode(":", sName));
  -- (child name, child decorable, attr occurs on child)
  local childAccesses::[(String, Boolean, Boolean)] =
    map(
      \ e::NamedSignatureElement ->
        (e.elementName, isDecorable(e.typerep, top.env), attrMatchesFrame(top.env, sName, e.typerep)),
      top.frame.signature.inputElements);
  local matchingChildren::[String] = map(fst, filter(\ a::(String, Boolean, Boolean) -> a.3, childAccesses));
  top.partialTranslation =
    if sTotal
    then
      if !null(matchingChildren)
      then asPartial(top.totalTranslation)
      else Silver_Expr { silver:core:nothing() }
    else
      {- Translation of one(s) for prod::(Foo ::= a::Foo b::Integer c::Bar):
           case a.s, c.s of
           | just(a_s), _ -> just(prod(a_s, b, c))
           | _, just(c_s) -> just(prod(a, b, c_s))
           | _, _ -> nothing()
           end
         Could also be implemented as
           orElse(
             bind(a.s, \ a_s::Foo -> pure(prod(a_s, b, c))),
             bind(c.s, \ c_s::Bar -> pure(prod(a, b, c_s)))  -}
      caseExpr(
        map(
          \ a::String -> Silver_Expr { $name{a}.$name{sName} },
          matchingChildren),
        map(
          \ i::Integer ->
            let childI::String = head(drop(i, matchingChildren))
            in let childIndex::Integer = positionOf(childI, map(fst, childAccesses))
            in 
              matchRule(
                map(
                  \ p::Pattern -> decorate p with { grammarName = top.grammarName; config = top.config; env = top.env; frame = top.frame; patternVarEnv = []; },
                  repeat(wildcPattern('_'), i) ++
                  Silver_Pattern { silver:core:just($name{childI ++ "_" ++ sBaseName}) } ::
                  repeat(wildcPattern('_'), length(matchingChildren) - (i + 1))),
                nothing(),
                Silver_Expr {
                  silver:core:just(
                    $Expr{
                      mkFullFunctionInvocation(
                        baseExpr(qName(top.frame.fullName)),
                        map(
                          \ a::(String, Boolean, Boolean) ->
                            if a.2
                            then Silver_Expr { silver:core:new($name{a.1}) }
                            else Silver_Expr { $name{a.1} },
                          take(childIndex, childAccesses)) ++
                        Silver_Expr { $name{childI ++ "_" ++ sBaseName} } ::
                        map(
                          \ a::(String, Boolean, Boolean) ->
                            if a.2
                            then Silver_Expr { silver:core:new($name{a.1}) }
                            else Silver_Expr { $name{a.1} },
                          drop(childIndex + 1, childAccesses)),
                        map(
                          makeAnnoArg(top.frame.signature.outputElement.elementName, _),
                          top.frame.signature.namedInputElements))})
                })
            end end,
            range(0, length(matchingChildren))),
        false,
        Silver_Expr { silver:core:nothing() },
        appType(nonterminalType("silver:core:Maybe", [starKind()], true, false), top.frame.signature.outputElement.typerep));
  top.totalTranslation =
    if sTotal && !null(matchingChildren)
    then
      {- When s is total, optimized translation of one(s) for prod::(Foo ::= a::Foo b::Integer c::Bar):
           prod(a.s, b, c) -}
      mkFullFunctionInvocation(
        baseExpr(qName(top.frame.fullName)),
        map(
          \ a::(String, Boolean, Boolean) ->
            if a.1 == head(matchingChildren)
            then Silver_Expr { $name{a.1}.$name{sName} }
            else if a.2
            then Silver_Expr { silver:core:new($name{a.1}) }
            else Silver_Expr { $name{a.1} },
          childAccesses),
        map(
          makeAnnoArg(top.frame.signature.outputElement.elementName, _),
          top.frame.signature.namedInputElements))
    else asTotal(top.frame.signature.outputElement.typerep, top.partialTranslation);
}

abstract production prodTraversal
top::StrategyExpr ::= prod::QName s::StrategyExprs
{
  top.unparse = s"${prod.unparse}(${s.unparse})";
  
  top.errors <- prod.lookupValue.errors;
  
  local numParams::Integer = length(s.givenInputElements);
  local numArgs::Integer = length(s.attrRefNames);
  top.errors <-
    if prod.lookupValue.found && numArgs != numParams
    then [errFromOrigin(top,   s"Wrong number of arguments to ${prod.name}: expected ${toString(numParams)}, got ${toString(numArgs)}")]
    else [];
  
  propagate liftedStrategies;

  top.isTotalInProd = prod.lookupValue.fullName == top.frame.fullName && s.allTotal;
  
  s.givenInputElements =
    if prod.lookupValue.found
    then prod.lookupValue.dcl.namedSignature.inputElements
    else [];
  
  top.containsTraversal <- true;
  
  -- (child name, child decorable, if attr occurs on child then just(attr name) else nothing())
  local childAccesses::[(String, Boolean, Maybe<String>)] = zip3(
    top.frame.signature.inputNames,
    map(isDecorable(_, top.env), top.frame.signature.inputTypes),
    s.attrRefNames);
  top.partialTranslation = -- This is never total
    if prod.lookupValue.fullName == top.frame.fullName
    then
      {- Translation of prod(s1, s2, s3, s4) for prod::(Foo ::= a::Foo b::Integer c::Bar d::Baz)
         where s4 is total:
           case a.s1, c.s3 of
           | just(a_s1), just(c_s3) -> just(prod(a_s1, b, c_s3, d.s4))
           | _, _ -> nothing()
           end
         Could also be implemented using the Applicative instance for Maybe.  Maybe more efficient this way? -}
      caseExpr(
        flatMap(
          \ a::(String, Boolean, Maybe<String>) ->
            case a.3 of
            | just(attr) when !attrIsTotal(top.env, attr) -> [Silver_Expr { $name{a.1}.$name{attr} }]
            | _ -> []
            end,
          childAccesses),
        [matchRule(
           flatMap(
             \ a::(String, Boolean, Maybe<String>) ->
               case a.3 of
               | just(attr) when !attrIsTotal(top.env, attr)  ->
                 [decorate Silver_Pattern { silver:core:just($name{a.1 ++ "_" ++ last(explode(":", attr))}) }
                  with { grammarName = top.grammarName; config = top.config; env = top.env; frame = top.frame; patternVarEnv = []; }]
               | _ -> []
               end,
             childAccesses),
           nothing(),
           Silver_Expr {
             silver:core:just(
               $Expr{
                 mkFullFunctionInvocation(
                   baseExpr(qName(top.frame.fullName)),
                   map(
                     \ a::(String, Boolean, Maybe<String>) ->
                       case a.3 of
                       | just(attr) when attrIsTotal(top.env, attr) -> Silver_Expr { $name{a.1}.$name{attr} }
                       | just(attr) -> Silver_Expr { $name{a.1 ++ "_" ++ last(explode(":", attr))} }
                       | nothing() ->
                          if a.2
                          then Silver_Expr { silver:core:new($name{a.1}) }
                          else Silver_Expr { $name{a.1} }
                       end,
                     childAccesses),
                   map(
                     makeAnnoArg(top.frame.signature.outputElement.elementName, _),
                     top.frame.signature.namedInputElements))})
           })],
        false,
        Silver_Expr { silver:core:nothing() },
        appType(nonterminalType("silver:core:Maybe", [starKind()], true, false), top.frame.signature.outputElement.typerep))
    else Silver_Expr { silver:core:nothing() };
}

abstract production consStrategyExpr
top::StrategyExprs ::= h::StrategyExpr t::StrategyExprs
{
  top.unparse = s"${h.unparse}, ${t.unparse}";
   
  top.liftedStrategies :=
    -- Slight hack: when h is id (common case for prod traversals), there is no need for a new attribute.
    -- However this can't be avoided during the optimization phase, which happens after lifting.
    -- So, just don't lift the strategy, and we won't find the occurence of the non-existant attribute
    -- during translation - which means we will treat it as id anyway!
    (if h.attrRefName.isJust || h.isId
     then []
     else [(h.genName, h)]) ++
    t.liftedStrategies;
  
  nondecorated local hType::Type = head(top.givenInputElements).typerep;
  local attr::String = fromMaybe(h.genName, h.attrRefName);
  local attrMatch::Boolean = attrMatchesFrame(top.env, attr, hType);
  top.attrRefNames =
   (if !null(top.givenInputElements) && attrMatch && !h.isId
    then just(attr)
    else nothing()) :: t.attrRefNames;
  top.errors <-
    if !null(top.givenInputElements) && !attrMatch && !h.isId
    then [wrnFromOrigin(h, s"This (non-identity) strategy attribute does not occur on ${prettyType(hType)} and will be treated as identity")]
    else [];
  
  top.containsFail <- h.isFail;
  top.allId <- h.isId;
  top.allTotal <- !null(top.givenInputElements) && attrMatch && h.isTotal;
  
  h.isOutermost = false;
  t.givenInputElements =
    if !null(top.givenInputElements) then tail(top.givenInputElements) else [];
}

abstract production nilStrategyExpr
top::StrategyExprs ::=
{
  top.unparse = "";
  top.liftedStrategies := [];
  top.attrRefNames = [];
}

-- Recursive strategies
abstract production recComb
top::StrategyExpr ::= n::Name s::StrategyExpr
{
  top.unparse = s"rec ${n.name} -> (${s.unparse})";
  
  local sName::String = if top.isOutermost then top.outerAttr else top.genName ++ "_rec_body";
  top.liftedStrategies :=
    if top.isOutermost
    then s.liftedStrategies
    else [(sName, s)];
  top.freeRecVars := remove(n.name, s.freeRecVars);

  -- Decorate s assuming that the bound strategy is total, in order to check for totality.
  -- See Fig 4 of the strategy attributes paper (https://www-users.cse.umn.edu/~evw/pubs/kramer20sle/kramer20sle.pdf)
  local s2::StrategyExpr = ^s;
  s2.recVarTotalEnv = (n.name, true) :: s.recVarTotalEnv;
  s2.recVarTotalNoEnvEnv = (n.name, true) :: s.recVarTotalNoEnvEnv;
  s2.frame = s.frame;
  s2.env = s.env;
  s2.config = s.config;
  s2.grammarName = s.grammarName;
  s2.recVarNameEnv = s.recVarNameEnv;
  s2.outerAttr = s.outerAttr;
  s2.isOutermost = top.isOutermost;
  top.isTotal = s2.isTotal;
  top.isTotalNoEnv = s2.isTotalNoEnv;
  top.isTotalInProd = s2.isTotalInProd;
  
  s.frame = top.frame;
  s.recVarNameEnv = (n.name, sName) :: top.recVarNameEnv;
  s.recVarTotalEnv = (n.name, top.isTotal) :: top.recVarTotalEnv;
  s.recVarTotalNoEnvEnv = (n.name, top.isTotalNoEnv) :: top.recVarTotalNoEnvEnv;
  s.isOutermost = top.isOutermost;
  
  local sTotal::Boolean = attrIsTotal(top.env, sName);
  top.partialTranslation =
    if top.isOutermost
    then s.partialTranslation
    else if sTotal
    then asPartial(top.totalTranslation)
    else Silver_Expr { $name{top.frame.signature.outputElement.elementName}.$name{sName} };
  top.totalTranslation =
    if top.isOutermost
    then s.totalTranslation
    else if sTotal
    then Silver_Expr { $name{top.frame.signature.outputElement.elementName}.$name{sName} }
    else asTotal(top.frame.signature.outputElement.typerep, top.partialTranslation);
}

-- Rules
abstract production rewriteRule
top::StrategyExpr ::= id::Name ty::TypeExpr ml::MRuleList
{
  top.unparse = "rule on " ++ id.name ++ "::" ++ ty.unparse ++ " of " ++ ml.unparse ++ " end";
  propagate frame, liftedStrategies;

  top.isTotalInProd = ml.isTotalInProd;
  
  -- Pattern matching error checking (mostly) happens on what caseExpr forwards to,
  -- so we need to decorate one of those here.
  production checkExpr::Expr =
    caseExpr(
      [hackLHSExprType(ty.typerep.asDecoratedType)],
      -- TODO: matchRuleList on MRuleList depends on frame for some reason.
      -- Re-decorate ml here as a workaround to avoid checkExpr depending on top.frame
      decorate ^ml with {
        env = top.env;
        config = top.config;
        grammarName = top.grammarName; 
        matchRulePatternSize = 1;
        frame = error("not needed");
      }.matchRuleList, false,
      errorExpr([]),
      ty.typerep);
  checkExpr.env =
    newScopeEnv([lhsDef(top.grammarName, id.nameLoc, id.name, ty.typerep)], top.env);
  checkExpr.flowEnv = top.flowEnv;
  checkExpr.decSiteVertexInfo = nothing();
  checkExpr.alwaysDecorated = false;
  checkExpr.appDecSiteVertexInfo = nothing();
  checkExpr.dispatchFlowDeps = [];
  checkExpr.downSubst = emptySubst();
  checkExpr.downSubst2 = checkExpr.upSubst;
  checkExpr.finalSubst = checkExpr.upSubst2;
  checkExpr.grammarName = top.grammarName;
  checkExpr.config = top.config;
  checkExpr.compiledGrammars = top.compiledGrammars;
  checkExpr.originRules = [];
  checkExpr.isRoot = false;

  -- Frame doesn't really matter, since we will re-check any expressions occuring in ml when propagated.
  -- Need all this to construct a bogus frame...
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myProds :: EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;
  local myFlowGraph :: ProductionGraph = constructAnonymousGraph(checkExpr.flowDefs, top.env, myProds, myFlow);
  checkExpr.frame = bogusContext(myFlowGraph, sourceGrammar=top.grammarName);
  
  top.errors := checkExpr.errors;
  top.errors <-
    if !isDecorable(ty.typerep, top.env)
    then [wrnFromOrigin(ty, "Only rules on nonterminals can have an effect")]
    else [];
  top.errors <- ty.errorsKindStar;
  
  nondecorated local partialRes::Expr =
    caseExpr(
      [Silver_Expr { $name{top.frame.signature.outputElement.elementName} }],
      ml.partialTranslation, false,
      Silver_Expr { silver:core:nothing() },
      appType(nonterminalType("silver:core:Maybe", [starKind()], true, false), ty.typerep));
  top.partialTranslation =
    if unify(ty.typerep, top.frame.signature.outputElement.typerep).failure
    then Silver_Expr { silver:core:nothing() }
    else if top.frame.signature.outputElement.elementName == id.name
    then partialRes
    else if top.frame.signature.outputElement.typerep.isData
    then Silver_Expr {
      let $Name{^id}::$TypeExpr{^ty} = $name{top.frame.signature.outputElement.elementName}
      in $Expr{partialRes}
      end
    }
    else Silver_Expr {
      let $Name{^id}::$TypeExpr{typerepTypeExpr(ty.typerep.asDecoratedType)} =
        $name{top.frame.signature.outputElement.elementName}
      in $Expr{partialRes}
      end
    };
    nondecorated local totalRes::Expr =
      caseExpr(
        [Silver_Expr { $name{top.frame.signature.outputElement.elementName} }],
        ml.totalTranslation, false,
        Silver_Expr {
          silver:core:error(
            "Internal error: total rule did not match: " ++
            $Expr{stringConst(terminal(String_t, s"\"${escapeString(top.unparse)}\""))})
        },
        ty.typerep);
    top.totalTranslation =
      if top.frame.signature.outputElement.elementName == id.name
      then totalRes
      else if top.frame.signature.outputElement.typerep.isData
      then Silver_Expr {
        let $Name{^id}::$TypeExpr{^ty} = $name{top.frame.signature.outputElement.elementName}
        in $Expr{totalRes}
        end
      }
      else Silver_Expr {
        let $Name{^id}::$TypeExpr{typerepTypeExpr(ty.typerep.asDecoratedType)} =
          $name{top.frame.signature.outputElement.elementName}
        in $Expr{totalRes}
        end
      };
}

-- Hack dummy expr with a given type
abstract production hackLHSExprType
top::Expr ::= t::Type
{
  top.typerep = ^t;
  top.flowVertexInfo = just(lhsVertexType);
  forwards to errorExpr([]);
}

attribute matchesFrame occurs on MRuleList, MatchRule, PatternList, Pattern;
propagate matchesFrame on MRuleList, MatchRule, PatternList excluding matchRuleWhenMatches_c;

attribute isTotalInProd occurs on MRuleList, MatchRule, PatternList, Pattern;

attribute partialTranslation<[AbstractMatchRule]>, totalTranslation<[AbstractMatchRule]> occurs on MRuleList;

aspect production mRuleList_one
top::MRuleList ::= m::MatchRule
{
  top.partialTranslation = [m.partialTranslation];
  top.totalTranslation = [m.totalTranslation];
  top.isTotalInProd = m.isTotalInProd;
}

aspect production mRuleList_cons
top::MRuleList ::= h::MatchRule '|' t::MRuleList
{
  top.partialTranslation = h.partialTranslation :: t.partialTranslation;
  top.totalTranslation = h.totalTranslation :: t.totalTranslation;
  top.isTotalInProd = h.isTotalInProd && t.isTotalInProd;
}

attribute partialTranslation<AbstractMatchRule>, totalTranslation<AbstractMatchRule> occurs on MatchRule;

aspect production matchRule_c
top::MatchRule ::= pt::PatternList _ e::Expr
{
  top.partialTranslation =
    matchRule(
      pt.patternList, nothing(), Silver_Expr { silver:core:just($Expr{^e}) });
  top.totalTranslation = matchRule(pt.patternList, nothing(), ^e);
  top.isTotalInProd = pt.isTotalInProd;
}

aspect production matchRuleWhen_c
top::MatchRule ::= pt::PatternList 'when' cond::Expr _ e::Expr
{
  top.partialTranslation =
    matchRule(
      pt.patternList, just((^cond, nothing())), Silver_Expr { silver:core:just($Expr{^e}) });
  top.totalTranslation = matchRule(pt.patternList, just((^cond, nothing())), ^e);
  top.isTotalInProd = false;
}

aspect production matchRuleWhenMatches_c
top::MatchRule ::= pt::PatternList 'when' cond::Expr 'matches' p::Pattern _ e::Expr
{
  top.partialTranslation =
    matchRule(
      pt.patternList, just((^cond, just(^p))), Silver_Expr { silver:core:just($Expr{^e}) });
  top.totalTranslation = matchRule(pt.patternList, just((^cond, just(^p))), ^e);
  top.matchesFrame := pt.matchesFrame;
  top.isTotalInProd = false;
}

aspect matchesFrame on top::Pattern using := of
| prodAppPattern_named(prod, _, _, _, _, _) -> prod.lookupValue.fullName == top.frame.fullName
| _ -> true
end;

aspect isTotalInProd on PatternList of
| patternList_one(p) -> p.isTotalInProd
| patternList_more(p, _, _) -> p.isTotalInProd
| patternList_nil() -> false
end;

aspect isTotalInProd on top::Pattern of
| prodAppPattern_named(prod, _, ps, _, nps, _) ->
    prod.lookupValue.fullName == top.frame.fullName && ps.allWildcards && nps.allWildcards
| wildcPattern(_) -> true
| varPattern(_) -> true
| _ -> false
end;

monoid attribute allWildcards::Boolean with true, && occurs on PatternList, NamedPatternList, NamedPattern, Pattern;
propagate allWildcards on PatternList, NamedPatternList, NamedPattern;

aspect allWildcards on Pattern using := of
| wildcPattern(_) -> true
| varPattern(_) -> true
| _ -> false
end;

-- References to other attributes or rec variables
abstract production nameRef
top::StrategyExpr ::= id::QName
{
  top.unparse = id.unparse;
  propagate env;
  
  -- Forwarding depends on env here, these must be computed without env
  propagate liftedStrategies;
  top.attrRefName = just(fromMaybe(id.name, lookup(id.name, top.recVarNameEnv)));
  top.isId = false;
  top.isFail = false;
  top.isTotalNoEnv = fromMaybe(false, lookup(id.name, top.recVarTotalNoEnvEnv));
  
  nondecorated local attrDcl::AttributeDclInfo = id.lookupAttribute.dcl;
  forwards to
    if lookup(id.name, top.recVarNameEnv).isJust
    then recVarRef(id, genName=top.genName)
    else if !null(id.lookupAttribute.errors)
    then errorRef(id.lookupAttribute.errors, id, genName=top.genName)
    else if attrIsTotal(top.env, id.name)
    then totalRef(qNameAttrOccur(@id), genName=top.genName)
    else partialRef(qNameAttrOccur(@id), genName=top.genName);
}
abstract production errorRef
top::StrategyExpr ::= msg::[Message] id::Decorated QName
{
  top.unparse = id.unparse;
  
  propagate liftedStrategies;
  top.attrRefName = just(id.name);
  
  top.errors <- msg;
  top.partialTranslation = Silver_Expr { silver:core:nothing() };
}
abstract production recVarRef
top::StrategyExpr ::= id::Decorated QName
{
  top.unparse = id.unparse;
  
  propagate liftedStrategies;
  top.attrRefName = lookup(id.name, top.recVarNameEnv);
  top.isTotal = lookup(id.name, top.recVarTotalEnv).fromJust;
  top.freeRecVars <- [id.name];
  
  top.partialTranslation =
    if attrIsTotal(top.env, top.attrRefName.fromJust)
    then asPartial(top.totalTranslation)
    else Silver_Expr { $name{top.frame.signature.outputElement.elementName}.$qName{top.attrRefName.fromJust} };
  top.totalTranslation =
    if attrIsTotal(top.env, top.attrRefName.fromJust)
    then Silver_Expr { $name{top.frame.signature.outputElement.elementName}.$qName{top.attrRefName.fromJust} }
    else asTotal(top.frame.signature.outputElement.typerep, top.partialTranslation);
}
abstract production partialRef
top::StrategyExpr ::= attr::QNameAttrOccur
{
  top.unparse = attr.unparse;
  
  -- Lookup for error checking is *not* contextual, since we don't know the frame here
  production attrDclFound::Boolean = case attr of qNameAttrOccur(a) -> a.lookupAttribute.found end;
  production attrDcl::AttributeDclInfo = case attr of qNameAttrOccur(a) -> a.lookupAttribute.dcl end;
  local attrTypeScheme::PolyType = attrDcl.typeScheme;
  top.errors :=
    if !attrDcl.isSynthesized
    then [errFromOrigin(attr,   s"Attribute ${attr.name} cannot be used as a partial strategy, because it is not a synthesized attribute")]
    else case attrTypeScheme.typerep, attrTypeScheme.boundVars of
    | appType(nonterminalType("silver:core:Maybe", _, _, _), varType(a1)), [a2] when a1 == a2 && attrDcl.isSynthesized -> []
    | appType(nonterminalType("silver:core:Maybe", _, _, _), a), _
        when (a.baseType, attrDcl.isSynthesized) matches (nonterminalType(nt, _, _, _), true) ->
      if null(getOccursDcl(attrDcl.fullName, nt, top.env))
      then [wrnFromOrigin(attr, s"Attribute ${attr.name} cannot be used as a partial strategy, because it doesn't occur on its own nonterminal type ${nt}")]
      else []
    | errorType(), _ -> []
    | _, _ -> [errFromOrigin(attr,   s"Attribute ${attr.name} cannot be used as a partial strategy")]
    end;
  
  propagate liftedStrategies;
  top.attrRefName = just(attr.name);
  top.matchesFrame := attr.matchesFrame;
  top.isTotal = false;
  top.partialRefs <- [attrDcl.fullName];
  
  attr.attrFor = top.frame.signature.outputElement.typerep;
  
  top.partialTranslation =
    if attr.matchesFrame
    then Silver_Expr { $name{top.frame.signature.outputElement.elementName}.$QNameAttrOccur{^attr} }
    else Silver_Expr { silver:core:nothing() };
}
abstract production totalRef
top::StrategyExpr ::= attr::QNameAttrOccur
{
  top.unparse = attr.unparse;
  
  -- Lookup for error checking is *not* contextual, since we don't know the frame here
  production attrDclFound::Boolean = case attr of qNameAttrOccur(a) -> a.lookupAttribute.found end;
  production attrDcl::AttributeDclInfo = case attr of qNameAttrOccur(a) -> a.lookupAttribute.dcl end;
  local attrTypeScheme::PolyType = attrDcl.typeScheme;
  top.errors :=
    if !attrDcl.isSynthesized
    then [errFromOrigin(attr,   s"Attribute ${attr.name} cannot be used as a total strategy, because it is not a synthesized attribute")]
    else case attrTypeScheme.typerep.baseType, attrTypeScheme.boundVars of
    | varType(a1), [a2] when a1 == a2 -> []
    | nonterminalType(nt, _, _, _), _ ->
      if null(getOccursDcl(attrDcl.fullName, nt, top.env))
      then [wrnFromOrigin(attr, s"Attribute ${attr.name} cannot be used as a total strategy, because it doesn't occur on its own nonterminal type ${nt}")]
      else []
    | errorType(), _ -> []
    | _, _ -> [errFromOrigin(attr,   s"Attribute ${attr.name} cannot be used as a total strategy")]
    end;
  
  propagate liftedStrategies;
  top.attrRefName = just(attr.name);
  top.matchesFrame := attr.matchesFrame;
  top.isTotal = true;
  top.isTotalNoEnv = true;
  top.isTotalInProd = true;
  top.totalRefs <- [attrDcl.fullName];
  
  attr.attrFor = top.frame.signature.outputElement.typerep;
  
  top.totalTranslation = Silver_Expr { $name{top.frame.signature.outputElement.elementName}.$QNameAttrOccur{^attr} };
}

-- The result of performing an inlining optimization
abstract production inlined
top::StrategyExpr ::= attr::Decorated QNameAttrOccur s::StrategyExpr
{
  top.unparse = s"(${s.unparse} aka ${attr.unparse})";
  propagate frame, liftedStrategies;
  top.attrRefName = just(attr.attrDcl.fullName);
  top.isTotal = s.isTotal;
  top.isTotalInProd = s.isTotalInProd;
  top.partialTranslation =
    if attr.matchesFrame
    then s.partialTranslation
    else Silver_Expr { silver:core:nothing() };
  top.totalTranslation = s.totalTranslation;
  
  s.isOutermost = top.isOutermost;
  s.inlinedStrategies = attr.attrDcl.fullName :: top.inlinedStrategies;
}

attribute matchesFrame occurs on QNameAttrOccur;

aspect production qNameAttrOccur
top::QNameAttrOccur ::= at::QName
{
  top.matchesFrame := top.found &&
    case top.typerep of
    | appType(nonterminalType("silver:core:Maybe", _, _, _), t) -> !unify(top.attrFor, ^t).failure
    | t -> !unify(top.attrFor, t).failure
    end;
}

function attrIsTotal
Boolean ::= env::Env attrName::String
{
  local dcls::[AttributeDclInfo] = getAttrDcl(attrName, env);
  return
    case dcls of
    | [] -> false
    | d :: _ ->
      case d.typeScheme.typerep of
      | appType(nonterminalType("silver:core:Maybe", _, _, _), _) -> false
      | _ -> true
      end
    end;
}

fun attrMatchesFrame Boolean ::= env::Env attrName::String attrFor::Type =
  decorate qNameAttrOccur(qName(attrName))
  with { env = env; attrFor = attrFor; }.matchesFrame;

function attrMatchesChild
Boolean ::= env::Env attrName::String frame::BlockContext
{
  return
    any(
      map(
        \ e::NamedSignatureElement -> attrMatchesFrame(env, attrName, e.typerep),
        frame.signature.inputElements));
}

instance Eq StrategyExpr {
  eq = \ s1::StrategyExpr s2::StrategyExpr -> s1.unparse == s2.unparse;
}
