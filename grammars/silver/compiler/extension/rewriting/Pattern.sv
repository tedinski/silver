grammar silver:compiler:extension:rewriting;

import silver:compiler:driver:util;

inherited attribute scrutineeType::Type occurs on MRuleList, MatchRule;
propagate scrutineeType on MRuleList;

-- Note that the second type checking pass to specialize type variables is
-- omitted here, for the moment.
threaded attribute pDownSubst, pUpSubst::Substitution occurs on
  PatternList, Pattern, NamedPatternList, NamedPattern;
inherited attribute pFinalSubst::Substitution occurs on
  PatternList, Pattern, NamedPatternList, NamedPattern;
propagate pFinalSubst on PatternList, Pattern, NamedPatternList, NamedPattern;

inherited attribute ruleFlowEnv::FlowEnv occurs on MRuleList, MatchRule;
inherited attribute ruleCompiledGrammars::EnvTree<Decorated RootSpec> occurs on MRuleList, MatchRule;
propagate ruleFlowEnv, ruleCompiledGrammars on MRuleList, MatchRule;

monoid attribute ruleDefs::[Def] occurs on
  MRuleList, MatchRule, PatternList, Pattern, NamedPatternList, NamedPattern;
propagate ruleDefs on
  MRuleList, MatchRule, PatternList, Pattern, NamedPatternList, NamedPattern;

monoid attribute ruleErrors::[Message] occurs on
  MRuleList, MatchRule, PatternList, Pattern, NamedPatternList, NamedPattern;
propagate ruleErrors on
  MRuleList, MatchRule, PatternList, Pattern, NamedPatternList, NamedPattern;

synthesized attribute transform<a>::a;

attribute transform<Strategy> occurs on MRuleList, MatchRule;

{-
 - "Polymorphic" rules are ones in which the LHS matches some well-typed terms
 - that are not permitted by the type of the rule, due to the presence of type
 - variables - such rules require an additional run-time type check before
 - attempting to match.  For example,
 -   rule on Pair<a a> of
 -     pair(x, y) -> pair(y, x)
 -   end
 - matches only pairs where the parameters are the same type; this rule must
 - fail when applied to pair(3, "a") because performing the rewrite would lead
 - to the construction of a type-unsafe tree.  More generally, a rule is
 - polymorphic if the type of a variable/wildcard pattern depends on the rule
 - type.
 -}
synthesized attribute hasUnconstrainedPoly :: Boolean occurs on MRuleList, MatchRule;

aspect production mRuleList_one
top::MRuleList ::= m::MatchRule
{
  top.transform = m.transform;
  top.hasUnconstrainedPoly = m.hasUnconstrainedPoly;
}

aspect production mRuleList_cons
top::MRuleList ::= h::MatchRule '|' t::MRuleList
{
  top.transform = h.transform <+ t.transform;
  top.hasUnconstrainedPoly = h.hasUnconstrainedPoly || t.hasUnconstrainedPoly;
}

aspect production matchRule_c
top::MatchRule ::= pt::PatternList _ e::Expr
{
  pt.scrutineeTypes = [top.scrutineeType];

  production transE::Expr = ^e;
  transE.grammarName = top.grammarName;
  transE.config = top.config;
  transE.frame = top.frame;
  transE.env = newScopeEnv(pt.ruleDefs, top.env);
  transE.compiledGrammars = top.ruleCompiledGrammars;
  transE.isRoot = false;
  transE.flowEnv = top.ruleFlowEnv;
  transE.decSiteVertexInfo = nothing();
  transE.alwaysDecorated = false;
  transE.appDecSiteVertexInfo = nothing();
  transE.dispatchFlowDeps = [];
  transE.ruleEnv = newScopeEnv(pt.ruleDefs, emptyEnv());

  top.ruleErrors <- transE.errors;

  local checkResultType::TypeCheck = check(transE.typerep, top.scrutineeType);
  top.ruleErrors <-
    if checkResultType.typeerror
    then [errFromOrigin(e, "RHS of rule has type " ++ checkResultType.leftpp ++ ", expected " ++ checkResultType.rightpp)]
    else [];

  pt.pDownSubst = emptySubst();
  transE.downSubst = pt.pUpSubst;
  checkResultType.downSubst = transE.upSubst;

  pt.pFinalSubst = checkResultType.upSubst;
  transE.finalSubst = checkResultType.upSubst;
  checkResultType.finalSubst = checkResultType.upSubst;

  top.transform = rewriteRule(pt.firstTransform, transE.transform);
  
  top.hasUnconstrainedPoly =
    head(pt.patternList).patternIsVariable ||
    !null(performSubstitution(top.scrutineeType, pt.pUpSubst).freeVariables);
}

aspect production matchRuleWhen_c
top::MatchRule ::= pt::PatternList 'when' cond::Expr _ e::Expr
{
  pt.scrutineeTypes = [top.scrutineeType];

  production transCond::Expr = ^cond;
  transCond.grammarName = top.grammarName;
  transCond.config = top.config;
  transCond.frame = top.frame;
  transCond.env = newScopeEnv(pt.ruleDefs, top.env);
  transCond.compiledGrammars = top.ruleCompiledGrammars;
  transCond.isRoot = false;
  transCond.flowEnv = top.ruleFlowEnv;
  transCond.decSiteVertexInfo = nothing();
  transCond.alwaysDecorated = false;
  transCond.appDecSiteVertexInfo = nothing();
  transCond.dispatchFlowDeps = [];
  transCond.ruleEnv = newScopeEnv(pt.ruleDefs, emptyEnv());

  top.ruleErrors <- transCond.errors;

  local checkCondType::TypeCheck = check(transCond.typerep, boolType());
  top.ruleErrors <-
    if checkCondType.typeerror
    then [errFromOrigin(e, "Rule condition has type " ++ checkCondType.leftpp ++ ", expected " ++ checkCondType.rightpp)]
    else [];

  production transE::Expr = ^e;
  transE.grammarName = top.grammarName;
  transE.config = top.config;
  transE.frame = top.frame;
  transE.env = newScopeEnv(pt.ruleDefs, top.env);
  transE.compiledGrammars = top.ruleCompiledGrammars;
  transE.isRoot = false;
  transE.flowEnv = top.ruleFlowEnv;
  transE.decSiteVertexInfo = nothing();
  transE.alwaysDecorated = false;
  transE.appDecSiteVertexInfo = nothing();
  transE.dispatchFlowDeps = [];
  transE.ruleEnv = transCond.ruleEnv;

  top.ruleErrors <- transE.errors;

  local checkResultType::TypeCheck = check(transE.typerep, top.scrutineeType);
  top.ruleErrors <-
    if checkResultType.typeerror
    then [errFromOrigin(e, "RHS of rule has type " ++ checkResultType.leftpp ++ ", expected " ++ checkResultType.rightpp)]
    else [];

  pt.pDownSubst = emptySubst();
  transCond.downSubst = pt.pUpSubst;
  thread downSubst, upSubst on transCond, checkCondType, transE, checkResultType;

  pt.pFinalSubst = checkResultType.upSubst;
  transCond.finalSubst = checkResultType.upSubst;
  checkCondType.finalSubst = checkResultType.upSubst;
  transE.finalSubst = checkResultType.upSubst;
  checkResultType.finalSubst = checkResultType.upSubst;

  top.transform =
    require(pt.firstTransform, transCond.transform) <*
    rewriteRule(pt.firstTransform, transE.transform);

  top.hasUnconstrainedPoly =
    head(pt.patternList).patternIsVariable ||
    !null(performSubstitution(top.scrutineeType, pt.pUpSubst).freeVariables);
}

aspect production matchRuleWhenMatches_c
top::MatchRule ::= pt::PatternList 'when' cond::Expr 'matches' p::Pattern _ e::Expr
{
  pt.scrutineeTypes = [top.scrutineeType];

  production transCond::Expr = ^cond;
  transCond.grammarName = top.grammarName;
  transCond.config = top.config;
  transCond.frame = top.frame;
  transCond.env = newScopeEnv(pt.ruleDefs, top.env);
  transCond.compiledGrammars = top.ruleCompiledGrammars;
  transCond.isRoot = false;
  transCond.flowEnv = top.ruleFlowEnv;
  transCond.decSiteVertexInfo = nothing();
  transCond.alwaysDecorated = false;
  transCond.appDecSiteVertexInfo = nothing();
  transCond.dispatchFlowDeps = [];
  transCond.ruleEnv = newScopeEnv(pt.ruleDefs, emptyEnv());

  top.ruleErrors <- transCond.errors;

  p.scrutineeType = performSubstitution(transCond.typerep, transCond.upSubst);

  production transE::Expr = ^e;
  transE.grammarName = top.grammarName;
  transE.config = top.config;
  transE.frame = top.frame;
  transE.env = newScopeEnv(p.ruleDefs, cond.env);
  transE.compiledGrammars = top.ruleCompiledGrammars;
  transE.isRoot = false;
  transE.flowEnv = top.ruleFlowEnv;
  transE.decSiteVertexInfo = nothing();
  transE.alwaysDecorated = false;
  transE.appDecSiteVertexInfo = nothing();
  transE.dispatchFlowDeps = [];
  transE.ruleEnv = newScopeEnv(p.ruleDefs, transCond.ruleEnv);

  top.ruleErrors <- transE.errors;

  local checkResultType::TypeCheck = check(transE.typerep, top.scrutineeType);
  top.ruleErrors <-
    if checkResultType.typeerror
    then [errFromOrigin(e, "RHS of rule has type " ++ checkResultType.leftpp ++ ", expected " ++ checkResultType.rightpp)]
    else [];

  pt.pDownSubst = emptySubst();
  transCond.downSubst = pt.pUpSubst;
  p.pDownSubst = transCond.upSubst;
  transE.downSubst = p.pUpSubst;
  checkResultType.downSubst = transE.upSubst;

  pt.pFinalSubst = checkResultType.upSubst;
  transCond.finalSubst = checkResultType.upSubst;
  p.pFinalSubst = checkResultType.upSubst;
  transE.finalSubst = checkResultType.upSubst;
  checkResultType.finalSubst = checkResultType.upSubst;

  top.transform =
    require(
      pt.firstTransform,
      matchASTExpr(transCond.transform, p.transform, booleanASTExpr(true), booleanASTExpr(false))) <*
    rewriteRule(pt.firstTransform, transE.transform);

  top.hasUnconstrainedPoly =
    head(pt.patternList).patternIsVariable ||
    !null(performSubstitution(top.scrutineeType, pt.pUpSubst).freeVariables);
}

inherited attribute scrutineeTypes::[Type] occurs on PatternList;

attribute transform<ASTPatterns> occurs on PatternList;
synthesized attribute firstTransform::ASTPattern occurs on PatternList;

propagate pDownSubst, pUpSubst on PatternList;

aspect production patternList_one
top::PatternList ::= p::Pattern
{
  p.scrutineeType =
    case top.scrutineeTypes of
    | [] -> errorType()
    | h :: _ -> h
    end;

  top.transform = consASTPattern(p.transform, nilASTPattern());
  top.firstTransform = p.transform;
}
aspect production patternList_more
top::PatternList ::= p::Pattern ',' ps::PatternList
{
  p.scrutineeType =
    case top.scrutineeTypes of
    | [] -> errorType()
    | h :: _ -> h
    end;
  ps.scrutineeTypes =
    case top.scrutineeTypes of
    | [] -> []
    | _ :: t -> t
    end;

  top.transform = consASTPattern(p.transform, ps.transform);
  top.firstTransform = p.transform;
}

aspect production patternList_nil
top::PatternList ::=
{
  top.transform = nilASTPattern();
  top.firstTransform = error("Empty pattern list");
}

inherited attribute scrutineeNamedTypes::[(String, Type)];

attribute scrutineeNamedTypes, transform<NamedASTPatterns> occurs on NamedPatternList;
propagate scrutineeNamedTypes, pDownSubst, pUpSubst on NamedPatternList;

aspect production namedPatternList_one
top::NamedPatternList ::= p::NamedPattern
{
  top.transform = consNamedASTPattern(p.transform, nilNamedASTPattern());
}
aspect production namedPatternList_more
top::NamedPatternList ::= p::NamedPattern ',' ps::NamedPatternList
{
  top.transform = consNamedASTPattern(p.transform, ps.transform);
}

aspect production namedPatternList_nil
top::NamedPatternList ::=
{
  top.transform = nilNamedASTPattern();
}

attribute scrutineeNamedTypes, transform<NamedASTPattern> occurs on NamedPattern;
propagate pDownSubst, pUpSubst on NamedPattern;

aspect production namedPattern
top::NamedPattern ::= qn::QName '=' p::Pattern
{
  local lookupRes::Maybe<Type> = lookup(last(explode(":", qn.name)), top.scrutineeNamedTypes);
  p.scrutineeType = fromMaybe(errorType(), lookupRes);

  top.ruleErrors <-
    if lookupRes.isJust then []
    else [errFromOrigin(top, "Unexpected annotation " ++ qn.name ++ " for production")];

  top.transform = namedASTPattern(qn.lookupAttribute.fullName, p.transform);
}

attribute scrutineeType, transform<ASTPattern> occurs on Pattern;

propagate pDownSubst, pUpSubst on Pattern
  excluding prodAppPattern_named, nilListPattern, consListPattern;

aspect production prodAppPattern_named
top::Pattern ::= prod::QName '(' ps::PatternList ',' nps::NamedPatternList ')'
{
  -- Ignoring contexts and GADT productions here, for now.
  local prodType::Type = skolemizeProductionType(prod.lookupValue.typeScheme).2;
  ps.scrutineeTypes = prodType.inputTypes;
  nps.scrutineeNamedTypes = prodType.namedTypes;

  local checkResultType::TypeCheck = check(prodType.outputType, top.scrutineeType);
  top.ruleErrors <-
    if checkResultType.typeerror
    then [errFromOrigin(top, "Production " ++ prod.name ++ " has type " ++ checkResultType.leftpp ++ ", but we are matching against " ++ checkResultType.rightpp)]
    else [];
  
  checkResultType.downSubst = top.pDownSubst;
  ps.pDownSubst = checkResultType.upSubst;
  thread pDownSubst, pUpSubst on ps, nps, top;

  checkResultType.finalSubst = top.pFinalSubst;

  top.transform =
    prodCallASTPattern(prod.lookupValue.fullName, ps.transform, nps.transform);
}

aspect production wildcPattern
top::Pattern ::= '_'
{
  top.transform = wildASTPattern();
}

aspect production varPattern
top::Pattern ::= v::Name
{
  top.ruleDefs <- [lexicalLocalDef(top.grammarName, v.nameLoc, v.name, top.scrutineeType, nothing(), [])];
  top.transform = varASTPattern(v.name);
}

aspect production errorPattern
top::Pattern ::= msg::[Message]
{
  top.transform = error("transform undefined in the presence of errors");
}

aspect production intPattern
top::Pattern ::= num::Int_t
{
  top.transform = integerASTPattern(toInteger(num.lexeme));
}

aspect production fltPattern
top::Pattern ::= num::Float_t
{
  top.transform = floatASTPattern(toFloat(num.lexeme));
}

aspect production strPattern
top::Pattern ::= str::String_t
{
  top.transform = stringASTPattern(unescapeString(substring(1, length(str.lexeme) - 1, str.lexeme)));
}

aspect production truePattern
top::Pattern ::= 'true'
{
  top.transform = booleanASTPattern(true);
}

aspect production falsePattern
top::Pattern ::= 'false'
{
  top.transform = booleanASTPattern(false);
}

aspect production nilListPattern
top::Pattern ::= '[' ']'
{
  local checkIsList::TypeCheck = check(top.scrutineeType, listType(freshType()));
  top.ruleErrors <-
    if checkIsList.typeerror
    then [errFromOrigin(top, "Expected to match a list type, but got " ++ checkIsList.leftpp)]
    else [];
  
  checkIsList.downSubst = top.pDownSubst;
  top.pUpSubst = checkIsList.upSubst;
  checkIsList.finalSubst = top.pFinalSubst;

  top.transform = nilListASTPattern();
}

aspect production consListPattern
top::Pattern ::= hp::Pattern '::' tp::Pattern
{
  hp.scrutineeType = freshType();
  tp.scrutineeType = top.scrutineeType;

  local checkIsList::TypeCheck = check(top.scrutineeType, listType(hp.scrutineeType));
  top.ruleErrors <-
    if checkIsList.typeerror
    then [errFromOrigin(top, "Expected to match a list type, but got " ++ checkIsList.leftpp)]
    else [];

  checkIsList.downSubst = top.pDownSubst;
  hp.pDownSubst = checkIsList.upSubst;
  thread pDownSubst, pUpSubst on hp, tp, top;
  checkIsList.finalSubst = top.pFinalSubst;

  top.transform = consListASTPattern(hp.transform, tp.transform);
}
