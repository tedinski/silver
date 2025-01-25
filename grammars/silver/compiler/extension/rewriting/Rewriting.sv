grammar silver:compiler:extension:rewriting;

imports silver:core hiding id;
imports silver:util:treeset as ts;

imports silver:reflect;
imports silver:rewrite hiding repeat;
imports silver:compiler:metatranslation;
imports silver:langutil:pp;

imports silver:compiler:definition:core;
imports silver:compiler:definition:type;
imports silver:compiler:definition:type:syntax;
imports silver:compiler:definition:env;
imports silver:compiler:definition:flow:env;
imports silver:compiler:analysis:typechecking:core;
imports silver:compiler:extension:patternmatching;
imports silver:compiler:modification:list;
imports silver:compiler:modification:primitivepattern;
imports silver:compiler:modification:lambda_fn;
imports silver:compiler:modification:let_fix;

-- Note that these being infix operators means that this wouldn't pass the MDA,
-- despite being a Silver "extension".  This could be fixed by refactoring the
-- Silver Expr grammar into an "ETF" style with seperate operator nonterminals.
terminal Sequence_t '<*'  precedence = 12, association = left; -- Same as *
terminal Choice_t   '<+'  precedence = 11, association = left; -- Same as +

concrete production sequenceOperator
top::Expr ::= s1::Expr '<*' s2::Expr
{
  top.unparse = s"(${s1.unparse} <* ${s2.unparse})";
  forwards to Silver_Expr { silver:rewrite:sequence($Expr{@s1}, $Expr{@s2}) };
}

concrete production choiceOperator
top::Expr ::= s1::Expr '<+' s2::Expr
{
  top.unparse = s"(${s1.unparse} <+ ${s2.unparse})";
  forwards to Silver_Expr { silver:rewrite:choice($Expr{@s1}, $Expr{@s2}) };
}


terminal Traverse_t 'traverse' lexer classes {KEYWORD, RESERVED};

concrete production traverseProdExprAnno
top::Expr ::= 'traverse' n::QName '(' es::AppExprs ',' anns::AnnoAppExprs ')'
{
  top.unparse = s"traverse ${n.name}(${es.unparse}, ${anns.unparse})";
  propagate config, grammarName, compiledGrammars, frame, env, flowEnv;
  
  local numChildren::Integer = n.lookupValue.typeScheme.arity;
  local annotations::[String] = map(fst, n.lookupValue.typeScheme.typerep.namedTypes);
  es.appExprTypereps = repeat(nonterminalType("silver:rewrite:Strategy", [], false, true), numChildren);
  es.appExprApplied = n.unparse;
  es.decSiteVertexInfo = nothing();
  es.dispatchFlowDeps = [];
  es.appProd = nothing();
  es.appIndexOffset = 0;
  anns.appExprApplied = n.unparse;
  anns.funcAnnotations =
    map(pair(fst=_, snd=nonterminalType("silver:rewrite:Strategy", [], false, true)), annotations);
  anns.remainingFuncAnnotations = anns.funcAnnotations;
 
  local localErrors::[Message] =
    es.errors ++ anns.traverseErrors ++
    if null(getTypeDcl("silver:rewrite:Strategy", top.env))
    then [errFromOrigin(top, "Term rewriting requires import of silver:rewrite")]
    else [];

  propagate downSubst, upSubst, finalSubst, freeVars;
  
  nondecorated local transform::Strategy =
    traversal(n.lookupValue.fullName, es.traverseTransform, anns.traverseTransform);
  nondecorated local fwrd::Expr = translate(reflect(transform));
  
  forwards to if !null(localErrors) then errorExpr(localErrors) else fwrd;
}
concrete production traverseProdAnno
top::Expr ::= 'traverse' n::QName '(' anns::AnnoAppExprs ')'
{
  forwards to traverseProdExprAnno($1, @n, $3, emptyAppExprs(), ',', @anns, $5);
}
concrete production traverseProdExpr
top::Expr ::= 'traverse' n::QName '(' es::AppExprs ')'
{
  forwards to traverseProdExprAnno($1, @n, $3, @es, ',', emptyAnnoAppExprs(), $5);
}
concrete production traverseProdEmpty
top::Expr ::= 'traverse' n::QName '(' ')'
{
  forwards to traverseProdExprAnno($1, @n, $3, emptyAppExprs(), ',', emptyAnnoAppExprs(), $4);
}

abstract production traverseConsList
top::Expr ::= 'traverse' '(' h::AppExpr '::' t::AppExpr ')'
{
  top.unparse = s"traverse (${h.unparse} :: ${t.unparse})";
  
  nondecorated local transform::Strategy = consListCongruence(h.traverseTransform, t.traverseTransform);
  forwards to translate(reflect(transform));
}
concrete production traverseConsListFirstMissing
top::Expr ::= 'traverse' '(' h::'_' '::' t::AppExpr ')'
{
  forwards to traverseConsList($1, $2, missingAppExpr(h), $4, @t, $6);
}
concrete production traverseConsListFirstPresent
top::Expr ::= 'traverse' '(' h::Expr '::' t::AppExpr ')'
{
  forwards to traverseConsList($1, $2, presentAppExpr(@h), $4, @t, $6);
}

concrete production traverseNilList
top::Expr ::= 'traverse' '[' ']'
{
  top.unparse = s"traverse []";
  
  nondecorated local transform::Strategy = nilListCongruence();
  forwards to translate(reflect(transform));
}

concrete production traverseList
top::Expr ::= 'traverse' '[' es::AppExprs ']'
{
  top.unparse = s"traverse [${es.unparse}]";
  
  nondecorated local transform::Strategy = foldr(consListCongruence, nilListCongruence(), es.traverseTransform);
  forwards to translate(reflect(transform));
}

-- Compute our own errors on AnnoAppExprs, since we want to ignore missing annotations (like in patterns)
synthesized attribute traverseErrors::[Message] occurs on AnnoAppExprs, AnnoExpr;
synthesized attribute traverseTransform<a>::a;
attribute traverseTransform<Strategy> occurs on AppExpr;
attribute traverseTransform<Pair<String Strategy>> occurs on AnnoExpr;
attribute traverseTransform<[Strategy]> occurs on AppExprs;
attribute traverseTransform<[Pair<String Strategy>]> occurs on AnnoAppExprs;

aspect production missingAppExpr
top::AppExpr ::= '_'
{
  top.traverseTransform = id();
}
aspect production presentAppExpr
top::AppExpr ::= e::Expr
{
  top.traverseTransform = antiquoteStrategy(^e);
}

aspect production snocAppExprs
top::AppExprs ::= es::AppExprs ',' e::AppExpr
{
  top.traverseTransform = es.traverseTransform ++ [e.traverseTransform];
}
aspect production oneAppExprs
top::AppExprs ::= e::AppExpr
{
  top.traverseTransform = [e.traverseTransform];
}
aspect production emptyAppExprs
top::AppExprs ::=
{
  top.traverseTransform = [];
}

aspect production annoExpr
top::AnnoExpr ::= qn::QName '=' e::AppExpr
{
  top.traverseErrors =
    e.errors ++
    if !extractNamedArg(qn.name, top.funcAnnotations).fst.isJust
    then [errFromOrigin(qn, "Named parameter '" ++ qn.name ++ "' is not appropriate for '" ++ top.appExprApplied ++ "'")]
    else [];
  top.traverseTransform = (qn.lookupAttribute.fullName, e.traverseTransform);
}

aspect production snocAnnoAppExprs
top::AnnoAppExprs ::= es::AnnoAppExprs ',' e::AnnoExpr
{
  top.traverseErrors = es.traverseErrors ++ e.traverseErrors;
  top.traverseTransform = es.traverseTransform ++ [e.traverseTransform];
}
aspect production oneAnnoAppExprs
top::AnnoAppExprs ::= e::AnnoExpr
{
  top.traverseErrors = e.traverseErrors;
  top.traverseTransform = [e.traverseTransform];
}
aspect production emptyAnnoAppExprs
top::AnnoAppExprs ::=
{
  top.traverseErrors = [];
  top.traverseTransform = [];
}

terminal Rule_t 'rule' lexer classes {KEYWORD, RESERVED};

concrete production ruleExpr
top::Expr ::= 'rule' 'on' ty::TypeExpr 'of' Opt_Vbar_t ml::MRuleList 'end'
{
  top.unparse = "rule on " ++ ty.unparse ++ " of " ++ ml.unparse ++ " end";
  propagate grammarName, config, frame, flowEnv, freeVars;
  
  -- Find the free type variables (i.e. lacking a definition) to add as skolem constants
  local freeTyVars::[String] =
    filter(\ tv::String -> null(getTypeDcl(tv, top.env)), nub(ty.lexicalTypeVariables));
  ty.env = newScopeEnv(
    attachNote logicalLocationFromOrigin(ty) on
      addNewLexicalTyVars(top.grammarName, [], freeTyVars)
    end, top.env);

  ml.env = top.env;
  ml.matchRulePatternSize = 1;
  ml.ruleCompiledGrammars = top.compiledGrammars;
  ml.ruleFlowEnv = top.flowEnv;
  
  local localErrors::[Message] =
    ty.errors ++ ml.ruleErrors ++
    ty.errorsKindStar ++
    if null(getTypeDcl("silver:rewrite:Strategy", top.env))
    then [errFromOrigin(top, "Term rewriting requires import of silver:rewrite")]
    else [];
  
  -- Can't use an error production here, unfortunately, due to circular dependency issues.
  top.errors := if !null(localErrors) then localErrors else forward.errors;
  
  ml.scrutineeType =
    freshenType(
      ty.typerep,  -- TODO: Should this be substituted?
      ty.typerep.freeVariables);
  nondecorated local transform::Strategy =
    if ml.hasUnconstrainedPoly
    then requireType(antiquoteASTExpr(
      Silver_Expr {
        silver:rewrite:anyASTExpr(
          \ _::$TypeExpr{typerepTypeExpr(ml.scrutineeType)} -> unit())
      })) <* ml.transform
    else ml.transform;
  
  nondecorated local fwrd::Expr = translate(reflect(transform));
  
  --forwards to unsafeTrace(fwrd, print(top.location.unparse ++ ": " ++ show(80, transform.pp) ++ "\n\n\n", unsafeIO()));
  forwards to fwrd;
}

-- Strategy meta-translation
abstract production antiquoteASTExpr
top::ASTExpr ::= e::Expr
{
  top.pp = pp"antiquoteASTExpr {${text(e.unparse)}}";
  forwards to error("no forward");
}

abstract production antiquoteStrategy
top::Strategy ::= e::Expr
{
  top.pp = pp"antiquoteStrategy {${text(e.unparse)}}";
  forwards to error("no forward");
}

aspect production nonterminalAST
top::AST ::= prodName::String children::ASTs annotations::NamedASTs
{
  directAntiquoteProductions <-
    ["silver:compiler:extension:rewriting:antiquoteASTExpr",
     "silver:compiler:extension:rewriting:antiquoteStrategy"];
}

global builtin::Location = builtinLoc("rewriting");
