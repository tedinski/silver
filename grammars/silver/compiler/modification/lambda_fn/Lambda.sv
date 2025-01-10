import silver:compiler:definition:env;
import silver:util:treeset as ts;

--- Concrete Syntax for lambdas
--------------------------------------------------------------------------------

terminal Lambda_kwd '\' lexer classes {KEYWORD,RESERVED};
terminal Arrow_t '->' precedence = 0, lexer classes {SPECOP};

{--
 - Concrete syntax for lambda expressions
 - @param params Parameter name and signature declarations for this lambda
 - @param e Body of the lambda
 -}
concrete production lambda_c
top::Expr ::= '\' params::LambdaRHS '->' e::Expr
{
  top.unparse = "\\ " ++ params.unparse ++ " -> " ++ e.unparse;

  forwards to lambdap(@params, @e);
}

{--
 - Abstract syntax for lambda expressions
 - @param params Parameter name and signature declarations for this lambda
 - @param e Body of the lambda
 -}
abstract production lambdap
top::Expr ::= params::LambdaRHS e::Expr
{
  top.unparse = "\\ " ++ params.unparse ++ " -> " ++ e.unparse;
  top.freeVars := ts:removeAll(params.lambdaBoundVars, e.freeVars);
  
  propagate config, grammarName, compiledGrammars, errors, originRules;
  
  top.typerep = appTypes(functionType(length(params.inputElements), []), 
                         map((.typerep), params.inputElements) ++ [e.typerep]);

  production attribute sigDefs::[Def] with ++;
  sigDefs := params.lambdaDefs;
  sigDefs <-
    addNewLexicalTyVars_ActuallyVariables(
      top.grammarName, getParsedOriginLocationOrFallback(params), params.lexicalTyVarKinds,
      filter(\ tv::String -> null(getTypeDcl(tv, top.env)), nub(params.lexicalTypeVariables)));

  propagate downSubst, upSubst, downSubst2, upSubst2, finalSubst;
  
  params.env = newScopeEnv(sigDefs, top.env);
  params.givenLambdaParamIndex = 0;
  params.givenLambdaId = genInt();
  e.env = params.env;
  e.frame = inLambdaContext(top.frame, sourceGrammar=top.frame.sourceGrammar); --TODO: Is this sourceGrammar correct?
  e.isRoot = false;
}


tracked nonterminal LambdaRHS with 
  givenLambdaParamIndex, givenLambdaId, env, grammarName, flowEnv, 
  lambdaBoundVars, lambdaDefs, lexicalTypeVariables, lexicalTyVarKinds, 
  inputElements, unparse, elementCount, errors;

tracked nonterminal LambdaRHSElem with 
  givenLambdaParamIndex, givenLambdaId, grammarName, deterministicCount, env, 
  flowEnv, lambdaBoundVars, lambdaDefs, unparse, lexicalTypeVariables, 
  inputElements, lexicalTyVarKinds, errors;


monoid attribute lambdaDefs::[Def];
monoid attribute lambdaBoundVars::[String];

inherited attribute givenLambdaId::Integer;
inherited attribute givenLambdaParamIndex::Integer;

flowtype decorate {forward, grammarName, flowEnv} on LambdaRHS, LambdaRHSElem;
flowtype forward {env} on LambdaRHS;
flowtype forward {deterministicCount, env} on LambdaRHSElem;

flowtype lambdaDefs {decorate, givenLambdaId, givenLambdaParamIndex} on LambdaRHS, LambdaRHSElem;
flowtype lambdaBoundVars {} on LambdaRHS;
flowtype lambdaBoundVars {deterministicCount} on LambdaRHSElem;

propagate lambdaDefs, lambdaBoundVars on LambdaRHS;
propagate flowEnv, env, grammarName, givenLambdaId, lexicalTyVarKinds, errors on LambdaRHS, LambdaRHSElem;
propagate lexicalTypeVariables on LambdaRHS, LambdaRHSElem excluding lambdaRHSCons;


{--
 - Cons production for the lambda parameter signature list NT
 - @param h The head parameter signature
 - @param t The rest of the parameter signature list
 -}
concrete production lambdaRHSCons
top::LambdaRHS ::= h::LambdaRHSElem t::LambdaRHS
{
  t.givenLambdaParamIndex = top.givenLambdaParamIndex + 1;
  h.givenLambdaParamIndex = top.givenLambdaParamIndex;

  top.lexicalTypeVariables := nub(h.lexicalTypeVariables ++ t.lexicalTypeVariables);
  top.inputElements = h.inputElements ++ t.inputElements;

  top.unparse = h.unparse ++ " " ++ t.unparse;

  h.deterministicCount = t.elementCount;
  top.elementCount = 1 + t.elementCount;
}

{--
 - Nil production for lambda parameter signature list NT
 -}
concrete production lambdaRHSNil
top::LambdaRHS ::=
{
  top.inputElements = [];
  top.unparse = "";
  top.elementCount = 0;
}


{--
 - Lambda parameter declarations with explicit name and type
 - @param id The parameter name
 - @param t The parameter type declaration
 -}
concrete production lambdaRHSElemIdTy
top::LambdaRHSElem ::= id::Name '::' t::TypeExpr
{
  production fName :: String = toString(genInt()) ++ ":" ++ id.name;
  top.lambdaDefs := [lambdaParamDef(top.grammarName, id.nameLoc, fName, t.typerep, 
                                    top.givenLambdaId, top.givenLambdaParamIndex)];
  top.lambdaBoundVars := [id.name];

  top.inputElements = [namedSignatureElement(id.name, t.typerep, false)];
  
  top.unparse = id.unparse ++ "::" ++ t.unparse;

}

{--
 - Lambda parameter declarations with explicit type but no name
 - @param t The parameter type declaration
 -}
concrete production lambdaRHSElemTy
top::LambdaRHSElem ::= '_' '::' t::TypeExpr
{
  top.unparse = "_::" ++ t.unparse;

  forwards to lambdaRHSElemIdTy (
    name("_G_" ++ toString(top.deterministicCount)), 
    '::', 
    @t);
}

{--
 - Lambda parameter declarations with explicit name but no type
 - @param id The parameter name
 -}
concrete production lambdaRHSElemId
top::LambdaRHSElem ::= id::Name
{
  top.unparse = id.unparse;

  forwards to lambdaRHSElemIdTy (
    @id, 
    '::', 
    typerepTypeExpr(freshType()));
}

{--
 - Lambda parameter declarations with neither an explicit name nor type
 -}
concrete production lambdaRHSElemUnderline
top::LambdaRHSElem ::= '_'
{
  top.unparse = "_";

  forwards to lambdaRHSElemIdTy (
    name("_G_" ++ toString(top.deterministicCount)), 
    '::', 
    typerepTypeExpr(freshType()));
}


abstract production lambdaParamReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  propagate errors;
  top.freeVars := ts:fromList([q.name]);
  
  top.typerep = q.lookupValue.typeScheme.monoType;

  propagate downSubst, upSubst, downSubst2, upSubst2;
}