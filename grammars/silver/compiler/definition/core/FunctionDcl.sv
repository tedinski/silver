grammar silver:compiler:definition:core;

import silver:compiler:translation:java:core only escapeName, genFilesUnescapedDown;

tracked nonterminal FunctionSignature with config, grammarName, env, unparse, errors, defs, constraintDefs, occursDefs, namedSignature, signatureName;
tracked nonterminal FunctionLHS with config, grammarName, env, unparse, errors, defs, outputElement;

propagate config, grammarName, errors on FunctionSignature, FunctionLHS;

concrete production functionDcl
top::AGDcl ::= 'function' id::Name ns::FunctionSignature body::ProductionBody
{
  top.unparse = "function " ++ id.unparse ++ "\n" ++ ns.unparse ++ "\n" ++ body.unparse; 

  production fName :: String = top.grammarName ++ ":" ++ escapeName(id.name, top.genFilesUnescapedDown);
  production namedSig :: NamedSignature = ns.namedSignature;

  top.defs := funDef(top.grammarName, id.nameLoc, namedSig) ::
    if null(body.productionAttributes) then []
    else [prodOccursDef(top.grammarName, id.nameLoc, namedSig, body.productionAttributes)];

  top.errors <-
        if length(getValueDclAll(fName, top.env)) > 1
        then [errFromOrigin(id, "Value '" ++ fName ++ "' is already bound.")]
        else [];

  top.errors <-
        if null(body.returnExpr)
        then [errFromOrigin(top, "Function '" ++ id.name ++ "' does not have a return value.")]
        else if length(body.returnExpr) > 1
        then [errFromOrigin(top, "Function '" ++ id.name ++ "' has more than one declared return value.")]
        else [];

  production attribute sigDefs :: [Def] with ++;
  sigDefs := ns.defs;

  ns.signatureName = fName;
  ns.env = newScopeEnv(sigDefs, top.env);

  local attribute prodAtts :: [Def];
  prodAtts = defsFromPADcls(getProdAttrs(fName, top.env), namedSig);

  body.env = occursEnv(ns.occursDefs, newScopeEnv(body.defs ++ sigDefs ++ ns.constraintDefs, newScopeEnv(prodAtts, top.env)));
  body.frame = functionContext(namedSig, myFlowGraph, sourceGrammar=top.grammarName); -- graph from flow:env
} action {
  insert semantic token IdFnProdDcl_t at id.nameLoc;
  sigNames = [];
}

concrete production functionSignature
top::FunctionSignature ::= cl::ConstraintList '=>' lhs::FunctionLHS '::=' rhs::ProductionRHS 
{
  top.unparse = s"${cl.unparse} => ${lhs.unparse} ::= ${rhs.unparse}";

  cl.constraintPos = signaturePos(top.namedSignature, sourceGrammar=top.grammarName);
  cl.env = top.env;
  lhs.env = top.env;
  rhs.env = occursEnv(cl.occursDefs, top.env);
  rhs.implementedSig = nothing();

  top.defs := lhs.defs ++ rhs.defs;
  top.constraintDefs = cl.defs;
  top.occursDefs := cl.occursDefs;

  top.namedSignature =
    namedSignature(
      top.signatureName,
      foldContexts(cl.contexts),
      foldNamedSignatureElements(rhs.inputElements),
      lhs.outputElement,
      -- For the moment, functions do not have named parameters (hence, nilNamedSignatureElement)
      nilNamedSignatureElement());
  
  top.errors <-
    if any(map((.elementShared), rhs.inputElements))
    then [errFromOrigin(rhs, "Sharing in function parameters is not permitted.")]
    else [];
} action {
  sigNames = foldNamedSignatureElements(rhs.inputElements).elementNames;
}

concrete production functionSignatureNoCL
top::FunctionSignature ::= lhs::FunctionLHS '::=' rhs::ProductionRHS 
{
  top.unparse = s"${lhs.unparse} ::= ${rhs.unparse}";

  forwards to functionSignature(nilConstraint(), '=>', @lhs, $2, @rhs);
} action {
  sigNames = foldNamedSignatureElements(rhs.inputElements).elementNames;
}

concrete production functionLHS
top::FunctionLHS ::= t::TypeExpr
{
  top.unparse = t.unparse;
  propagate env;

  production attribute fName :: String;
  fName = "__func__lhs";

  top.outputElement = namedSignatureElement(fName, t.typerep, false);

  -- TODO: think about this. lhs doesn't really have an fName.
  top.defs := [lhsDef(top.grammarName, getParsedOriginLocationOrFallback(t), fName, t.typerep)];
}

