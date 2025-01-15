grammar silver:compiler:modification:defaultattr;

import silver:compiler:definition:core;
import silver:compiler:definition:origins;
import silver:compiler:definition:env;
import silver:compiler:definition:type;
import silver:compiler:definition:type:syntax;
import silver:compiler:analysis:typechecking:core;
import silver:compiler:translation:java;

import silver:compiler:definition:flow:env;
import silver:compiler:definition:flow:ast only lhsVertexType;
import silver:compiler:definition:flow:driver only ProductionGraph, FlowType, constructDefaultProductionGraph; -- for the "oh no again!" hack below
import silver:compiler:driver:util only RootSpec; -- ditto

terminal Default_kwd 'default' lexer classes {KEYWORD, RESERVED};

concrete production aspectDefaultProduction
top::AGDcl ::= 'aspect' 'default' 'production' ns::AspectDefaultProductionSignature body::ProductionBody 
{
  top.unparse = "aspect default production\n" ++ ns.unparse ++ "\n" ++ body.unparse;

  top.defs := [];

  propagate config, grammarName, compiledGrammars, errors;
  
  local sigDefs :: [Def] = addNewLexicalTyVars(top.grammarName, ns.lexicalTyVarKinds, ns.lexicalTypeVariables);

  ns.env = newScopeEnv(sigDefs, top.env);

  body.env = newScopeEnv(ns.defs, ns.env);
  body.frame = defaultAspectContext(ns.namedSignature, myFlowGraph, sourceGrammar=top.grammarName);

  body.downSubst = emptySubst();

  top.setupInh := body.setupInh; -- Probably should be empty?
  top.initProd := "\t\t//ASPECT DEFAULT PRODUCTION for " ++ ns.namedSignature.outputElement.typerep.typeName ++ "\n" ++ body.translation;
  top.valueWeaving := body.valueWeaving; -- Probably should be empty?
} action {
  sigNames = [];
}

tracked nonterminal AspectDefaultProductionSignature with config, grammarName, env, flowEnv, unparse, errors, defs, namedSignature, lexicalTypeVariables, lexicalTyVarKinds;

concrete production aspectDefaultProductionSignature
top::AspectDefaultProductionSignature ::= lhs::Name '::' te::TypeExpr '::='
{
  top.unparse = lhs.unparse ++ "::" ++ te.unparse ++ " ::=";
  top.defs := [defaultLhsDef(top.grammarName, lhs.nameLoc, lhs.name, te.typerep)];
  top.namedSignature =
    namedSignature(top.grammarName ++ ":" ++ te.typerep.typeName ++ ":default",
      nilContext(), nilNamedSignatureElement(),
      namedSignatureElement(lhs.name, te.typerep, false),
      foldNamedSignatureElements(annotationsForNonterminal(te.typerep, top.env)));

  propagate config, grammarName, env, compiledGrammars, errors, lexicalTypeVariables, lexicalTyVarKinds, flowEnv;

  local checkNT::TypeCheck = checkNonterminal(top.env, false, te.typerep);
  checkNT.downSubst = emptySubst();
  checkNT.finalSubst = emptySubst();

  top.errors <-
    if checkNT.typeerror
    then [errFromOrigin(top, "Default production LHS type must be a nonterminal.  Instead it is of type " ++ checkNT.leftpp)]
    else [];

  top.errors <- te.errorsKindStar;
  top.errors <-
    case te of
    -- LHS must be either NT or NT<a b ...> where a b ... are all ty vars
    | appTypeExpr(_, tl) -> tl.errorsTyVars
    | _ -> []
    end;
} action {
  insert semantic token IdSigNameDcl_t at lhs.nameLoc;
  sigNames = [lhs.name];
}

fun defaultLhsDef Def ::= sg::String sl::Location fn::String ty::Type =
  valueDef(defaultEnvItem(defaultLhsDcl(fn,ty,sourceGrammar=sg,sourceLocation=sl)));
abstract production defaultLhsDcl
top::ValueDclInfo ::= fn::String ty::Type
{
  top.fullName = fn;
  propagate isEqual;

  top.typeScheme = monoType(^ty);
  
  top.refDispatcher = lhsReference;
  top.defDispatcher = errorValueDef; -- TODO: be smarter about the error message
  top.defLHSDispatcher = defaultLhsDefLHS;
  top.transDefLHSDispatcher = errorTransAttrDefLHS;
}

abstract production defaultLhsDefLHS implements BaseDefLHS
top::DefLHS ::= @q::QName
{
  top.name = q.name;
  top.unparse = q.unparse;
  top.found = !existingProblems && top.defLHSattr.attrDcl.isSynthesized;
  
  local existingProblems :: Boolean = !top.defLHSattr.found || top.typerep.isError;
  
  top.errors :=
    if existingProblems || top.found then []
    else [errFromOrigin(q, "Cannot define inherited attribute '" ++ top.defLHSattr.name ++ "' on the lhs '" ++ q.name ++ "'")];
  
  top.typerep = q.lookupValue.typeScheme.monoType;

  top.defLHSVertex = lhsVertexType;
  top.defLHSInhEq = [];
  top.inhAttrName = "";

  top.translation = makeNTName(top.frame.lhsNtName) ++ ".defaultSynthesizedAttributes";
}

abstract production defaultAspectContext
top::BlockContext ::= sig::NamedSignature  g::ProductionGraph
{
  top.fullName = sig.fullName;
  top.lhsNtName = sig.outputElement.typerep.typeName;
  top.signature = sig;
  top.flowGraph = g;
  top.originsContextSource = useContextLhsAndRules();
}
