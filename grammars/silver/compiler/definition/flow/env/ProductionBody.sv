grammar silver:compiler:definition:flow:env;

import silver:compiler:definition:type only isNonterminal, typerep;
import silver:compiler:definition:type:syntax;
import silver:compiler:analysis:typechecking:core;
import silver:compiler:modification:defaultattr;
import silver:compiler:modification:collection;
import silver:compiler:modification:copper;
import silver:compiler:driver:util only isExportedBy, RootSpec;

attribute flowDefs, flowEnv occurs on ProductionBody, ProductionStmts, ProductionStmt, ForwardInhs, ForwardInh;
attribute flowEnv occurs on DefLHS;

propagate flowDefs, flowEnv on ProductionBody, ProductionStmts, ProductionStmt, ForwardInhs, ForwardInh;
propagate flowEnv on DefLHS;

{- A short note on how flowDefs are generated:

  - We ALWAYS produce the flowDef itself. This is necessary to catch missing or duplicate equations.
  - We omit the dependencies if it appears in a location not permitted to affect the flow type.
    This is to allow us to just compute flow types once, globally.
-}

{--
 - An occurs dcl info 's flow type can be affected here
 -}
function isAffectable
Boolean ::= prodgram::String  ntgram::String  cg::EnvTree<Decorated RootSpec>  d::OccursDclInfo
{
  return isExportedBy(prodgram, [ntgram, d.sourceGrammar], cg);
}

aspect production attachNoteStmt
top::ProductionStmt ::= 'attachNote' note::Expr ';'
{
  note.decSiteVertexInfo = nothing();
  note.alwaysDecorated = false;
  note.appDecSiteVertexInfo = nothing();
  note.dispatchFlowDeps = [];
}

aspect production forwardsTo
top::ProductionStmt ::= 'forwards' 'to' e::Expr ';'
{
  local ntDefGram :: String = hackGramFromFName(top.frame.lhsNtName);

  local mayAffectFlowType :: Boolean =
    isExportedBy(top.grammarName, [ntDefGram], top.compiledGrammars);
  
  top.flowDefs <- [
    fwdEq(top.frame.fullName, e.flowDeps, mayAffectFlowType),
    -- These are attributes that we know, here, occurs on this nonterminal.
    -- The point is, these are the implicit equations we KNOW get generated, so
    -- we regard these as non-suspect. That is, we implicitly insert these copy
    -- equations here.
    -- Currently, we don't bother to filter this to just synthesized, but we should?
    -- TODO: What about attrs on translation attrs?
    implicitFwdAffects(top.frame.fullName, map((.attrOccurring),
      filter(isAffectable(top.grammarName, ntDefGram, top.compiledGrammars, _),
        getAttrOccursOn(top.frame.lhsNtName, top.env))))];

  e.decSiteVertexInfo = just(forwardVertexType);
  e.alwaysDecorated = true;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
aspect production forwardInh
top::ForwardInh ::= lhs::ForwardLHSExpr '=' e::Expr ';'
{
  -- TODO: we need to figure out how to introduce any new lhsinh deps to the
  -- forward flow type automatically.
  top.flowDefs <-
    case lhs of
    | forwardLhsExpr(q) -> [fwdInhEq(top.frame.fullName, q.attrDcl.fullName, e.flowDeps)]
    end;
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
aspect production returnDef
top::ProductionStmt ::= 'return' e::Expr ';'
{
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}

aspect production attributeDef
top::ProductionStmt ::= dl::DefLHS '.' attr::QNameAttrOccur '=' e::Expr ';'
{
  propagate flowEnv;
  e.dispatchFlowDeps = [];
}
aspect production errorAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr msg::[Message]
{
  propagate flowEnv;
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
aspect production synthesizedAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  local ntDefGram :: String = hackGramFromFName(top.frame.lhsNtName);

  local srcGrams :: [String] = [ntDefGram, hackGramFromDcl(attr)];

  local mayAffectFlowType :: Boolean =
    isExportedBy(top.grammarName, srcGrams, top.compiledGrammars);
  
  top.flowDefs <-
    if top.frame.hasPartialSignature then 
      [synEq(top.frame.fullName, attr.attrDcl.fullName, e.flowDeps, mayAffectFlowType)]
    else
      [defaultSynEq(top.frame.lhsNtName, attr.attrDcl.fullName, e.flowDeps)];
  e.decSiteVertexInfo =
    if attr.found && attr.attrDcl.isTranslation
    then just(transAttrVertexType(dl.defLHSVertex, attr.attrDcl.fullName))
    else nothing();
  e.alwaysDecorated = attr.found && attr.attrDcl.isTranslation;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
aspect production inheritedAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  top.flowDefs <- flap(dl.defLHSInhEq, e.flowDeps);
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}

-- The flow vertex type corresponding to attributes on this DefLHS
synthesized attribute defLHSVertex::VertexType occurs on DefLHS;

-- The constructor for inherited equations on this DefLHS
synthesized attribute defLHSInhEq::[(FlowDef ::= [FlowVertex])] occurs on DefLHS;

-- The name of the inherited attribute described by this DefLHS.  May be syn.inh for translation attributes.
synthesized attribute inhAttrName::String occurs on DefLHS;

aspect default production
top::DefLHS ::=
{
  top.defLHSVertex = localVertexType("bogus:lhs:vertex");
  top.defLHSInhEq = [];
  top.inhAttrName = "";
}
aspect production childDefLHS
top::DefLHS ::= @q::QName
{
  top.defLHSVertex = rhsVertexType(q.lookupValue.fullName);
  top.defLHSInhEq = [inhEq(top.frame.fullName, q.lookupValue.fullName, top.defLHSattr.attrDcl.fullName, _)];
  top.inhAttrName = top.defLHSattr.attrDcl.fullName;
}
aspect production lhsDefLHS
top::DefLHS ::= @q::QName
{
  top.defLHSVertex = lhsVertexType;
  top.defLHSInhEq = [];
  top.inhAttrName = "";
}
aspect production localDefLHS
top::DefLHS ::= @q::QName
{
  top.defLHSVertex = localVertexType(q.lookupValue.fullName);
  top.defLHSInhEq = [localInhEq(top.frame.fullName, q.lookupValue.fullName, top.defLHSattr.attrDcl.fullName, _)];
  top.inhAttrName = top.defLHSattr.attrDcl.fullName;
}
aspect production forwardDefLHS
top::DefLHS ::= @q::QName
{
  top.defLHSVertex = forwardVertexType;
  top.defLHSInhEq = [fwdInhEq(top.frame.fullName, top.defLHSattr.attrDcl.fullName, _)];
  top.inhAttrName = top.defLHSattr.attrDcl.fullName;
}
aspect production childTransAttrDefLHS
top::DefLHS ::= @q::QName @attr::QNameAttrOccur
{
  top.defLHSVertex = transAttrVertexType(rhsVertexType(q.lookupValue.fullName), attr.attrDcl.fullName);
  top.defLHSInhEq = [transInhEq(top.frame.fullName, q.lookupValue.fullName, attr.attrDcl.fullName, top.defLHSattr.attrDcl.fullName, _)];
  top.inhAttrName = s"${attr.attrDcl.fullName}.${top.defLHSattr.attrDcl.fullName}";
}
aspect production localTransAttrDefLHS
top::DefLHS ::= @q::QName @attr::QNameAttrOccur
{
  top.defLHSVertex = transAttrVertexType(localVertexType(q.lookupValue.fullName), attr.attrDcl.fullName);
  top.defLHSInhEq = [localTransInhEq(top.frame.fullName, q.lookupValue.fullName, attr.attrDcl.fullName, top.defLHSattr.attrDcl.fullName, _)];
  top.inhAttrName = s"${attr.attrDcl.fullName}.${top.defLHSattr.attrDcl.fullName}";
}

aspect production errorValueDef
top::ProductionStmt ::= @val::QName e::Expr
{
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}

aspect production localValueDef
top::ProductionStmt ::= @val::QName e::Expr
{
  -- TODO: So, I'm just going to assume for the moment that we're always allowed to define the eq for a local...
  -- technically, it's possible to break this if you declare it in one grammar, but define it in another, but
  -- I think we should forbid that syntactically, later on...
  top.flowDefs <-
    [localEq(
      top.frame.fullName, val.lookupValue.fullName, val.lookupValue.typeScheme.typeName,
      val.lookupValue.typeScheme.typerep.isNonterminal, val.lookupValue.found && val.lookupValue.dcl.hasForward, e.flowDeps)];

  -- If we have a type var with occurs-on contexts, add the specified syn -> inh deps for the new vertex
  top.flowDefs <- occursContextDeps(top.frame.signature, top.env, val.lookupValue.typeScheme.typerep, localVertexType(val.lookupValue.fullName));

  e.decSiteVertexInfo =
    if e.alwaysDecorated
    then just(localVertexType(val.lookupValue.fullName))
    else nothing();
  e.alwaysDecorated =
    isDecorable(e.finalType, top.env) && val.lookupValue.found && !val.lookupValue.dcl.isNondec;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}

-- FROM COLLECTIONS TODO

aspect production synAppendColAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur  {- <- -} e::Expr
{
  local ntDefGram :: String = hackGramFromFName(top.frame.lhsNtName);

  local mayAffectFlowType :: Boolean =
    isExportedBy(top.grammarName, [ntDefGram, hackGramFromDcl(attr)], top.compiledGrammars);

  top.flowDefs <-
    [extraEq(top.frame.fullName, lhsSynVertex(attr.attrDcl.fullName), e.flowDeps, mayAffectFlowType)];
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}

aspect production inhAppendColAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur  {- <- -} e::Expr
{
  top.flowDefs <- [extraEq(top.frame.fullName, dl.defLHSVertex.inhVertex(attr.attrDcl.fullName), e.flowDeps, true)];
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
aspect production synBaseColAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  local ntDefGram :: String = hackGramFromFName(top.frame.lhsNtName);

  local srcGrams :: [String] = [ntDefGram, hackGramFromDcl(attr)];

  local mayAffectFlowType :: Boolean =
    isExportedBy(top.grammarName, srcGrams, top.compiledGrammars);
  
  top.flowDefs <-
    if top.frame.hasPartialSignature then 
      [synEq(top.frame.fullName, attr.attrDcl.fullName, e.flowDeps, mayAffectFlowType)]
    else
      [defaultSynEq(top.frame.lhsNtName, attr.attrDcl.fullName, e.flowDeps)];
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
aspect production inhBaseColAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  top.flowDefs <- flap(dl.defLHSInhEq, e.flowDeps);
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}

aspect production baseCollectionValueDef
top::ProductionStmt ::= @val::QName e::Expr
{
  -- We actually don't want reference site flow projections in e,
  -- since we don't actually know the entire tree in which it is decorated.
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
aspect production appendCollectionValueDef
top::ProductionStmt ::= @val::QName e::Expr
{
  local locDefGram :: String = hackGramFromQName(val.lookupValue);

  local mayAffectFlowType :: Boolean =
    isExportedBy(top.grammarName, [locDefGram], top.compiledGrammars);

  -- TODO: So, locals that may affect flow types' suspect edges can NEVER have an effect
  -- so we don't bother to even emit the extra equations in that case.
  -- But, this means we might lose out on knowing there's a contribution here.
  -- If we ever start using this information to locate contributions.
  -- If we do, we'll have to come back here to add 'location' info anyway,
  -- so if we do that, uhhh... fix this! Because you're here! Reading this!

  -- TODO: This shouldn't be a forwarding prod!
  top.flowDefs := e.flowDefs ++
    if mayAffectFlowType
    then [extraEq(top.frame.fullName, localEqVertex(val.lookupValue.fullName), e.flowDeps, true)]
    else [];
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}

-- TODO: flowDefs for Copper ProductionStmts
aspect production pluckDef
top::ProductionStmt ::= 'pluck' e::Expr ';'
{
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
aspect production printStmt
top::ProductionStmt ::= 'print' e::Expr ';'
{
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
aspect production parserAttributeValueDef
top::ProductionStmt ::= @val::QName e::Expr
{
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}
aspect production pushTokenStmt
top::ProductionStmt ::= 'pushToken' '(' val::QName ',' lexeme::Expr ')' ';'
{
  lexeme.decSiteVertexInfo = nothing();
  lexeme.alwaysDecorated = false;
  lexeme.appDecSiteVertexInfo = nothing();
  lexeme.dispatchFlowDeps = [];
}
aspect production insertSemanticTokenStmt
top::ProductionStmt ::= 'insert' 'semantic' 'token' n::QNameType 'at' loc::Expr ';'
{
  loc.decSiteVertexInfo = nothing();
  loc.alwaysDecorated = false;
  loc.appDecSiteVertexInfo = nothing();
  loc.dispatchFlowDeps = [];
}
aspect production ifElseStmt
top::ProductionStmt ::= 'if' '(' condition::Expr ')' th::ProductionStmt 'else' el::ProductionStmt
{
  condition.decSiteVertexInfo = nothing();
  condition.alwaysDecorated = false;
  condition.appDecSiteVertexInfo = nothing();
  condition.dispatchFlowDeps = [];
}
aspect production termAttrValueValueDef
top::ProductionStmt ::= @val::QName e::Expr
{
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
}

-- We're in the unfortunate position of HAVING to compute values for 'flowDefs'
-- even if there are errors in the larger grammar, as remote errors in binding
-- cannot be observed to suppress the analysis of flow.

-- It's not clear how to ideally fix this problem. What we do here is just report
-- harmless junk if we can't determine a good value.

-- Source grammar of a nonterminal's fullName
function hackGramFromFName
String ::= s::String
{
  -- As a safety feature, rather than crash in this instance, report no known grammar
  local i :: Integer = lastIndexOf(":", s);
  return if i > 0 then substring(0, i, s) else "";
}
-- Source grammar of a lookup of an attribute occurrence dcl
fun hackGramFromDcl String ::= qn::Decorated QNameAttrOccur =
  if qn.found then qn.dcl.sourceGrammar else "";
-- Source grammar of a lookup of a local dcl
fun hackGramFromQName String ::= qn::QNameLookup<ValueDclInfo> =
  if qn.found then qn.dcl.sourceGrammar else "";

