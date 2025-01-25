grammar silver:compiler:analysis:warnings:flow;

import silver:compiler:modification:list;

synthesized attribute warnMissingInh :: Boolean occurs on CmdArgs;

aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.warnMissingInh = false;
}
abstract production warnMissingInhFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.warnMissingInh = true;
  forwards to @rest;
}
aspect function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  flags <- [
    flagSpec(name="--warn-missing-inh", paramString=nothing(),
      help="warn about any of several MWDA violations involving demanding inhs",
      flagParser=flag(warnMissingInhFlag))];
}

--------------------------------------------------------------------------------

-- In this file:

-- CHECK 1: Exceeds flowtype
--   - Examine overall dependencies of an equation, and see if they use LHS inh
--     that are not permissible, given the equation's flow type.
--   - Accomplished by explicit calculations in each production.

-- CHECK 1b: Reference set exceeded checks
--   - Direct accesses from references need to be checked, they don't emit dependencies otherwise
--   - Attribute sections need special checking, too
--   - Pattern matching can create dependencies on references, too

-- CHECK 2: Effective Completeness
--   - Ensure each inherited attribute that's used actually has an equation
--     in existence.
--   - Consists of calls to `checkAllEqDeps`
--   - Pattern variable accesses can induced *remote* inherited equation checks

--------------------------------------------------------------------------------

{--
 - Used as a stop-gap measure to ensure equations exist.
 - Given a needed equation (represented by FlowVertex 'v'),
 - ensure such an equation exists, accounting for:
 -  1. Defaults
 -  2. Forwards
 -  3. Reference accesses
 - 
 - This gives rise to 'missing transitive dependency' errors.
 - The reason this exists is to handle 'taking a reference'
 - actions needing to ensure equations were actually provided for
 - things we reference.
 -
 - @param v  A value we need an equation for.
 - @param anonResolve  A list of anonymous decoration sites
 - @param config  Command-line arguments, that affect error reporting
 - @param prodGraphs The final production flow graphs.
 - @param prodName  The full name of the production we're in
 - @param prodNt  The nonterminal this production belongs to. (For functions, a dummy value is ok)
 - @param flowEnv  The local flow environment
 - @param realEnv  The local real environment
 - @returns  Errors for missing equations
 -}
fun checkEqDeps
[Message] ::=
  v::FlowVertex  anonResolve::[(String, Location)]
  config::Decorated CmdArgs  prodName::String
  prodGraphs::EnvTree<ProductionGraph>  flowEnv::FlowEnv  realEnv::Env =
  -- We're concerned with missing inherited equations on RHS, LOCAL, and ANON. (Implicitly, FORWARD.)
  case v of
  -- A dependency on an LHS.INH is a flow issue: these equations do not exist
  -- locally, so we cannot check them.
  | lhsInhVertex(_) -> []
  -- A dependency on an LHS.SYN can be checked locally, but we do not do so here.
  -- All productions must have all SYN equations, so those errors are raised elsewhere.
  | lhsSynVertex(attrName) -> []
  -- A dependency on an RHS.ATTR. SYN are always present, so we only care about INH here.
  | rhsInhVertex(sigName, attrName) ->
      checkInhEq(prodName, rhsVertexType(sigName), attrName, config, prodGraphs, flowEnv, realEnv)
  | rhsSynVertex(sigName, attrName) -> []
  -- A dependency on a LOCAL. Technically, local equations may not exist!
  -- But let's just assume they do, since `local name :: type = expr;` is the preferred syntax.
  | localEqVertex(fName) -> []
  -- A dependency on a LOCAL.ATTR. SYN always exist again, so we only care about INH here.
  | localInhVertex(fName, attrName) -> 
      checkInhEq(prodName, localVertexType(fName), attrName, config, prodGraphs, flowEnv, realEnv)
  | localSynVertex(fName, attrName) -> []
  -- A dependency on a ANON. This do always exist (`decorate expr with..` always has expr.)
  | anonEqVertex(fName) -> []
  -- A dependency on ANON.ATTR. Again, SYN are safe. We need to check only for INH.
  -- If the equation is missing, then we again filter down to just those equations
  -- missing within THIS overall equation.
  -- i.e. `top.syn1 = ... missing ...; top.syn2 = top.syn1;` should only raise
  -- the missing in the first equation.
  | anonInhVertex(fName, attrName) ->
      if !null(lookupLocalInh(prodName, fName, attrName, flowEnv))
      then []
      else let
        anonl :: Maybe<Location> = lookup(fName, anonResolve)
      in if anonl.isJust
        then [mwdaWrn(config, anonl.fromJust, "Decoration requires inherited attribute for " ++ attrName ++ ".")]
        else [] -- If it's not in the list, then it's a transitive dep from a DIFFERENT equation (and thus reported there)
      end
  | anonSynVertex(fName, attrName) -> []
  -- A dependency on a projected equation in another production.
  | subtermInhVertex(parent, termProdName, sigName, attrName) ->
      checkInhEq(prodName, subtermVertexType(parent, termProdName, sigName), attrName, config, prodGraphs, flowEnv, realEnv)
  | subtermSynVertex(parent, termProdName, sigName, attrName) -> []
  end;

fun checkInhEq
[Message] ::=
    prodName::String vt::VertexType attrName::String config::Decorated CmdArgs
    prodGraphs::EnvTree<ProductionGraph>  flowEnv::FlowEnv realEnv::Env =
  case resolveInhEq(prodName, vt, attrName, prodGraphs, flowEnv, realEnv) of
  | alwaysDec() -> []
  | missing -> [mwdaWrnAmbientOrigin(config, s"Equation requires inherited attribute ${attrName} be supplied to ${prettyDecSites(0, missing)}")]
  end;

function checkAllEqDeps
[Message] ::=
  vs::[FlowVertex]  flowDefs::[FlowDef]
  config::Decorated CmdArgs  prodName::String  prodGraphs::EnvTree<ProductionGraph>  flowEnv::FlowEnv  realEnv::Env
{
  -- If a shared tree is missing an inherited equation, then the equation is also
  -- missing for the sharing decoration site vertex on which it depends.
  -- We want to suppress reporting the error again on the decoration site vertex,
  -- since that error wouldn't list the original vertex as a place where the
  -- attribute could be supplied.
  local alreadyReported::[FlowVertex] = do {
    v :: FlowVertex <- vs;
    refInh::(VertexType, String) <-
      case v of
      | rhsInhVertex(sigName, attrName) -> [(rhsVertexType(sigName), attrName)]
      | localInhVertex(fName, attrName) -> [(localVertexType(fName), attrName)]
      | anonInhVertex(fName, attrName) -> [(anonVertexType(fName), attrName)]
      | _ -> []
      end;
    decSite::VertexType <- lookupRefDecSite(prodName, refInh.1, flowEnv);
    guard(!decSiteHasInhEq(prodName, refInh.1, refInh.2, prodGraphs, flowEnv, realEnv));
    expandGraph([decSite.inhVertex(refInh.2)], findProductionGraph(prodName, prodGraphs));
  };
  local anonResolve::[(String, Location)] = collectAnonOrigin(flowDefs);
  return flatMap(
    checkEqDeps(_, anonResolve, config, prodName, prodGraphs, flowEnv, realEnv),
    removeAll(alreadyReported, vs));
}

{--
 - Look up flow types, either from the flow environment (for a nonterminal) or the occurs-on contexts (for a type var).
 - @param syn  A synthesized attribute's full name
 - @param t  The type to look up this attribute on
 - @param flow  The flow type environment (NOTE: TODO: this is currently 'top.grammarFlowTypes' or something, NOT top.flowEnv)
 - @param ns    The named signature of the enclosing production
 - @param env   The regular (type) environment
 - @return A set of inherited attributes (if the inh dependencies for the attribute are bounded) and a list of type variables of kind InhSet,
 - needed to compute this synthesized attribute on this type.
 -}
function inhDepsForSynOnType
(Maybe<set:Set<String>>, [TyVar]) ::= syn::String  t::Type  flow::EnvTree<FlowType>  ns::NamedSignature env::Env
{
  local contexts::Contexts = foldContexts(ns.contexts);
  contexts.env = env;

  return
    if t.isNonterminal || (t.isDecorated && t.decoratedType.isNonterminal)
    then (just(inhDepsForSyn(syn, t.typeName, flow)), [])
    else (
      map(set:fromList, lookup(syn, lookupAll(t.typeName, contexts.occursContextInhDeps))),
      concat(lookupAll(syn, lookupAll(t.typeName, contexts.occursContextInhSetDeps))));
}


--------------------------------------------------------------------------------


aspect production globalValueDclConcrete
top::AGDcl ::= 'global' id::Name '::' cl::ConstraintList '=>' t::TypeExpr '=' e::Expr ';'
{
  -- oh no again!
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] = expandGraph(e.flowDeps, e.frame.flowGraph);

  top.errors <-
    if top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, fName, myGraphs, top.flowEnv, top.env)
    else [];
}

aspect production defaultConstraintClassBodyItem
top::ClassBodyItem ::= id::Name '::' cl::ConstraintList '=>' ty::TypeExpr '=' e::Expr ';'
{
  -- oh no again!
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] = expandGraph(e.flowDeps, e.frame.flowGraph);

  top.errors <-
    if top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, fName, myGraphs, top.flowEnv, top.env)
    else [];
}

aspect production instanceBodyItem
top::InstanceBodyItem ::= id::QName '=' e::Expr ';'
{
  -- oh no again!
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] = expandGraph(e.flowDeps, e.frame.flowGraph);

  top.errors <-
    if top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, id.lookupValue.fullName, myGraphs, top.flowEnv, top.env)
    else [];
}

aspect production synthesizedAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] =
    expandGraph(e.flowDeps, top.frame.flowGraph);
  
  local lhsInhDeps :: set:Set<String> = onlyLhsInh(transitiveDeps);
  local lhsInhExceedsFlowType :: [String] = set:toList(set:difference(lhsInhDeps, inhDepsForSyn(attr.attrDcl.fullName, top.frame.lhsNtName, myFlow)));

  top.errors <-
    if dl.found && attr.found && top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, top.frame.fullName, myGraphs, top.flowEnv, top.env) ++
      if null(lhsInhExceedsFlowType) then []
      else [mwdaWrnFromOrigin(top, "Synthesized equation " ++ attr.name ++ " exceeds flow type with dependencies on " ++ implode(", ", lhsInhExceedsFlowType))]
    else [];
}

aspect production inheritedAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] = 
    expandGraph(e.flowDeps, top.frame.flowGraph);
  
  local lhsInhDeps :: set:Set<String> = onlyLhsInh(transitiveDeps);

  -- problem = lhsinh deps - fwd flow type - this inh attribute
  local lhsInhExceedsForwardFlowType :: [String] = 
    set:toList(
      set:removeAll(
        [dl.inhAttrName],
        set:difference(
          lhsInhDeps,
          inhDepsForSyn("forward", top.frame.lhsNtName, myFlow))));

  -- Make sure we aren't introducing any hidden transitive dependencies.

  local vertexHasHideableEq :: (Boolean ::= VertexType String) =
    possibleDecSiteHasInhEq(top.frame.fullName, _, _, myGraphs, top.flowEnv, top.env);

  local refDecSiteInhDepsLhsInh :: Maybe<set:Set<String>> =
    case filter(
      vertexHasHideableEq(_, attr.attrDcl.fullName),
      lookupRefPossibleDecSites(top.frame.fullName, dl.defLHSVertex, top.flowEnv)) of
    | [] -> nothing()
    | vs -> just(onlyLhsInh(expandGraph(
        dl.defLHSVertex.eqVertex ++
        map(\ v::VertexType -> v.inhVertex(attr.attrDcl.fullName), vs),
        top.frame.flowGraph)))
    end;

  local transBaseRefDecSiteInhDepsLhsInh :: Maybe<set:Set<String>> =
    case dl.defLHSVertex of
    | transAttrVertexType(v, transAttr) ->
      case filter(
        vertexHasHideableEq(_, dl.inhAttrName),
        lookupRefPossibleDecSites(top.frame.fullName, v, top.flowEnv)) of
      | [] -> nothing()
      | vs -> just(onlyLhsInh(expandGraph(
          v.eqVertex ++
          map(\ v::VertexType -> v.inhVertex(dl.inhAttrName), vs),
          top.frame.flowGraph)))
      end
    | _ -> nothing()
    end;

  -- problem = lhsinh deps - inh deps on dec site
  local lhsInhExceedsRefDecSiteDeps :: [String] =
    case refDecSiteInhDepsLhsInh of
    | just(deps) -> set:toList(set:difference(lhsInhDeps, deps))
    | _ -> []
    end;

  local lhsInhExceedsTransBaseRefDecSiteDeps :: [String] =
    case transBaseRefDecSiteInhDepsLhsInh of
    | just(deps) -> set:toList(set:difference(lhsInhDeps, deps))
    | _ -> []
    end;
  
  -- Extension productions that implement a dispatch signature

  local ns :: NamedSignature =  -- top.frame.signature might have aspect sig names that don't match the flow env
    case getValueDcl(top.frame.fullName, top.env) of
    | dcl :: _ -> dcl.namedSignature
    | _ -> error("didn't find a decl for prod " ++ top.frame.fullName)
    end;
  local implementedSig :: Maybe<NamedSignature> =
    case getValueDcl(top.frame.fullName, top.env) of
    | dcl :: _ -> dcl.implementedSignature
    | _ -> nothing()
    end;
  local dispatchHostSigInhDepsLhsInh :: Maybe<set:Set<String>> =
    case implementedSig of
    | just(dispatchSig) ->
      case dl.defLHSVertex of
      | rhsVertexType(sigName)
          when lookupSignatureInputElem(sigName, ns).elementShared ->
        just(onlyLhsInh(expandGraph(
          [rhsInhVertex(
            head(drop(positionOf(sigName, ns.inputNames), dispatchSig.inputNames)),
            attr.attrDcl.fullName)],
          findProductionGraph(dispatchSig.fullName, myGraphs))))
      | transAttrVertexType(rhsVertexType(sigName), transAttr)
          when lookupSignatureInputElem(sigName, ns).elementShared ->
        just(onlyLhsInh(expandGraph(
          [rhsInhVertex(
            head(drop(positionOf(sigName, ns.inputNames), dispatchSig.inputNames)),
            transAttr ++ "." ++ attr.attrDcl.fullName)],
          findProductionGraph(dispatchSig.fullName, myGraphs))))
      | _ -> nothing()
      end
    | _ -> nothing()
    end;

  -- problem = lhsinh deps - inh deps on host implementation prods
  local lhsInhExceedsDispatchHostSigInhDeps :: [String] =
    case dispatchHostSigInhDepsLhsInh of
    | just(deps) -> set:toList(set:difference(lhsInhDeps, deps))
    | _ -> []
    end;

  top.errors <-
    if top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, top.frame.fullName, myGraphs, top.flowEnv, top.env)
    else [];
  top.errors <-
    if top.config.warnMissingInh && dl.name == "forward" && !null(lhsInhExceedsForwardFlowType)
    then [mwdaWrnFromOrigin(top, "Forward inherited equation for " ++ dl.inhAttrName ++ " exceeds flow type with dependencies on " ++ implode(", ", lhsInhExceedsForwardFlowType))]
    else [];
  top.errors <-
    if top.config.warnMissingInh && !null(lhsInhExceedsRefDecSiteDeps)
    then
      [mwdaWrnFromOrigin(top,
        s"Inherited override equation for ${attr.attrDcl.fullName} on ${dl.defLHSVertex.vertexPP} may exceed a flow type " ++
        s"with hidden transitive dependencies on ${implode(", ", lhsInhExceedsRefDecSiteDeps)}; " ++
        s"on some reference to this tree, this attribute may be expected to depend ${depListStr(refDecSiteInhDepsLhsInh.fromJust)}" ++
        s" (from ${implode(", ", map((.vertexPP), lookupRefPossibleDecSites(top.frame.fullName, dl.defLHSVertex, top.flowEnv)))})")]
    else [];
  top.errors <-
    case dl.defLHSVertex of
    | transAttrVertexType(v, transAttr)
        when top.config.warnMissingInh && !null(lhsInhExceedsTransBaseRefDecSiteDeps) ->
      [mwdaWrnFromOrigin(top,
        s"Inherited override equation for ${transAttr}.${attr.attrDcl.fullName} on ${v.vertexPP} may exceed a flow type " ++
        s"with hidden transitive dependencies on ${implode(", ", lhsInhExceedsTransBaseRefDecSiteDeps)}; " ++
        s"on some reference to this tree, this attribute may be expected to depend ${depListStr(transBaseRefDecSiteInhDepsLhsInh.fromJust)}" ++
        s" (from ${implode(", ", map((.vertexPP), lookupRefPossibleDecSites(top.frame.fullName, v, top.flowEnv)))})")]
    | _ -> []
    end;
  top.errors <-
    case implementedSig of
    | just(sig) when top.config.warnMissingInh && !null(lhsInhExceedsDispatchHostSigInhDeps) ->
      [mwdaWrnFromOrigin(top,
        s"Inherited override equation for ${attr.attrDcl.fullName} on ${dl.defLHSVertex.vertexPP} may exceed a flow type " ++
        s"with hidden transitive dependencies on ${implode(", ", lhsInhExceedsDispatchHostSigInhDeps)}; " ++
        s"in a production that dispatched to this one, this attribute may be expected to depend ${depListStr(dispatchHostSigInhDepsLhsInh.fromJust)}" ++
        s" (from ${sig.fullName})")]
    | _ -> []
    end;
}

fun depListStr String ::= deps::set:Set<String> =
  case set:toList(deps) of
  | [] -> "on no left-side inherited attributes"
  | deps -> "only on " ++ implode(", ", deps)
  end;

fun vertexHasPossibleInhEq Boolean ::= v::VertexType env::Env =
  case v of
  | subtermVertexType(_, prodName, sigName) ->
      case getTypeDcl(prodName, env), getValueDcl(prodName, env) of
      | dcl :: _, _ -> !lookupSignatureInputElem(sigName, dcl.dispatchSignature).elementShared
      | _, dcl :: _ -> !lookupSignatureInputElem(sigName, dcl.namedSignature).elementShared
      | _, _ -> false
      end
  | _ -> true
  end;

----- WARNING TODO BEGIN MASSIVE COPY & PASTE SESSION
aspect production synBaseColAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] =
    expandGraph(e.flowDeps, top.frame.flowGraph);
  
  local lhsInhDeps :: set:Set<String> = onlyLhsInh(transitiveDeps);
  local lhsInhExceedsFlowType :: [String] = set:toList(set:difference(lhsInhDeps, inhDepsForSyn(attr.attrDcl.fullName, top.frame.lhsNtName, myFlow)));

  top.errors <-
    if dl.found && attr.found && top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, top.frame.fullName, myGraphs, top.flowEnv, top.env) ++
      if null(lhsInhExceedsFlowType) then []
      else [mwdaWrnFromOrigin(top, "Synthesized equation " ++ attr.name ++ " exceeds flow type with dependencies on " ++ implode(", ", lhsInhExceedsFlowType))]
    else [];
}
aspect production synAppendColAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] =
    expandGraph(e.flowDeps, top.frame.flowGraph);
  
  local lhsInhDeps :: set:Set<String> = onlyLhsInh(transitiveDeps);
  local lhsInhExceedsFlowType :: [String] = set:toList(set:difference(lhsInhDeps, inhDepsForSyn(attr.attrDcl.fullName, top.frame.lhsNtName, myFlow)));

  top.errors <-
    if dl.found && attr.found && top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, top.frame.fullName, myGraphs, top.flowEnv, top.env) ++
      if null(lhsInhExceedsFlowType) then []
      else [mwdaWrnFromOrigin(top, "Synthesized equation " ++ attr.name ++ " exceeds flow type with dependencies on " ++ implode(", ", lhsInhExceedsFlowType))]
    else [];
}
aspect production inhBaseColAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] = 
    expandGraph(e.flowDeps, top.frame.flowGraph);
  
  local lhsInhDeps :: set:Set<String> = onlyLhsInh(transitiveDeps);
  -- problem = lhsinh deps - fwd flow type - this inh attribute
  local lhsInhExceedsForwardFlowType :: [String] = 
    set:toList(
      set:removeAll(
        [dl.inhAttrName],
        set:difference(
          lhsInhDeps,
          inhDepsForSyn("forward", top.frame.lhsNtName, myFlow))));

  top.errors <-
    if top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, top.frame.fullName, myGraphs, top.flowEnv, top.env) ++
         if dl.name != "forward" || null(lhsInhExceedsForwardFlowType) then []
         else [mwdaWrnFromOrigin(top, "Forward inherited equation for " ++ dl.inhAttrName ++ " exceeds flow type with dependencies on " ++ implode(", ", lhsInhExceedsForwardFlowType))]
    else [];
  
  -- TOOD: Hidden transitive deps check?
}
aspect production inhAppendColAttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] = 
    expandGraph(e.flowDeps, top.frame.flowGraph);
  
  local lhsInhDeps :: set:Set<String> = onlyLhsInh(transitiveDeps);
  -- problem = lhsinh deps - fwd flow type - this inh attribute
  local lhsInhExceedsForwardFlowType :: [String] = 
    set:toList(
      set:removeAll(
        [dl.inhAttrName],
        set:difference(
          lhsInhDeps,
          inhDepsForSyn("forward", top.frame.lhsNtName, myFlow))));

  top.errors <-
    if top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, top.frame.fullName, myGraphs, top.flowEnv, top.env) ++
         if dl.name != "forward" || null(lhsInhExceedsForwardFlowType) then []
         else [mwdaWrnFromOrigin(top, "Forward inherited equation exceeds for " ++ dl.inhAttrName ++ " flow type with dependencies on " ++ implode(", ", lhsInhExceedsForwardFlowType))]
    else [];
  
  -- TOOD: Hidden transitive deps check?
}
------ END AWFUL COPY & PASTE SESSION

aspect production forwardsTo
top::ProductionStmt ::= 'forwards' 'to' e::Expr ';'
{
  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] =
    expandGraph(e.flowDeps, top.frame.flowGraph);
  
  local lhsInhDeps :: set:Set<String> = onlyLhsInh(transitiveDeps);
  local lhsInhExceedsFlowType :: [String] = set:toList(set:difference(lhsInhDeps, inhDepsForSyn("forward", top.frame.lhsNtName, myFlow)));

  top.errors <-
    if top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, top.frame.fullName, myGraphs, top.flowEnv, top.env) ++
         if null(lhsInhExceedsFlowType) then []
         else [mwdaWrnFromOrigin(top, "Forward equation exceeds flow type with dependencies on " ++ implode(", ", lhsInhExceedsFlowType))]
    else [];
}
aspect production forwardInh
top::ForwardInh ::= lhs::ForwardLHSExpr '=' e::Expr ';'
{
  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] =
    expandGraph(e.flowDeps, top.frame.flowGraph);
  
  local lhsInhDeps :: set:Set<String> = onlyLhsInh(transitiveDeps);
  -- problem = lhsinh deps - fwd flow type - this inh attribute
  local lhsInhExceedsFlowType :: [String] = 
    set:toList(
      set:removeAll(
        [case lhs of
         | forwardLhsExpr(q) -> q.attrDcl.fullName
         end],
        set:difference(
          lhsInhDeps,
          inhDepsForSyn("forward", top.frame.lhsNtName, myFlow))));

  top.errors <-
    if top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, top.frame.fullName, myGraphs, top.flowEnv, top.env) ++
         if null(lhsInhExceedsFlowType) then []
         else [mwdaWrnFromOrigin(top, "Forward inherited equation exceeds flow type with dependencies on " ++ implode(", ", lhsInhExceedsFlowType))]
    else [];
}

aspect production localValueDef
top::ProductionStmt ::= @val::QName e::Expr
{
  -- oh no again!
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] =
    expandGraph(e.flowDeps, top.frame.flowGraph);
  
  -- check transitive deps only. No worries about flow types.
  top.errors <-
    if top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, top.frame.fullName, myGraphs, top.flowEnv, top.env)
    else [];
}

aspect production returnDef
top::ProductionStmt ::= 'return' e::Expr ';'
{
  -- oh no again!
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] =
    expandGraph(e.flowDeps, top.frame.flowGraph);

  top.errors <-
    if top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, top.frame.fullName, myGraphs, top.flowEnv, top.env)
    else [];
}

aspect production attachNoteStmt
top::ProductionStmt ::= 'attachNote' e::Expr ';'
{
  -- oh no again!
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local transitiveDeps :: [FlowVertex] =
    expandGraph(e.flowDeps, top.frame.flowGraph);

  top.errors <-
    if top.config.warnMissingInh
    then checkAllEqDeps(transitiveDeps, e.flowDefs, top.config, top.frame.fullName, myGraphs, top.flowEnv, top.env)
    else [];
}

-- Skipping `baseCollectionValueDef`: it forwards to `localValueDef`
-- Partially skipping `appendCollectionValueDef`: it likewise forwards
-- But we do have a special "exceeds check" to do here:
aspect production appendCollectionValueDef
top::ProductionStmt ::= @val::QName e::Expr
{
  local productionFlowGraph :: ProductionGraph = top.frame.flowGraph;
  local transitiveDeps :: [FlowVertex] = expandGraph(e.flowDeps, productionFlowGraph);
  
  local originalEqDeps :: [FlowVertex] = 
    expandGraph([localEqVertex(val.lookupValue.fullName)], productionFlowGraph);
  
  local lhsInhDeps :: set:Set<String> = onlyLhsInh(transitiveDeps);
  
  local originalEqLhsInhDeps :: set:Set<String> = onlyLhsInh(originalEqDeps);
  
  local lhsInhExceedsFlowType :: [String] = set:toList(set:difference(lhsInhDeps, originalEqLhsInhDeps));

  top.errors <-
    if top.config.warnMissingInh
       -- We can ignore functions. We're checking LHS inhs here... functions don't have any!
    && top.frame.hasFullSignature
    then if null(lhsInhExceedsFlowType) then []
         else [mwdaWrnFromOrigin(top, "Local contribution (" ++ val.name ++ " <-) equation exceeds flow dependencies with: " ++ implode(", ", lhsInhExceedsFlowType))]
    else [];
}


--------------------------------------------------------------------------------


{-
Step 2: Let's go check on expressions. This has two purposes:
1. Better error messages for missing equations than the "transitive dependency" ones.
   But technically, unneeded and transititve dependencies are covering this.
2. We have to ensure that each individual access from a reference fits within the inferred reference set.
   Additionally we must check that wherever we take a reference, the required reference set is bounded.
   This is not covered by any other checks.
-}

aspect production childReference
top::Expr ::= @q::QName
{
  top.errors <-
    if top.config.warnMissingInh
    && isDecorable(q.lookupValue.typeScheme.typerep, top.env)
    then if refSet.isJust then []
         else [mwdaWrnFromOrigin(top, s"Cannot take a reference of type ${prettyType(top.finalType)}, as the reference set is not bounded.")]
    else [];
}
aspect production lhsReference
top::Expr ::= @q::QName
{
  top.errors <-
    if top.config.warnMissingInh
    then if refSet.isJust then []
         else [mwdaWrnFromOrigin(top, s"Cannot take a reference of type ${prettyType(top.finalType)}, as the reference set is not bounded.")]
    else [];
}
aspect production localReference
top::Expr ::= @q::QName
{
  top.errors <-
    if top.config.warnMissingInh
    && isDecorable(q.lookupValue.typeScheme.typerep, top.env)
    then if refSet.isJust then []
         else [mwdaWrnFromOrigin(top, s"Cannot take a reference of type ${prettyType(top.finalType)}, as the reference set is not bounded.")]
    else [];
}
aspect production forwardReference
top::Expr ::= @q::QName
{
  top.errors <-
    if top.config.warnMissingInh
    then if refSet.isJust then []
         else [mwdaWrnFromOrigin(top, s"Cannot take a reference of type ${prettyType(top.finalType)}, as the reference set is not bounded.")]
    else [];
}

aspect production forwardAccess
top::Expr ::= e::Expr '.' 'forward'
{
  -- TODO?
}

aspect production synDecoratedAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  -- oh no again
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local deps :: (Maybe<set:Set<String>>, [TyVar]) =
    inhDepsForSynOnType(q.attrDcl.fullName, e.finalType, myFlow, top.frame.signature, top.env);
  local inhDeps :: set:Set<String> = fromMaybe(set:empty(), deps.1);  -- Need to check that we have bounded inh deps, i.e. deps.1 == just(...)

-- This aspect is in two parts. First: we *must* check that any accesses
-- on a unknown decorated tree are in the ref-set.
  local acceptable :: ([String], [TyVar]) =
    case e.finalType of
    | decoratedType(_, i) -> getMinInhSetMembers([], ^i, top.env)
    | _ -> ([], [])
    end;
  local diff :: [String] =
    set:toList(set:removeAll(acceptable.1,  -- blessed inhs for a reference
      inhDeps)); -- needed inhs
  
  -- CASE 1: References. This check is necessary and won't be caught elsewhere.
  top.errors <- 
    if null(e.errors)
    && top.config.warnMissingInh
    then
      case e.flowVertexInfo of
      -- We don't track dependencies on inh sets transitively, so we need to check that the inh deps are bounded here;
      -- an access with unbounded inh deps only ever makes sense on a reference. 
      | just(_) ->
          if deps.1.isJust then []
          else [mwdaWrnFromOrigin(top, "Access of " ++ q.name ++ " from " ++ prettyType(e.finalType) ++ " requires an unbounded set of inherited attributes")]
      -- without a vertex, we're accessing from a reference, and so...
      | nothing() ->
          if any(map(contains(_, deps.2), acceptable.2)) then []  -- The deps are supplied as a common InhSet var
          -- We didn't find the deps as an InhSet var
          else if null(diff)
            then if deps.fst.isJust then []  -- We have a bound on the inh deps, and they are all present
            -- We don't have a bound on the inh deps, flag the unsatisfied InhSet deps
            else if null(acceptable.2)
            then [mwdaWrnFromOrigin(top, "Access of " ++ q.name ++ " from " ++ prettyType(e.finalType) ++ " requires an unbounded set of inherited attributes")]
            else [mwdaWrnFromOrigin(top, "Access of " ++ q.name ++ " from reference of type " ++ prettyType(e.finalType) ++ " requires one of the following sets of inherited attributes not known to be supplied to this reference: " ++ implode(", ", map(findAbbrevFor(_, top.frame.signature.freeVariables), deps.snd)))]
          -- We didn't find the inh deps
          else [mwdaWrnFromOrigin(top, "Access of " ++ q.name ++ " from reference of type " ++ prettyType(e.finalType) ++ " requires inherited attributes not known to be supplied to this reference: " ++ implode(", ", diff))]
      end
    else [];

----------------

  -- CASE 2: More specific errors for things already caught by `checkAllEqDeps`.
  -- Equation has transitive dep on `i`, but here we can say where this dependency
  -- originated: from a syn access.
  top.errors <- 
    if null(e.errors) && top.config.warnMissingInh
    then
      case e.flowVertexInfo of
      | just(vt) when
          case vt of
          | rhsVertexType(_) -> true
          | localVertexType(_) -> true
          | _ -> false
          end ->
        case decSitesMissingInhEqs(top.frame.fullName, vt, set:toList(inhDeps), myGraphs, top.flowEnv, top.env) of
        | [] -> []
        | missingEqs -> map(\ di::(DecSiteTree, [String]) ->
            mwdaWrnFromOrigin(top,
              "Access of synthesized attribute " ++ q.name ++ " on " ++ e.unparse ++
              " requires missing inherited attribute(s) " ++ implode(", ", di.2) ++
              " to be supplied to " ++ prettyDecSites(0, di.1)),
            missingEqs)
        end
      | _ -> []
      end
    else [];
}

aspect production inhDecoratedAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  -- In this case, ONLY check for references.
  -- The transitive deps error will be less difficult to figure out when there's
  -- an explicit access to the attributes.
  top.errors <- 
    if null(e.errors) && top.config.warnMissingInh
    then
      case e.flowVertexInfo of
      | just(_) -> [] -- no check to make, as it was done transitively
      -- without a vertex, we're accessing from a reference, and so...
      | nothing() ->
          if contains(q.attrDcl.fullName, getMinRefSet(e.finalType, top.env))
          then []
          else [mwdaWrnFromOrigin(top, "Access of inherited attribute " ++ q.name ++ " on reference of type " ++ prettyType(e.finalType) ++ " is not permitted")]
      end
    else [];
}

aspect production transDecoratedAccessHandler
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  -- oh no again
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local deps :: (Maybe<set:Set<String>>, [TyVar]) =
    inhDepsForSynOnType(q.attrDcl.fullName, e.finalType, myFlow, top.frame.signature, top.env);
  local inhDeps :: set:Set<String> =
    -- Inh deps for computing this syn attribute
    fromMaybe(set:empty(), deps.1) ++  -- Need to check that we have bounded inh deps, i.e. deps.1 == just(...)
    -- When taking a reference to this translation attribute access, we depend on the ref set inhs on e.
    set:fromList(map(\ inh::String -> s"${q.attrDcl.fullName}.${inh}", fromMaybe([], refSet)));

  -- Need to check that the reference set is bounded when taking a reference, as with locals/children/etc.
  top.errors <-
    if top.config.warnMissingInh
    then if refSet.isJust then []
         else [mwdaWrnFromOrigin(top, s"Cannot take a reference of type ${prettyType(e.finalType)}, as the reference set is not bounded.")]
    else [];

  -- TODO: check that reference set is only inhs?

  -- This logic exactly mirrors synDecoratedAccessHandler, except with inhDeps containing extra inh dependencies from taking a reference.

-- This aspect is in two parts. First: we *must* check that any accesses
-- on a unknown decorated tree are in the ref-set.
  local acceptable :: ([String], [TyVar]) =
    case e.finalType of
    | decoratedType(_, i) -> getMinInhSetMembers([], ^i, top.env)
    | _ -> ([], [])
    end;
  local diff :: [String] =
    set:toList(set:removeAll(acceptable.1,  -- blessed inhs for a reference
      inhDeps)); -- needed inhs
  
  -- CASE 1: References. This check is necessary and won't be caught elsewhere.
  top.errors <- 
    if null(e.errors)
    && top.config.warnMissingInh
    then
      case e.flowVertexInfo of
      -- We don't track dependencies on inh sets transitively, so we need to check that the inh deps are bounded here;
      -- an access with unbounded inh deps only ever makes sense on a reference. 
      | just(_) ->
          if deps.1.isJust then []
          else [mwdaWrnFromOrigin(top, "Access of " ++ q.name ++ " from " ++ prettyType(e.finalType) ++ " requires an unbounded set of inherited attributes")]
      -- without a vertex, we're accessing from a reference, and so...
      | nothing() ->
          if any(map(contains(_, deps.2), acceptable.2)) then []  -- The deps are supplied as a common InhSet var
          -- We didn't find the deps as an InhSet var
          else if null(diff)
            then if deps.fst.isJust then []  -- We have a bound on the inh deps, and they are all present
            -- We don't have a bound on the inh deps, flag the unsatisfied InhSet deps
            else if null(acceptable.2)
            then [mwdaWrnFromOrigin(top, "Access of " ++ q.name ++ " from " ++ prettyType(e.finalType) ++ " requires an unbounded set of inherited attributes")]
            else [mwdaWrnFromOrigin(top, "Access of " ++ q.name ++ " from reference of type " ++ prettyType(e.finalType) ++ " requires one of the following sets of inherited attributes not known to be supplied to this reference: " ++ implode(", ", map(findAbbrevFor(_, top.frame.signature.freeVariables), deps.snd)))]
          -- We didn't find the inh deps
          else [mwdaWrnFromOrigin(top, "Access of " ++ q.name ++ " from reference of type " ++ prettyType(e.finalType) ++ " requires inherited attributes not known to be supplied to this reference: " ++ implode(", ", diff))]
      end
    else [];

----------------

  -- CASE 2: More specific errors for things already caught by `checkAllEqDeps`.
  -- Equation has transitive dep on `i`, but here we can say where this dependency
  -- originated: from a syn access.
  top.errors <- 
    if null(e.errors) && top.config.warnMissingInh
    then
      case e.flowVertexInfo of
      | just(vt) when
          case vt of
          | rhsVertexType(_) -> true
          | localVertexType(_) -> true
          | _ -> false
          end ->
        case decSitesMissingInhEqs(top.frame.fullName, vt, set:toList(inhDeps), myGraphs, top.flowEnv, top.env) of
        | [] -> []
        | missingEqs -> map(\ di::(DecSiteTree, [String]) ->
            mwdaWrnFromOrigin(top,
              "Access of translation attribute " ++ q.name ++ " on " ++ e.unparse ++
              " requires missing inherited attribute(s) " ++ implode(", ", di.2) ++
              " to be supplied to " ++ prettyDecSites(0, di.1)),
            missingEqs)
        end
      | _ -> []
      end
    else [];
}


aspect production decorateExprWith
top::Expr ::= 'decorate' e::Expr 'with' '{' inh::ExprInhs '}'
{
  -- Do nothing. Everything gets taken care of with anonResolve and checkEqDeps at the top-level of the equation
}

aspect production decorationSiteExpr
top::Expr ::= '@' e::Expr
{
  -- Check for an inherited attribute supplied via sharing, that may be needed to determine dispatching.

  -- The dependencies for determining the production(s) under which this tree is shared:
  local dispatchDeps :: set:Set<FlowVertex> =
    set:fromList(expandGraph(top.dispatchFlowDeps, top.frame.flowGraph));
  
  -- All inherited attributes known locally to occur on the shared tree.
  -- We don't need *all* inherited attributes, because only the ones we know about
  -- could be a dependency for dispatching.
  local sharedRefInhs :: [String] = getInhAndInhOnTransAttrsOn(e.finalType.typeName, top.env);

  -- Inherited attributes on the shared tree that might be depended upon by dispatching.
  local dispatchDepsOnRef :: [String] =
    case e.flowVertexInfo of
    | just(localVertexType(fName)) when isForwardProdAttr(fName, top.env) -> []
    | just(vt) -> filter(\ i::String ->
        set:contains(vt.inhVertex(i), dispatchDeps) &&
        !vertexHasInhEq(top.frame.fullName, vt, i, top.flowEnv),
        sharedRefInhs)
    | _ -> []
    end;

  top.errors <-
    if top.config.warnMissingInh
    then
      case e.flowVertexInfo of
      | just(vt) when !null(dispatchDepsOnRef) ->
        [mwdaWrnFromOrigin(top, s"Dispatching may require inherited attribute(s) ${implode(", ", dispatchDepsOnRef)} on ${vt.vertexName}, but these attribute(s) are supplied here after dispatching")]
      | _ -> []
      end
    else [];

  -- Sharing a forward production attribute somewhere that isn't already being decorated as the forward
  -- may cause hidden transitive dependency issues for attributes we don't know about, so we forbid this.
  top.errors <- 
    if top.config.warnMissingInh
    then
      case e.flowVertexInfo of
      | just(localVertexType(fName)) when isForwardProdAttr(fName, top.env) ->
        case top.decSiteVertexInfo of
        | just(forwardVertexType_real()) -> []
        | just(localVertexType(dSiteFName)) when isForwardProdAttr(dSiteFName, top.env) -> []
        | _ -> [mwdaWrnFromOrigin(top, s"Forward production attribute ${fName} may only be shared in a forward decoration site")]
        end
      | _ -> []
      end
    else [];
}

aspect production presentAppExpr
top::AppExpr ::= e::Expr
{
  -- Same checks as for decorationSiteExpr, for application of a prod with a shared signature param.

  -- The dependencies for determining the production(s) under which this tree is shared:
  local dispatchDeps :: set:Set<FlowVertex> =
    set:fromList(expandGraph(top.dispatchFlowDeps, top.frame.flowGraph));
  
  -- All inherited attributes known locally to occur on the shared tree.
  -- We don't need *all* inherited attributes, because only the ones we know about
  -- could be a dependency for dispatching.
  local sharedRefInhs :: [String] = getInhAndInhOnTransAttrsOn(e.finalType.typeName, top.env);

  -- Inherited attributes on the shared tree that might be depended upon by dispatching.
  local dispatchDepsOnRef :: [String] =
    case e.flowVertexInfo of
    | just(localVertexType(fName)) when isForwardProdAttr(fName, top.env) -> []
    | just(vt) -> filter(\ i::String ->
        set:contains(vt.inhVertex(i), dispatchDeps) &&
        !vertexHasInhEq(top.frame.fullName, vt, i, top.flowEnv),
        sharedRefInhs)
    | _ -> []
    end;

  top.errors <-
    if top.config.warnMissingInh && sigIsShared && isForwardParam
    then
      case e.flowVertexInfo of
      | just(vt) when !null(dispatchDepsOnRef) ->
        [mwdaWrnFromOrigin(top, s"Dispatching may require inherited attribute(s) ${implode(", ", dispatchDepsOnRef)} on ${vt.vertexName}, but these attribute(s) are supplied here after dispatching")]
      | _ -> []
      end
    else [];

  -- Sharing a forward production attribute somewhere that isn't already being decorated as the forward
  -- may cause hidden transitive dependency issues for attributes we don't know about, so we forbid this.
  top.errors <- 
    if top.config.warnMissingInh && sigIsShared && isForwardParam
    then
      case e.flowVertexInfo of
      | just(localVertexType(fName)) when isForwardProdAttr(fName, top.env) ->
        case top.decSiteVertexInfo of
        | just(forwardVertexType_real()) -> []
        | just(localVertexType(dSiteFName)) when isForwardProdAttr(dSiteFName, top.env) -> []
        | _ -> [mwdaWrnFromOrigin(top, s"Forward production attribute ${fName} may only be shared in a forward decoration site")]
        end
      | _ -> []
      end
    else [];
}

{--
 - For pattern matching, we have an obligation to check:
 - 1. If we invented an anon vertex type for the scrutinee, then it's a sink, and
 -    we need to check that nothing more than the ref set was depended upon.
 -}
aspect production matchPrimitiveReal
top::Expr ::= e::Expr t::TypeExpr pr::PrimPatterns f::Expr
{
  -- slightly awkward way to recover the name and whether/not it was invented
  local sinkVertexName :: Maybe<String> =
    case e.flowVertexInfo, pr.scrutineeVertexType of
    | nothing(), anonVertexType(n) -> just(n)
    | _, _ -> nothing()
    end;

  -- These should be the only ones that can reference our anon sink
  local transitiveDeps :: [FlowVertex] =
    expandGraph(top.flowDeps, top.frame.flowGraph);
  
  pr.receivedDeps = transitiveDeps;

  -- just the deps on inhs of our sink
  local inhDeps :: [String] = toAnonInhs(transitiveDeps, sinkVertexName.fromJust);

  -- Subtract the ref set from our deps
  local diff :: [String] =
    set:toList(set:removeAll(getMinRefSet(^scrutineeType, top.env), set:add(inhDeps, set:empty())));

  top.errors <-
    if null(e.errors)
    && top.config.warnMissingInh
    && sinkVertexName.isJust
    && !null(diff)
    then [mwdaWrnFromOrigin(e, "Pattern match on reference of type " ++ prettyType(^scrutineeType) ++ " has transitive dependencies on " ++ implode(", ", diff))]
    else [];

}

fun toAnonInhs [String] ::= vs::[FlowVertex]  vertex::String =
  filterMap(\ v::FlowVertex ->
    case v of
    | anonInhVertex(n, inh) when n == vertex -> just(inh)
    | _ -> nothing()
    end, vs);

inherited attribute receivedDeps :: [FlowVertex] occurs on VarBinders, VarBinder, PrimPatterns, PrimPattern;
propagate @receivedDeps on VarBinders, VarBinder, PrimPatterns, PrimPattern;

aspect production varVarBinder
top::VarBinder ::= n::Name
{
  -- oh no again!
  local myGraphs::EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  -- Check that we're not taking an unbounded reference
  top.errors <-
    if top.config.warnMissingInh
    && isDecorable(top.bindingType, top.env)
    then if refSet.isJust then []
         else [mwdaWrnFromOrigin(top, s"Cannot take a reference of type ${prettyType(^finalTy)}, as the reference set is not bounded.")]
    else [];

  -- fName is our invented vertex name for the pattern variable
  local requiredInhs :: [String] = toAnonInhs(top.receivedDeps, fName);

  -- Check for equation's existence:
  -- Prod: top.matchingAgainst.fromJust.fullName
  -- Child: top.bindingName
  -- Inh: each of requiredInhs
  local missingInhEqs :: [(DecSiteTree, [String])] =
    decSitesMissingInhEqs(
      top.matchingAgainst.fromJust.fullName, rhsVertexType(top.bindingName),
      removeAll(getMinRefSet(top.bindingType, top.env), requiredInhs),
      myGraphs, top.flowEnv, top.env);

  top.errors <-
    if top.config.warnMissingInh
    && isDecorable(top.bindingType, top.env)
    && top.matchingAgainst.isJust
    then map(\ eqs::(DecSiteTree, [String]) ->
        mwdaWrnFromOrigin(top, s"Pattern variable '${n.name}' has transitive dependencies with missing remote equations for ${implode(", ", eqs.2)}. These attributes must be supplied to ${prettyDecSites(0, eqs.1)}"),
      missingInhEqs)
    else [];
}

-- In places where we solve a synthesized attribute occurs-on context,
-- check that the actual deps for the attribute do not exceed the one specified for the context.
aspect production synOccursContext
top::Context ::= attr::String args::[Type] atty::Type inhs::Type ntty::Type
{
  -- oh no again
  production myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;

  -- The logic here mirrors the reference case in synDecoratedAccessHandler
  local deps :: (Maybe<set:Set<String>>, [TyVar]) =
    inhDepsForSynOnType(attr, ^ntty, myFlow, top.frame.signature, top.env);
  local inhDeps :: set:Set<String> = fromMaybe(set:empty(), deps.1);  -- Need to check that we have bounded inh deps, i.e. deps.1 == just(...)

  local acceptable :: ([String], [TyVar]) = getMinInhSetMembers([], ^inhs, top.env);
  local diff :: [String] = set:toList(set:removeAll(acceptable.1, inhDeps));

  top.contextErrors <-
    if top.config.warnMissingInh
    && null(ntty.freeFlexibleVars) && null(inhs.freeFlexibleVars)
    && !null(top.resolvedOccurs)
    then
      if any(map(contains(_, deps.2), acceptable.2)) then []  -- The deps are supplied as a common InhSet var
      -- We didn't find the deps as an InhSet var
      else if null(diff)
        then if deps.1.isJust then []  -- We have a bound on the inh deps, and they are all present
        -- We don't have a bound on the inh deps, flag the unsatisfied InhSet deps
        else if null(acceptable.2)
        then [mwdaWrn(top.config, top.contextLoc, s"The instance for ${prettyContext(^top)} (arising from ${top.contextSource}) depends on an unbounded set of inherited attributes")]
        else [mwdaWrn(top.config, top.contextLoc, s"The instance for ${prettyContext(^top)} (arising from ${top.contextSource}) exceeds the flow type constraint with dependencies on one of the following sets of inherited attributes: " ++ implode(", ", map(findAbbrevFor(_, top.frame.signature.freeVariables), deps.2)))]
      -- We didn't find the inh deps
      else [mwdaWrn(top.config, top.contextLoc, s"The instance for ${prettyContext(^top)} (arising from ${top.contextSource}) has a flow type exceeding the constraint with dependencies on " ++ implode(", ", diff))]
   else [];
}

--------------------------------------------------------------------------------

-- TODO: There are a few final places where we need to `checkEqDeps` for the sake of `anonVertex`s

-- action blocks (production, terminal, disam, etc)

-- But we don't create flowEnv information for these locations so they can't be checked... oops
-- (e.g. `checkEqDeps` wants a production fName to look things up about.)


