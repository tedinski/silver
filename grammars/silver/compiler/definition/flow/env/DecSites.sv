grammar silver:compiler:definition:flow:env;

import silver:util:treemap as map;
import silver:util:treeset as set;
import silver:compiler:definition:flow:driver;

{--
 - Generate a decision tree to determine all decoration sites where an inherited equation could be supplied
 - for it to be available on some vertex type.
 - This is used in checking for inherited completeness.
 -
 - @param prodName The name of the production containing the vertex type.
 - @param vt The vertex type to find decoration sites for.
 - @param flowEnv The flow environment.
 - @param realEnv The regular environment.
 - @return A decision tree to determine if an inherited attributes has been supplied for vt.
 -}
function findDecSites
DecSiteTree ::= prodName::String vt::VertexType flowEnv::FlowEnv realEnv::Env
{
  local prodDcl :: [ValueDclInfo] = getValueDcl(prodName, realEnv);
  local ns :: NamedSignature =
    case prodDcl of
    | d :: _ -> d.namedSignature
    | [] -> bogusNamedSignature()
    end;
  local ntName::String =
    case vt of
    | forwardVertexType_real() -> ns.outputElement.typerep.typeName
    | localVertexType(fName) when getValueDcl(fName, realEnv) matches dcl :: _ -> dcl.typeScheme.typeName
    | rhsVertexType(sigName) -> lookupSignatureInputElem(sigName, ns).typerep.typeName
    | _ -> ""
    end;
  local implementedSigName::Maybe<String> =
    case prodDcl of
    | d :: _ -> map((.fullName), d.implementedSignature)
    | _ -> nothing()
    end;

  local recurse::(DecSiteTree ::= String VertexType) =
    findDecSites(_, _, flowEnv, realEnv);

  return
    viaProdVertexDec(prodName, vt,
      -- Direct inherited equation at a decoration site
      (if vt.isInhDefVertex
       then directDec(prodName, vt)
       else neverDec()) +
      case vt of
      -- Via flow type
      | lhsVertexType_real() -> error("findDecSites: lhsVertexType") -- Should never actually be a decoration site
      | transAttrVertexType(lhsVertexType_real(), attrName) -> alwaysDec()
      -- Via forwarding
      | forwardVertexType_real() -> forwardDec(prodName, nothing())
      | localVertexType("forward") -> forwardDec(prodName, nothing())
      | localVertexType(fName) when
          isForwardProdAttr(fName,
            newScopeEnv(flatMap((.prodDefs), getProdAttrs(prodName, realEnv)), emptyEnv())) ->
        forwardDec(prodName, just(fName))
      -- Via projected remote equation
      | subtermVertexType(parent, prodOrSig, sigName) ->
         (if !null(getValueDcl(prodOrSig, realEnv))
          -- Projected from a production
          then recurse(prodOrSig, rhsVertexType(sigName))
          -- Projected from a dispatch signature
          else if implementedSigName == just(prodOrSig)
          -- A projection of the same dispatch signature that the current production implements.
          -- Could potentially be a cycle, but more likely is just an implementation
          -- production that dispatches again, which we want to permit.
          -- TODO: This should check that the dispatch is actually applied to the same child;
          -- should this check be done here or in resolving the decision tree?
          then alwaysDec()
          else
            case getTypeDcl(prodOrSig, realEnv) of
            | sigDcl :: _ -> 
              viaDispatchDec(prodOrSig, sigName, product(map(
                \ prod::(String, [String]) ->
                  case getTypeDcl(prodOrSig, realEnv) of
                  | sigDcl :: _
                      when drop(positionOf(sigName, sigDcl.dispatchSignature.inputNames), prod.2)
                      matches sn :: _ -> recurse(prod.1, rhsVertexType(sn))
                  | _ -> error(s"findDecSites: Couldn't resolve ${sigName} in ${prodOrSig}")
                  end,
                -- Look at all the (host) productions that implement this dispatch signature
                getImplementingProds(prodOrSig, flowEnv))))
            | _ -> error(s"findDecSites: Couldn't find dispatch ${sigName}")
            end) *
          projectedDepsDec(prodOrSig, sigName, recurse(prodName, parent))
      -- Via signature/dispatch sharing
      | rhsVertexType(sigName) when lookupSignatureInputElem(sigName, ns).elementShared ->
        product(unzipWith(recurse,
          -- places where this child was decorated in a production forwarding to this one,
          -- or in a dispatch signature that this production implements
          lookupAllSigShareSites(prodName, sigName, flowEnv, realEnv)))
      | _ -> neverDec()
      end +
      -- Via direct sharing
      sum(map(recurse(prodName, _), lookupRefDecSite(prodName, vt, flowEnv))) +
      -- Via translation attribute sharing
      sum(
        flatMap(
          \ attrName ->
            case getAttrDcl(attrName, realEnv) of
            | dcl :: _ when dcl.isTranslation ->
              map(\ transDecSite -> transAttrDec(attrName, recurse(prodName, transDecSite)),
                lookupRefDecSite(prodName, transAttrVertexType(vt, attrName), flowEnv))
            | _ -> []
            end,
          getSynAttrsOn(ntName, realEnv))));
}

{--
 - Generate a decision tree to determine all decoration sites where an inherited attribute
 - might be supplied to some vertex type.
 - This is used in checking for potentially hidden transitive dependencies.
 - This mirrors the above, but we also consider sites where a tree is only conditionally shared.
 - Since we only care if a vertex is *possibly* supplied with an attribute, we can memoize the
 - vertices visited in the enitre search (using a State monad) rather than just the current branch.
 -
 - @param prodName The name of the production containing the vertex type.
 - @param vt The vertex type to find decoration sites for.
 - @param flowEnv The flow environment.
 - @param realEnv The regular environment.
 - @return A decision tree to determine if an inherited attributes could possibly be supplied for vt.
 -}
function findPossibleDecSites
State<([(String, VertexType)], [(String, String)]) DecSiteTree> ::=
  prodName::String vt::VertexType
  flowEnv::FlowEnv realEnv::Env
{
  local prodDcl :: [ValueDclInfo] = getValueDcl(prodName, realEnv);
  local ns :: NamedSignature =
    case prodDcl of
    | d :: _ -> d.namedSignature
    | [] -> bogusNamedSignature()
    end;
  local ntName::String =
    case vt of
    | forwardVertexType_real() -> ns.outputElement.typerep.typeName
    | localVertexType(fName) when getValueDcl(fName, realEnv) matches dcl :: _ -> dcl.typeScheme.typeName
    | rhsVertexType(sigName) -> lookupSignatureInputElem(sigName, ns).typerep.typeName
    | _ -> ""
    end;

  local recurse::(State<([(String, VertexType)], [(String, String)]) DecSiteTree> ::= String VertexType) =
    findPossibleDecSites(_, _, flowEnv, realEnv);

  return do {
    seen :: ([(String, VertexType)], [(String, String)]) <- getState();
    if contains((prodName, vt), seen.1)
    then pure(neverDec())
    else do {
      setState(((prodName, vt) :: seen.1, seen.2));
      viaVertex :: DecSiteTree <-
        case vt of
        -- Via forwarding
        | forwardVertexType_real() -> pure(forwardDec(prodName, nothing()))
        | localVertexType("forward") -> pure(forwardDec(prodName, nothing()))
        | localVertexType(fName) when
            isForwardProdAttr(fName,
              newScopeEnv(flatMap((.prodDefs), getProdAttrs(prodName, realEnv)), emptyEnv())) ->
          pure(forwardDec(prodName, just(fName)))
        -- Via projected remote equation
        | subtermVertexType(parent, prodOrSig, sigName) -> map(
            -- Transitive dependencies of an attribute on the projection must be supplied
            -- for the attribute on the projection to be depended upon.
            bothDec(_, projectedDepsDec(prodOrSig, sigName, findDecSites(prodName, parent, flowEnv, realEnv))),
            if !null(getValueDcl(prodOrSig, realEnv))
            -- Projected from a production
            then recurse(prodOrSig, rhsVertexType(sigName))
            -- Projected from a dispatch signature
            else if contains((prodOrSig, sigName), seen.2)
            -- This is a dispatch that we have already tried to resolve.
            then pure(neverDec())
            -- Otherwise, look at all the (host) productions that implement this dispatch signature
            else map(sum, traverseA(
              \ prod::(String, [String]) ->
                case getTypeDcl(prodOrSig, realEnv) of
                | sigDcl :: _
                    when drop(positionOf(sigName, sigDcl.dispatchSignature.inputNames), prod.2)
                    matches sn :: _ -> do {
                      setState((seen.1, (prod.1, sn) :: seen.2));
                      recurse(prod.1, rhsVertexType(sn));
                    }
                | _ -> error(s"findDecSites: Couldn't resolve ${sigName} in ${prodOrSig}")
                end,
              getImplementingProds(prodOrSig, flowEnv))))
        -- Via signature/dispatch sharing
        | rhsVertexType(sigName) when lookupSignatureInputElem(sigName, ns).elementShared ->
          map(sum, sequence(unzipWith(recurse,
            -- places where this child was decorated in a production forwarding to this one,
            -- or in a dispatch signature that this production implements
            lookupAllSigShareSites(prodName, sigName, flowEnv, realEnv))))
        | _ -> pure(neverDec())
        end;
      viaDirectShare :: [DecSiteTree] <-
        traverseA(recurse(prodName, _), lookupRefPossibleDecSites(prodName, vt, flowEnv));
      viaTransAttrShare :: [[DecSiteTree]] <-
        traverseA(\ attrName ->
          case getAttrDcl(attrName, realEnv) of
          | dcl :: _ when dcl.isTranslation ->
            traverseA(\ transDecSite -> map(transAttrDec(attrName, _), recurse(prodName, transDecSite)),
              lookupRefPossibleDecSites(prodName, transAttrVertexType(vt, attrName), flowEnv))
          | _ -> pure([])
          end,
          getSynAttrsOn(ntName, realEnv));
      return
        -- Direct inherited equation at a decoration site
        (if vt.isInhDefVertex
        then directDec(prodName, vt)
        else neverDec()) +
        viaVertex + sum(viaDirectShare) + sum(concat(viaTransAttrShare));
    };
  };
}

-- Flatten a resolved decision tree, to determine the minimal places where an
-- equation is needed.
partial strategy attribute reduceDecSiteStep =
  rule on DecSiteTree of
  | altDec(alwaysDec(), d) -> alwaysDec()
  | altDec(d, alwaysDec()) -> alwaysDec()
  | altDec(neverDec(), d) -> ^d
  | altDec(d, neverDec()) -> ^d
  | bothDec(alwaysDec(), d) -> ^d
  | bothDec(d, alwaysDec()) -> ^d
  | bothDec(neverDec(), _) -> neverDec()
  | bothDec(_, neverDec()) -> neverDec()
  | altDec(altDec(d1, d2), d3) -> altDec(^d1, altDec(^d2, ^d3))
  | bothDec(bothDec(d1, d2), d3) -> bothDec(^d1, bothDec(^d2, ^d3))
  -- Valid optimizations, but actually makes things slower (due to forcing the
  -- entire tree to be built):
  -- | altDec(d1, d2) when contains(^d1, d2.decSiteAlts) -> ^d2
  -- | bothDec(d1, d2) when contains(^d1, d2.decSiteReqs) -> ^d2
  | depAttrDec(_, alwaysDec()) -> alwaysDec()
  | depAttrDec(_, neverDec()) -> neverDec()
  end occurs on DecSiteTree;

-- The inherited attribute for which we are trying to resolve the decision tree
inherited attribute attrToResolve::String occurs on DecSiteTree;
propagate attrToResolve on DecSiteTree excluding depAttrDec, projectedDepsDec, transAttrDec;
aspect production depAttrDec
top::DecSiteTree ::= attrName::String d::DecSiteTree
{
  d.attrToResolve = attrName;
}

-- The set of (prod, vertex, inh) that have been seen so far in this branch of the tree
inherited attribute seenProdVertexAttrs::set:Set<(String, VertexType, String)> occurs on DecSiteTree;
propagate seenProdVertexAttrs on DecSiteTree excluding viaProdVertexDec;
aspect production viaProdVertexDec
top::DecSiteTree ::= prodName::String vt::VertexType d::DecSiteTree
{
  d.seenProdVertexAttrs = set:add([(prodName, vt, top.attrToResolve)], top.seenProdVertexAttrs);
}

-- The set of (dispatch, child, inh) that have been seen so far in this branch of the tree
inherited attribute seenDispatchSigAttrs::set:Set<(String, String, String)> occurs on DecSiteTree;
propagate seenDispatchSigAttrs on DecSiteTree excluding viaDispatchDec;
aspect production viaDispatchDec
top::DecSiteTree ::= dispatchSig::String sigName::String d::DecSiteTree
{
  d.seenDispatchSigAttrs = set:add([(dispatchSig, sigName, top.attrToResolve)], top.seenDispatchSigAttrs);
}

partial strategy attribute elimCycleDecSiteStep =
  rule on DecSiteTree of
  | viaProdVertexDec(prodName, vt, _)
      when set:contains((prodName, vt, top.attrToResolve), top.seenProdVertexAttrs) ->
      -- This is a cycle due to a missing equation somewhere.
      neverDec()
  | viaProdVertexDec(_, _, alwaysDec()) -> alwaysDec()
  | viaProdVertexDec(_, _, neverDec()) -> neverDec()
  | viaDispatchDec(dispatchSig, sigName, _)
      when set:contains((dispatchSig, sigName, top.attrToResolve), top.seenDispatchSigAttrs) ->
      -- This is a dispatch that we are already trying to resolve.
      -- Could potentially be a cycle, but more likely is just an implementation
      -- production that dispatches again, which we want to permit.
      neverDec()
  | viaDispatchDec(_, _, alwaysDec()) -> alwaysDec()
  | viaDispatchDec(_, _, neverDec()) -> neverDec()
  end occurs on DecSiteTree;

attribute flowEnv, productionFlowGraphs occurs on DecSiteTree;

-- Resolve the decision tree for a particular attribute, replacing decoration
-- sites known to be supplied with alwaysDec().
partial strategy attribute lookupDecSiteStep =
  rule on top::DecSiteTree of
  | directDec(prodName, vt)
        when vertexHasInhEq(prodName, vt, top.attrToResolve, top.flowEnv) ->
      alwaysDec()
  | forwardDec(_, just(_)) ->
      if splitTransAttrInh(top.attrToResolve).isJust
      then neverDec()
      else alwaysDec()
  | forwardDec(prodName, nothing()) ->
      case splitTransAttrInh(top.attrToResolve) of
      | just((transAttr, inhAttr))
            when !null(lookupSyn(prodName, transAttr, top.flowEnv)) ->
          -- transAttr has an override equation, so trans.inh supplied on lhs
          -- isn't supplied to trans on forward:
          neverDec()
      | _ -> alwaysDec()
      end
  | depAttrDec(attrName, d) when top.attrToResolve == attrName -> ^d
  | projectedDepsDec(prodName, sigName, d) ->
      product(map(depAttrDec(_, ^d), set:toList(onlyLhsInh(expandGraph(
        [rhsInhVertex(sigName, top.attrToResolve)],
        findProductionGraph(prodName, top.productionFlowGraphs))))))
  | transAttrDec(attrName, d) ->
      case splitTransAttrInh(top.attrToResolve) of
      | just((transAttr, inhAttr)) when transAttr == attrName -> depAttrDec(inhAttr, ^d)
      | _ -> neverDec()
      end
  end occurs on DecSiteTree;

partial strategy attribute resolveDecSiteStep =
  --rule on DecSiteTree of
  --| ds -> unsafeTracePrint(^ds, ds.dbgPP ++ "\n\n")
  --end <*
  elimCycleDecSiteStep <+ lookupDecSiteStep <+ reduceDecSiteStep <+
  -- Short-circuit alternatives to potentially avoid building the entire tree
  altDec(resolveDecSiteStep, id) <+
  some(resolveDecSiteStep)
  occurs on DecSiteTree;

strategy attribute resolveDecSite = repeat(resolveDecSiteStep)
  occurs on DecSiteTree;

propagate flowEnv, productionFlowGraphs, reduceDecSiteStep, elimCycleDecSiteStep, lookupDecSiteStep, resolveDecSiteStep, resolveDecSite on DecSiteTree;

{--
  - Determine if some decoration site has some inherited attribute supplied.
  -
  - @param d The decoration site to check.
  - @param attrName The name of the inherited attribute.
  - @param prodGraphs The final production flow graphs.
  - @param flowEnv The flow environment.
  - @return alwaysDec(), if the attribute is always present,
  - or else the places where it could be supplied.
  -}
function resolveDecSiteInhEq
DecSiteTree ::= attrName::String d::DecSiteTree prodGraphs::EnvTree<ProductionGraph> flowEnv::FlowEnv
{
  d.attrToResolve = attrName;
  d.productionFlowGraphs = prodGraphs;
  d.flowEnv = flowEnv;
  d.seenProdVertexAttrs = set:empty();
  d.seenDispatchSigAttrs = set:empty();
  d.maxDepth = 10;
  return d.resolveDecSite;
}

{--
  - Determine if some flow vertex type in a production has some inherited attribute supplied.
  -
  - @param prodName The name of the production containing the vertex.
  - @param vt The vertex type to check.
  - @param attrName The name of the inherited attribute.
  - @param prodGraphs The final production flow graphs.
  - @param flowEnv The flow environment.
  - @param realEnv The regular environment.
  - @return alwaysDec(), if the attribute is always present,
  - or else the places where it could be supplied.
  -}
fun resolveInhEq
DecSiteTree ::=
    prodName::String vt::VertexType attrName::String
    prodGraphs::EnvTree<ProductionGraph> flowEnv::FlowEnv realEnv::Env =
  resolveDecSiteInhEq(attrName, findDecSites(prodName, vt, flowEnv, realEnv), prodGraphs, flowEnv);

{--
 - Determine if a decoration site for some vertex has an inherited attribute supplied.
 - 
 - @param prodName The name of the production containing the vertex.
 - @param vt The vertex type to check.
 - @param attrName The name of the inherited attribute.
 - @param flowEnv The flow environment.
 - @param realEnv The regular environment.
 - @return true if the vertex is guranteed to be supplied with the attribute.
 -}
fun decSiteHasInhEq
Boolean ::=
    prodName::String vt::VertexType attrName::String
    prodGraphs::EnvTree<ProductionGraph> flowEnv::FlowEnv realEnv::Env =
  resolveInhEq(attrName, vt, attrName, prodGraphs, flowEnv, realEnv) == alwaysDec();

-- Helper for checking multiple inh attributes
function decSitesMissingInhEqs
[(DecSiteTree, [String])] ::=
  prodName::String vt::VertexType attrNames::[String]
  prodGraphs::EnvTree<ProductionGraph> flowEnv::FlowEnv realEnv::Env
{
  nondecorated local d::DecSiteTree = findDecSites(prodName, vt, flowEnv, realEnv);
  local resolved::map:Map<DecSiteTree String> =
    map:add(map(\ a -> (resolveDecSiteInhEq(a, d, prodGraphs, flowEnv), a), attrNames), map:empty());
  return flatMap(\ d -> 
    case map:lookup(d, resolved) of
    | [] -> []
    | missing -> [(d, missing)]
    end,
    remove(alwaysDec(), map:keys(resolved)));
}

{--
 - Determine if an inherited attribute for some vertex could possibly be demanded somewhere.
 - 
 - @param prodName The name of the production containing the vertex.
 - @param vt The vertex type to check.
 - @param attrName The name of the inherited attribute.
 - @param prodGraphs The final production flow graphs.
 - @param flowEnv The flow environment.
 - @param realEnv The regular environment.
 - @return true if the vertex might ever be supplied with the attribute, false otherwise.
 -}
fun possibleDecSiteHasInhEq
Boolean ::=
    prodName::String vt::VertexType attrName::String
    prodGraphs::EnvTree<ProductionGraph> flowEnv::FlowEnv realEnv::Env =
  resolveDecSiteInhEq(attrName, evalState(findPossibleDecSites(prodName, vt, flowEnv, realEnv), ([], [])), prodGraphs, flowEnv)
  == alwaysDec();
