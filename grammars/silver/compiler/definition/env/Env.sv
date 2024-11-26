grammar silver:compiler:definition:env;


-- emptyEnv    Env ::=
-- toEnv       Env ::= d::Defs
-- appendEnv   Env ::= e1::Env  e2::Env
-- newScopeEnv Env ::= e1::Defs  e2::Env

-- [DclInfo] ::= search::String e::Env
-- getValueDclInScope getValueDcl getValueDclAll
-- getTypeDcl
-- getAttrDcl

-- getProdAttrs [DclInfo] ::= prod::String e::Env

data nonterminal Env with
  typeTree, valueTree, attrTree, instTree, prodOccursTree, occursTree, prodsForNtTree,
  prodDclList, dispatchDclList;

synthesized attribute typeTree      :: [EnvTree<TypeDclInfo>]; -- Expr is type tau
synthesized attribute valueTree     :: [EnvTree<ValueDclInfo>]; -- x has type tau
synthesized attribute attrTree      :: [EnvTree<AttributeDclInfo>]; -- attr a has type tau

synthesized attribute instTree       :: EnvTree<InstDclInfo>; -- class on type
synthesized attribute prodOccursTree :: EnvTree<ProductionAttrDclInfo>; -- value on prod
synthesized attribute occursTree     :: EnvTree<OccursDclInfo>; -- attr on NT

synthesized attribute prodsForNtTree :: [EnvTree<ValueDclInfo>]; -- maps nt fname to prods known to construct it

----------------------------------------------------------------------------------------------------
--Environment creation functions--------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

abstract production emptyEnv
top::Env ::=
{
  top.typeTree = [emptyEnvTree()];
  top.valueTree = [emptyEnvTree()];
  top.attrTree = [emptyEnvTree()];
  
  top.instTree = emptyEnvTree();
  top.prodOccursTree = emptyEnvTree();
  top.occursTree = emptyEnvTree();
  
  top.prodsForNtTree = [emptyEnvTree()];

  top.prodDclList = [];
  top.dispatchDclList = [];
}

fun toEnv Env ::= d::[Def] od::[OccursDclInfo] = occursEnv(od, newScopeEnv(d, emptyEnv()));

{--
 - appendEnv exists because we do a weird scope swizzling.
 - Our scopes go [global, import, grammar] but hierarchically we
 - should have   [global, grammar, import] because grammar-wide names would
 - seem to have wider scope than per-file imports.
 - But this would be horrible semantics: the file in question is even included
 - in the grammar-wide scope. So imports would hide things in the local file, even.
 - 
 - Instead, we build these three scopes as essentially separate environments,
 - and append them together in the correct order.
 -}
abstract production appendEnv
top::Env ::= e1::Env  e2::Env
{
  top.typeTree = e1.typeTree ++ e2.typeTree;
  top.valueTree = e1.valueTree ++ e2.valueTree;
  top.attrTree = e1.attrTree ++ e2.attrTree;

  top.instTree = appendEnvTree(e1.instTree, e2.instTree);
  top.prodOccursTree = appendEnvTree(e1.prodOccursTree, e2.prodOccursTree);
  top.occursTree = appendEnvTree(e1.occursTree, e2.occursTree);

  top.prodsForNtTree = e1.prodsForNtTree ++ e2.prodsForNtTree;

  top.prodDclList = e1.prodDclList ++ e2.prodDclList;
  top.dispatchDclList = e1.dispatchDclList ++ e2.dispatchDclList;
}

{--
 - The usual means of introducing new defs to an environment, by creating a new nested scope.
 -}
abstract production newScopeEnv
top::Env ::= ds::[Def]  e::Env
{
  production d::Defs = foldr(consDefs, nilDefs(), ds);
  top.typeTree = buildTree(d.typeList) :: e.typeTree;
  top.valueTree = buildTree(d.valueList) :: e.valueTree;
  top.attrTree = buildTree(d.attrList) :: e.attrTree;

  top.instTree = consEnvTree(mapFullnameDcls(d.instList), e.instTree);
  top.prodOccursTree = consEnvTree(mapFullnameDcls(d.prodOccursList), e.prodOccursTree);
  top.occursTree = e.occursTree;

  top.prodsForNtTree =
    directBuildTree(map(\ di::ValueDclInfo -> (di.namedSignature.outputElement.typerep.typeName, di), d.prodDclList)) ::
    e.prodsForNtTree;

  top.prodDclList = d.prodDclList ++ e.prodDclList;
  top.dispatchDclList = d.dispatchDclList ++ e.dispatchDclList;
}

{--
 - Introduces new occurs defs to an environment.
 - This is seperate from newScopeEnv as we must be able to build the other env trees without having the occurs tree.
 -}
abstract production occursEnv
top::Env ::= d::[OccursDclInfo]  e::Env
{
  top.typeTree = e.typeTree;
  top.valueTree = e.valueTree;
  top.attrTree = e.attrTree;
  
  top.instTree = e.instTree;
  top.prodOccursTree = e.prodOccursTree;
  top.occursTree = consEnvTree(mapFullnameDcls(d), e.occursTree);
  
  top.prodsForNtTree = e.prodsForNtTree;

  top.prodDclList = e.prodDclList;
  top.dispatchDclList = e.dispatchDclList;
}

----------------------------------------------------------------------------------------------------
--Environment query functions-----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

fun searchEnvAll [a] ::= search::String e::[EnvTree<a>] = flatMap(searchEnvTree(search, _), e);

function searchEnv
[a] ::= search::String e::[EnvTree<a>]
{
  local found :: [a] = searchEnvTree(search, head(e));
  
  return if null(e) then []
         else if null(found) then searchEnv(search, tail(e))
         else found;
}

fun getValueDclInScope [ValueDclInfo] ::= search::String e::Env =
  searchEnvTree(search, head(e.valueTree));
fun getValueDcl [ValueDclInfo] ::= search::String e::Env = searchEnv(search, e.valueTree);
fun getValueDclAll [ValueDclInfo] ::= search::String e::Env = searchEnvAll(search, e.valueTree);

fun getTypeDclInScope [TypeDclInfo] ::= search::String e::Env =
  searchEnvTree(search, head(e.typeTree));
fun getTypeDcl [TypeDclInfo] ::= search::String e::Env = searchEnv(search, e.typeTree);
fun getTypeDclAll [TypeDclInfo] ::= search::String e::Env = searchEnvAll(search, e.typeTree);

fun getAttrDclInScope [AttributeDclInfo] ::= search::String e::Env =
  searchEnvTree(search, head(e.attrTree));
fun getAttrDcl [AttributeDclInfo] ::= search::String e::Env = searchEnv(search, e.attrTree);
fun getAttrDclAll [AttributeDclInfo] ::= search::String e::Env = searchEnvAll(search, e.attrTree);

{--
 - Look up the short name of an attribute,
 - disambiguating based on some nonterminal on which it is known to occur.
 -}
fun getOccuringAttrDcl [AttributeDclInfo] ::= fnnt::String search::String e::Env =
  getOccuringAttrDclHelp(map((.attrOccurring), getAttrOccursOn(fnnt, e)), search, e.attrTree);
function getOccuringAttrDclHelp
[AttributeDclInfo] ::= allAttrs::[String] search::String e::[EnvTree<AttributeDclInfo>]
{
  local found :: [AttributeDclInfo] =
    filter(
      \ a::AttributeDclInfo -> contains(a.fullName, allAttrs),
      searchEnvTree(search, head(e)));
  
  return if null(e) then []
         else if null(found) then getOccuringAttrDclHelp(allAttrs, search, tail(e))
         else found;
}

fun getOccursDcl [OccursDclInfo] ::= fnat::String fnnt::String e::Env =
  occursOnHelp(searchEnvTree(fnnt, e.occursTree), fnat);
fun occursOnHelp [OccursDclInfo] ::= i::[OccursDclInfo] fnat::String =
  if null(i) then []
  else if head(i).attrOccurring == fnat
       then head(i) :: occursOnHelp(tail(i), fnat)
       else occursOnHelp(tail(i), fnat);

-- Determines whether a type is automatically promoted to a decorated type
-- and whether a type may be supplied with inherited attributes.
-- Used by expression (id refs), decorate type checking, and translations.
function isDecorable
Boolean ::= t::Type e::Env
{
  return
    case t of
    | skolemType(_) -> !null(searchEnvTree(t.typeName, e.occursTree))
    | varType(_) -> !null(searchEnvTree(t.typeName, e.occursTree))  -- Can happen when pattern matching on a prod with occurs contexts
    | _ -> t.isNonterminal && !t.isData
    end;
}

fun getProdAttrs [ProductionAttrDclInfo] ::= fnprod::String e::Env =
  searchEnvTree(fnprod, e.prodOccursTree);

{--
 - Get all productions for a nonterminal known to local environment.
 - (forwarding and non-forwarding.)
 - Current known use cases:
 -  1. Interference testing code generation (randomly generate trees)
 -       - Because we test each production independently, we may not actually need this?
 -  2. MWDA checking known forwarding productions on attribute occurrence declaration.
 -       - We need to be able to look from forwarding to occurs, and from
 -         occurs to forwarding to cover all cases.
 -  3. For the automatic attributes extension
 -       - to implement propagate on all the known non-forwarding productions of a nonterminal.
 - You should probably have a good reason for using this, and document it here if you do.
 -}
fun getKnownProds [ValueDclInfo] ::= fnnt::String e::Env = searchEnvAll(fnnt, e.prodsForNtTree);

-- The list of non-forwarding productions may contain productions from `options` not
-- imported locally, and so we must consult the "flow environment" for that information:
--function getNonforwardingProds

{--
 - Returns all attributes known locally to occur on a nonterminal.
 - Obviously we can never know all attributes, but we generally don't need to for
 - any reason.
 -}
fun getAttrOccursOn [OccursDclInfo] ::= fnnt::String e::Env = searchEnvTree(fnnt, e.occursTree);

{--
 - Returns the names of all synthesized attributes known locally to occur on a nonterminal.
 -}
fun getSynAttrsOn [String] ::= fnnt::String e::Env =
  flatMap(
    \ o::OccursDclInfo ->
      case getAttrDcl(o.attrOccurring, e) of
      | at :: _ when at.isSynthesized -> [o.attrOccurring]
      | _ -> []
      end,
    getAttrOccursOn(fnnt, e));

{--
 - Returns the names of all inherited attributes known locally to occur on a nonterminal.
 -}
fun getInhAttrsOn [String] ::= fnnt::String e::Env =
  flatMap(
    \ o::OccursDclInfo ->
      case getAttrDcl(o.attrOccurring, e) of
      | at :: _ when at.isInherited -> [o.attrOccurring]
      | _ -> []
      end,
    getAttrOccursOn(fnnt, e));

{--
 - Returns the names of all inherited attributes known locally to occur on a nonterminal.
 - Also includes all inherited attributes occurring on translation attributes on the
 - nonterminal, when we want to treat these like inherited attributes.
 -}
fun getInhAndInhOnTransAttrsOn [String] ::= fnnt::String e::Env =
  flatMap(
    \ o::OccursDclInfo ->
      case getAttrDcl(o.attrOccurring, e) of
      | at :: _ when at.isInherited -> [o.attrOccurring]
      | at :: _ when at.isSynthesized && at.isTranslation ->
        map(
          \ inh::String -> s"${o.attrOccurring}.${inh}",
          getInhAttrsOn(at.typeScheme.typeName, e))
      | _ -> []
      end,
    getAttrOccursOn(fnnt, e));

-- This ensure the annotation list is in the properly sorted order!
function annotationsForNonterminal
[NamedSignatureElement] ::= nt::Type  env::Env
{
  local annos :: [OccursDclInfo] =
    filter((.isAnnotation), getAttrOccursOn(nt.typeName, env));
  
  return sortBy(namedSignatureElementLte, map(annoInstanceToNamed(^nt, _), annos));
}
-- only used by the above
function annoInstanceToNamed
NamedSignatureElement ::= nt::Type  anno::OccursDclInfo
{
  -- Used to compute the local typerep for this nonterminal
  anno.givenNonterminalType = ^nt;
  
  return namedSignatureElement(anno.attrOccurring, anno.typeScheme.typerep, false);
}

-- Looks up class instances matching a type
function getInstanceDcl
[InstDclInfo] ::= fntc::String t::Type e::Env
{
  local c::Context = instContext(fntc, @t);
  c.env = e;
  return c.resolved;
}

-- Compute a lower bound on the members of an InhSet type, including transitive ones arising from subset constraints
function getMinInhSetMembers
([String], [TyVar]) ::= seen::[TyVar] t::Type e::Env
{
  local c::Context = inhSubsetContext(varType(freshTyVar(inhSetKind())), @t);
  c.env = e;
  
  local recurse::[([String], [TyVar])] =
    map(
      \ d::InstDclInfo -> getMinInhSetMembers(t.freeVariables ++ seen, d.typeScheme.monoType, e),
      c.resolved);

  return
    case t of
    | skolemType(tv) when contains(tv, seen) -> ([], [])
    | varType(_) -> ([], [])  -- If an InhSet is unspecialized after type checking, assume it is empty
    | _ -> (sort(unions(t.inhSetMembers :: map(fst, recurse))), unions(t.freeVariables :: map(snd, recurse))) 
    end;
}

function getMinRefSet
[String] ::= t::Type e::Env
{
  return
    case t of
    | decoratedType(_, i) -> getMinInhSetMembers([], ^i, e).fst
    | _ -> []
    end;
}

-- Try to compute an upper bound on the members of an InhSet type, including transitive ones arising from subset constraints
function getMaxInhSetMembers
(Maybe<[String]>, [TyVar]) ::= seen::[TyVar] t::Type e::Env
{
  local c::Context = inhSubsetContext(@t, varType(freshTyVar(inhSetKind())));
  c.env = e;
  
  local recurse::[(Maybe<[String]>, [TyVar])] =
    map(
      \ d::InstDclInfo -> getMaxInhSetMembers(t.freeVariables ++ seen, d.typerep2, e),
      c.resolved);
  
  return
    case t of
    | skolemType(tv) when contains(tv, seen) -> (nothing(), [])
    | varType(_) -> (just([]), [])  -- If an InhSet is unspecialized after type checking, assume it is empty
    | inhSetType(inhs) -> (just(inhs), [])
    | _ -> (map(sort, foldr(
        \ inhs1::Maybe<[String]> inhs2::Maybe<[String]> -> alt(lift2(intersect, inhs1, inhs2), alt(inhs1, inhs2)),
        empty, map(fst, recurse))),
      unions(t.freeVariables :: map(snd, recurse)))
    end;
}

function getMaxRefSet
Maybe<[String]> ::= t::Type e::Env
{
  return
    case t of
    | decoratedType(_, i) -> getMaxInhSetMembers([], ^i, e).fst
    | _ -> just([])
    end;
}

-- Check if a production attribute is a forward production attribute.
-- Note this expects the local env for the production!
-- If looking up in another prod, need to get the prod attr defs for the prod.
fun isForwardProdAttr Boolean ::= a::String  e::Env =
  case getValueDclAll(a, e) of
  | d :: _ -> d.hasForward
  | _ -> false
  end;
