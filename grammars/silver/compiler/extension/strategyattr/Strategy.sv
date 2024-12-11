grammar silver:compiler:extension:strategyattr;

abstract production strategyAttributeDcl
top::AGDcl ::= isTotal::Boolean a::Name recVarNameEnv::[Pair<String String>] recVarTotalEnv::[Pair<String Boolean>] e::StrategyExpr
{
  top.unparse = (if isTotal then "" else "partial ") ++ "strategy attribute " ++ a.unparse ++ "=" ++ e.unparse ++ ";";
  propagate grammarName, config, env, flowEnv;

  top.occursDefs := [];
  top.specDefs := [];
  top.refDefs := [];

  production attribute fName :: String;
  fName = top.grammarName ++ ":" ++ a.name;
  
  -- Define these directly to avoid circular dependencies,
  -- since the forward contributes to the env.
  propagate compiledGrammars, errors, moduleNames;
  
  top.errors <-
    if length(getAttrDclAll(fName, top.env)) > 1
    then [errFromOrigin(a, "Attribute '" ++ fName ++ "' is already bound.")]
    else [];
  top.errors <-
    if isTotal && !e.isTotal
    -- Not an error since we can still translate this, but the translation may raise run-time errors in case of failure
    then [wrnFromOrigin(e, s"Implementation of total strategy ${a.name} is not total")]
    else [];

  e.recVarNameEnv = recVarNameEnv;
  e.recVarTotalEnv = recVarTotalEnv;
  e.recVarTotalNoEnvEnv = recVarTotalEnv;
  e.outerAttr = a.name;
  e.isOutermost = true;
  
  nondecorated local fwrd::AGDcl =
    foldr(
      appendAGDcl,
      defsAGDcl(
        [attrDef(
           defaultEnvItem(
             strategyDcl(
               fName, isTotal,
               !null(top.errors), map(fst, e.liftedStrategies), recVarNameEnv, recVarTotalEnv, e.partialRefs, e.totalRefs, e.containsTraversal, ^e,
               sourceGrammar=top.grammarName, sourceLocation=a.nameLoc)))]),
      map(
        \ d::(String, Decorated StrategyExpr with LiftedInhs) ->
          strategyAttributeDcl(
            d.snd.isTotalNoEnv, name(d.fst), d.snd.recVarNameEnv, d.snd.recVarTotalNoEnvEnv, new(d.snd)),
        e.liftedStrategies));
  
  -- Uncomment for debugging
  --forwards to unsafeTrace(fwrd, printT(a.name ++ " = " ++ e.unparse ++ "; lifted  " ++ implode(",  ", map(fst, e.liftedStrategies)) ++ "\n\n", unsafeIO()));

  forwards to fwrd;
}

abstract production strategyAttributionDcl implements AttributionDcl
top::AGDcl ::= at::QName attl::BracketedOptTypeExprs nt::QName nttl::BracketedOptTypeExprs
{
  top.unparse = "attribute " ++ at.unparse ++ attl.unparse ++ " occurs on " ++ nt.unparse ++ nttl.unparse ++ ";";
  top.moduleNames := [];

  production attribute localErrors::[Message] with ++;
  localErrors :=
    attl.errors ++ attl.errorsTyVars ++ nt.lookupType.errors ++ nttl.errors ++ nttl.errorsTyVars;
  localErrors <-
    if length(attl.types) > 0
    then [errFromOrigin(attl, "Explicit type arguments are not allowed for strategy attributes")]
    else [];
  
  -- Technically we could do this check on the propagate, but it seems clearer to raise it here
  localErrors <-
    flatMap(
      \ totalAttr::String ->
        if null(getOccursDcl(totalAttr, nt.lookupType.fullName, top.env))
        then [errFromOrigin(top, s"Total strategy attribute ${totalAttr} referenced by ${at.name} does not occur on ${nt.name}")]
        else [],
      nub(at.lookupAttribute.dcl.totalRefs));
  
  -- TODO: Check that the type parameters of any rules of type nt match nttl
  
  top.errors := if !null(localErrors) then localErrors else forward.errors;

  forwards to
    extraDclsAttributionDcl(
      @at, @attl, @nt, @nttl,
      altParamAttributionDcl(
        defaultAttributionDcl,
        botlSome(
          bTypeList(
            '<',
            typeListSingle(
              case nttl of
              | botlSome(tl) -> 
                appTypeExpr(
                  nominalTypeExpr(nt.qNameType),
                  ^tl)
              | botlNone() -> nominalTypeExpr(nt.qNameType)
              end),
            '>'))),
      foldr(appendAGDcl, emptyAGDcl(),
        map(
          \ n::String ->
            attributionDcl(
              'attribute', qName(n), ^attl, 'occurs', 'on', ^nt, ^nttl, ';'),
          at.lookupAttribute.dcl.liftedStrategyNames)));
}

{--
 - Propagate a strategy attribute on the enclosing production
 - @param attr  The name of the attribute to propagate
 -}
abstract production propagateStrategy implements Propagate
top::ProductionStmt ::= includeShared::Boolean @attr::QName
{
  top.unparse = s"propagate ${if includeShared then "@" else ""}${attr.unparse}";
  
  production isTotal::Boolean = attr.lookupAttribute.dcl.isTotal;
  production e::StrategyExpr = attr.lookupAttribute.dcl.strategyExpr;
  e.grammarName = top.grammarName;
  e.config = top.config;
  e.frame = top.frame;
  e.env = top.env;
  e.recVarNameEnv = attr.lookupAttribute.dcl.givenRecVarNameEnv;
  e.recVarTotalEnv = attr.lookupAttribute.dcl.givenRecVarTotalEnv;
  e.outerAttr = attr.lookupAttribute.fullName;
  e.isOutermost = true;
  e.inlinedStrategies = [attr.lookupAttribute.fullName]; -- Don't unfold the top-level strategy within itself
  
  production e2::StrategyExpr = e.optimize;
  e2.grammarName = e.grammarName;
  e2.config = e.config;
  e2.frame = e.frame;
  e2.env = e.env;
  e2.recVarNameEnv = e.recVarNameEnv;
  e2.recVarTotalEnv = e.recVarTotalEnv;
  e2.outerAttr = e.outerAttr;
  e2.isOutermost = e.isOutermost;
  e2.inlinedStrategies = e.inlinedStrategies;
  e2.flowEnv = top.flowEnv;
  
  -- Can't do this with forwarding to avoid circular dependency of
  -- forward -> dcl.containsErrors -> dcl.flowEnv -> forward.flowDefs
  top.errors :=
    if
      -- Check for errors in this or inlined strategy expressions that would be reported on the attribute definition
      attr.lookupAttribute.dcl.containsErrors ||
      any(map((.containsErrors), flatMap(getAttrDcl(_, top.env), attr.lookupAttribute.dcl.partialRefs))) ||
      -- Check for total strategy ref occurs errors that would already be reported on the occurence
      (!null(getOccursDcl(attr.lookupAttribute.fullName, top.frame.signature.outputElement.typerep.typeName, top.env)) &&
       any(map(null, map(getOccursDcl(_, top.frame.signature.outputElement.typerep.typeName, top.env), attr.lookupAttribute.dcl.totalRefs))))
    then []
    else forward.errors;
  
  nondecorated local fwrd::ProductionStmt =
    foldr(
      productionStmtAppend(_, _),
      attributeDef(
        concreteDefLHS(qName(top.frame.signature.outputElement.elementName)),
        '.',
        qNameAttrOccur(^attr),
        '=',
        if isTotal then e2.totalTranslation else e2.partialTranslation,
        ';'),
      map(
        \ n::String -> propagateOneAttr(if includeShared then elemShared('@') else elemNotShared(), qName(n)),
        attr.lookupAttribute.dcl.liftedStrategyNames));
  
  -- Uncomment for debugging
  --forwards to unsafeTrace(propagateImpl(includeShared, attr, fwrd), printT(attr.name ++ " on " ++ top.frame.fullName ++ " = " ++ (if isTotal then e2.totalTranslation else e2.partialTranslation).unparse ++ ";\n\n", unsafeIO()));
  forwards to propagateImpl(includeShared, attr, fwrd);
}
