grammar silver:compiler:definition:core;

dispatch AttributionDcl = AGDcl ::= at::QName attl::BracketedOptTypeExprs nt::QName nttl::BracketedOptTypeExprs;

abstract production defaultAttributionDcl implements AttributionDcl
top::AGDcl ::= at::QName attl::BracketedOptTypeExprs nt::QName nttl::BracketedOptTypeExprs
{ 
  top.unparse = "attribute " ++ at.unparse ++ attl.unparse ++ " occurs on " ++ nt.unparse ++ nttl.unparse ++ ";";

  -- TODO: this location is highly unreliable.

  -- We must unconditionally emit the occurs def in order to signal to the
  -- environment mechanism that we're in a different namespace than
  -- the types/attributes.
  top.occursDefs := [
    (if !at.lookupAttribute.dcl.isAnnotation then occursDcl else annoInstanceDcl)(
      nt.lookupType.fullName, at.lookupAttribute.fullName,
      protontty,
      if ntParamKinds == map((.kindrep), nttl.types) && map((.kind), atTypeScheme.boundVars) == map((.kindrep), attl.types)
      then protoatty
      else errorType(),
      sourceGrammar=top.grammarName, sourceLocation=at.nameLoc)];

  -- binding errors in looking up these names.
  top.errors <- nt.lookupType.errors ++
    -- The nonterminal type list is strictly type VARIABLES only
    nttl.errorsTyVars;
  
  top.errors <-
    if attl.missingCount > 0
    then [errFromOrigin(attl, "Attribute type arguments cannot contain _")]
    else [];
  
  nttl.initialEnv = top.env;
  at.env = top.env;
  attl.env = nttl.envBindingTyVars;
  nt.env = top.env;
  nttl.env = nttl.envBindingTyVars;
  
  local ntTypeScheme::PolyType = nt.lookupType.typeScheme;
  local atTypeScheme::PolyType = at.lookupAttribute.typeScheme;
  
  -- Make sure we get the number and kind of type variables correct for the NT
  local ntParamKinds :: [Kind] =
    case nt.lookupType.dcls of
    | ntDcl(_, ks, _, _, _) :: _ -> ks
    | _ -> []
    end;
  top.errors <-
    if null(nt.lookupType.dcls) then []
    else if length(ntParamKinds) != length(nttl.types)
    then
      [errFromOrigin(nt,
        nt.name ++ " expects " ++ toString(length(ntParamKinds)) ++
        " type variables, but " ++ toString(length(nttl.types)) ++ " were provided.")]
    else if ntParamKinds != map((.kindrep), nttl.types)
    then
      [errFromOrigin(nt,
        nt.name ++ " had kind " ++ foldr(arrowKind, starKind(), ntParamKinds).typepp ++
        " but type variable(s) have kind(s) " ++ implode(", ", map(compose(prettyKind, (.kindrep)), nttl.types)) ++ ".")]
    else [];

  -- Make sure we get the number and kind of type variables correct for the ATTR
  top.errors <-
    if length(atTypeScheme.boundVars) != length(attl.types)
    then [errFromOrigin(at,
      at.name ++ " expects " ++ toString(length(atTypeScheme.boundVars)) ++
      " type variables, but " ++ toString(length(attl.types)) ++ " were provided.")]
    else if map((.kind), atTypeScheme.boundVars) != map((.kindrep), attl.types)
    then [errFromOrigin(at,
      at.name ++ " has kind " ++ prettyKind(foldr(arrowKind, starKind(), map((.kind), atTypeScheme.boundVars))) ++
        " but type variable(s) have kind(s) " ++ implode(", ", map(compose(prettyKind, (.kindrep)), attl.types)) ++ ".")]
    else [];

  -- We have 4 types.
  -- 1: A type, from env, for the nonterminal (unapplied)
  -- 2: A type, from syntax, for the nonterminal (applied to type vars)
  -- 3: A type, from env, for the attribute (with bound type vars)
  -- 4: A type, from syntax, for the attribute (sharing the same type vars as #2)
  
  -- Our goal is to be able to take a (unknown) nonterminal type
  -- and yield the appropriate attribute type it corresponds to.
  
  -- To that end, we want two things:
  -- 1: A type that we can unify with some nonterminal type.
  -- 2: A type that, under that unification, will be the resulting attribute type.

  -- So we generate a list of fresh type variables corresponding to the types of #2,
  -- and generate two substitutions:
  -- 1: Rewrite the tyvars of type #3 to the types of type #4.
  -- 2: Rewrite our local tyvars to fresh variables.
  
  -- Thus, we apply #1 to our fresh type vars, perform both substitutions on #3, and get our goal.
  
  -- Fresh type variables that will go in the environment
  local tyVars :: [TyVar] = freshTyVars(nttl.freeVariables);
  
  -- Apply the nonterminal type to the type variables.
  -- NOT .monoType so we do something sensible if someone does "occurs on TypeAlias<a>" or something.
  nondecorated production protontty :: Type = appTypes(ntTypeScheme.typerep, map(varType, tyVars));
  
  -- This renames the vars from the environment
  -- at's env types -> type params containing local skolem vars  (vars -> types)
  local rewrite_from :: Substitution = zipVarsAndTypesIntoSubstitution(atTypeScheme.boundVars, attl.types);
  
  -- local skolem vars -> fresh type vars (vars -> vars)
  local rewrite_to :: Substitution = zipVarsIntoSubstitution(nttl.freeVariables, tyVars);
  
  -- These have to be two separate renamings, because the second renaming replaces names getting substituted in by the first renaming.
  nondecorated production protoatty :: Type = performRenaming(performRenaming(atTypeScheme.typerep, rewrite_from), rewrite_to);
  
  -- Now, finally, make sure we're not "redefining" the occurs.
  production occursCheck :: [OccursDclInfo] = getOccursDcl(at.lookupAttribute.fullName, nt.lookupType.fullName, top.env);
  
  top.errors <-
    if length(occursCheck) > 1
    then [errFromOrigin(at, "Attribute '" ++ at.name ++ "' already occurs on '" ++ nt.name ++ "'.")]
    else [];

  -- Make sure that no two annotations with the same short name (but different full names) can be declared on the same nonterminal
  local snat :: String = last(explode(":", at.name)); -- short name of annotation
  top.errors <-
    if at.lookupAttribute.dcl.isAnnotation && length(filter((.isAnnotation), getOccursDclBySN(snat, nt.lookupType.fullName, top.env))) > 1
    then [errFromOrigin(at, "Annotation with the same short name '" ++ snat ++ "' already occurs on '" ++ nt.name ++ "'.")]
    else [];

  top.errors <-
    if nt.lookupType.found && (!nt.lookupType.dcl.isType || !ntTypeScheme.typerep.isNonterminal)
    then [errFromOrigin(nt, nt.name ++ " is not a nonterminal. Attributes can only occur on nonterminals.")]
    else [];

  top.errors <-
    if !nt.lookupType.found || !at.lookupAttribute.found || !at.lookupAttribute.dcl.isAnnotation ||
       isExportedBy(top.grammarName, [nt.lookupType.dcl.sourceGrammar], top.compiledGrammars) then []
    else [errFromOrigin(top, "Annotations for a nonterminal must be in a module exported by the nonterminal's declaring grammar.")];
  
  top.errors <-
    if nt.lookupType.found && ntTypeScheme.isData && at.lookupAttribute.found
    then
      if at.lookupAttribute.dcl.isInherited
      then [errFromOrigin(top, "Inherited attributes may not occur on data nonterminals.")]
      else if at.lookupAttribute.dcl.isTranslation
      then [errFromOrigin(top, "Translation attributes may not occur on data nonterminals.")]
      else []
    else [];
}

abstract production errorAttributionDcl
top::AGDcl ::= msg::[Message] @at::QName attl::BracketedOptTypeExprs nt::QName nttl::BracketedOptTypeExprs
{
  top.unparse = "attribute " ++ at.unparse ++ attl.unparse ++ " occurs on " ++ nt.unparse ++ nttl.unparse ++ ";";
  top.occursDefs := [];
  top.errors <- msg;
  
  nttl.initialEnv = top.env;
  attl.env = nttl.envBindingTyVars;
  nt.env = top.env;
  nttl.env = nttl.envBindingTyVars;
  
  -- Decorate everything else to still check for errors
  top.errors <-
    -- binding errors in looking up these names.
    nt.lookupType.errors ++
    -- The nonterminal type list is strictly type VARIABLES only
    nttl.errorsTyVars;
  
  -- Make sure we get the number and kinds of tyvars correct for the NT
  top.errors <-
    case nt.lookupType.dcls of
    | ntDcl(_, ks, _, _, _) :: _ when length(ks) != length(nttl.types) ->
      [errFromOrigin(nt,
        nt.name ++ " expects " ++ toString(length(ks)) ++
        " type variables, but " ++ toString(length(nttl.types)) ++ " were provided.")]
    | ntDcl(_, ks, _, _, _) :: _ when ks != map((.kindrep), nttl.types) ->
      [errFromOrigin(nt,
        nt.name ++ " had kind " ++ foldr(arrowKind, starKind(), ks).typepp ++
        " but type variable(s) have kind(s) " ++ implode(", ", map(compose(prettyKind, (.kindrep)), nttl.types)) ++ ".")]
    | _ -> []
    end;
}

concrete production attributionDcl
top::AGDcl ::= 'attribute' at::QName attl::BracketedOptTypeExprs 'occurs' 'on' nt::QName nttl::BracketedOptTypeExprs ';'
{
  top.unparse = "attribute " ++ at.unparse ++ attl.unparse ++ " occurs on " ++ nt.unparse ++ nttl.unparse ++ ";";
  -- Note: we are supplying (the wrong) env to attl, nt, nttl here (and then re-decorating them after dispatching.)
  -- This is needed to permit computing flow defs on this production.
  propagate env;
  
  -- Workaround for circular dependency due to dispatching on env:
  -- Nothing used to build the env namespaces on which we dispatch can depend on
  -- the forward here.
  -- Attribution (occurs) defs, which obviously must depend on this forward, are
  -- specified by a seperate occursDefs attribute.
  -- Attribution dispatch productions should only define occursDefs (i.e. no new
  -- nonterminals, productions, attributes, etc.)
  top.defs := [];
  top.moduleNames := [];
  
  forwards to
    if !at.lookupAttribute.found
    then errorAttributionDcl(at.lookupAttribute.errors, at, @attl, @nt, @nttl)
    else at.lookupAttribute.dcl.attributionDispatcher(^at, ^attl, ^nt, ^nttl);
}

concrete production annotateDcl
top::AGDcl ::= 'annotation' at::QName attl::BracketedOptTypeExprs 'occurs' 'on' nt::QName nttl::BracketedOptTypeExprs ';'
{
  forwards to attributionDcl('attribute', @at, @attl, $4, $5, @nt, @nttl, $8);
}

-- Utility productions for extensions to inject extra declarations besides the occurs-on.
production extraDclsAttributionDcl implements AttributionDcl
top::AGDcl ::= at::QName attl::BracketedOptTypeExprs nt::QName nttl::BracketedOptTypeExprs prod::AttributionDcl extraDcls::AGDcl
{
  forwards to appendAGDcl(prod(@at, @attl, @nt, @nttl), @extraDcls);
}
abstract production altParamAttributionDcl implements AttributionDcl
top::AGDcl ::= at::QName attl::BracketedOptTypeExprs nt::QName nttl::BracketedOptTypeExprs prod::AttributionDcl newAttl::BracketedOptTypeExprs
{
  attl.env = nttl.envBindingTyVars;
  attl.flowEnv = top.flowEnv;
  attl.grammarName = top.grammarName;
  forwards to prod(@at, @newAttl, @nt, @nttl);
}
