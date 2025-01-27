grammar silver:compiler:definition:type:syntax;

inherited attribute constraintPos::ConstraintPosition;

tracked nonterminal ConstraintList
  -- This grammar doesn't export silver:compiler:definition:core, so the type concrete
  -- syntax doesn't "know about" the core layout terminals.
  -- Thus we have to set the layout explicitly for the "root" nonterminal here.
  layout {BlockComments, Comments, WhiteSpace}
  with config, grammarName, env, flowEnv, unparse, errors, defs, occursDefs, contexts, lexicalTypeVariables, lexicalTyVarKinds, constraintPos;
tracked nonterminal Constraint with config, grammarName, env, flowEnv, unparse, errors, defs, occursDefs, contexts, lexicalTypeVariables, lexicalTyVarKinds, constraintPos;

flowtype Constraint = decorate {grammarName, env, flowEnv, constraintPos};

propagate config, grammarName, env, flowEnv, errors, defs, occursDefs, lexicalTypeVariables, lexicalTyVarKinds, constraintPos
  on ConstraintList, Constraint;

concrete production consConstraint
top::ConstraintList ::= h::Constraint ',' t::ConstraintList
{
  top.unparse = h.unparse ++ ", " ++ t.unparse;
  top.contexts = h.contexts ++ t.contexts;
}
concrete production oneConstraint
top::ConstraintList ::= h::Constraint
{
  top.unparse = h.unparse;
  top.contexts = h.contexts;
}
abstract production nilConstraint
top::ConstraintList ::=
{
  top.unparse = "";
  top.contexts = [];
}

concrete production classConstraint
top::Constraint ::= c::QNameType t::TypeExpr
{
  top.unparse = c.unparse ++ " " ++ t.unparse;
  top.contexts =
    if !null(undecidableInstanceErrors) then [] -- Avoid a cycle in instance resolution checking
    else [instContext(fName, t.typerep)];
  
  production dcl::TypeDclInfo = c.lookupType.dcl;
  production fName::String = c.lookupType.fullName;
  
  top.errors <- c.lookupType.errors;
  top.errors <-
    if c.lookupType.found && dcl.isClass then []
    else [errFromOrigin(c, c.name ++ " is not a type class.")];
  top.errors <- t.errorsTyVars;
  
  -- We essentially permit FlexibleInstances but not UndecidableInstnaces,
  -- check that there are no class constraints if instance head is a type variable.
  -- This is required to ensure that instance resolution will terminate, otherwise
  -- one could write e.g. instance Eq a => Eq a.
  -- HOWEVER, this is sometimes really handy in some places (that we know are safe)
  -- within the standard library; turn off this check for those instances
  -- (equivalent to writing {-# LANGUAGE UndecidableInstances #-} in Haskell):
  production attribute undecidableInstanceClasses::[String] with ++;
  undecidableInstanceClasses := [
    -- Safe because instance for Show a has no further class constraints
    "silver:langutil:pp:Show"
  ];
  
  production undecidableInstanceErrors::[Message] =
    case top.constraintPos.instanceHead of
    | just(h) when (h, contains(fName, undecidableInstanceClasses)) matches (instContext(_, skolemType(_)), false) ->
      [errFromOrigin(top, s"The constraint ${top.unparse} is no smaller than the instance head ${prettyContext(h)}")]
    | _ -> []
    end;
  top.errors <- undecidableInstanceErrors;

  nondecorated local instDcl::InstDclInfo = top.constraintPos.classInstDcl(fName, t.typerep);
  top.defs <- [tcInstDef(instDcl)];
  top.defs <- transitiveSuperDefs(top.env, t.typerep, [], instDcl);
  top.occursDefs <- transitiveSuperOccursDefs(top.env, t.typerep, [], instDcl);

  top.lexicalTyVarKinds <-
    case t of
    | typeVariableTypeExpr(tv)
      -- Avoid circular inference if someone uses a class constraint within its own definition
      when top.constraintPos.classDefName != just(fName) ->
      [(tv.lexeme, c.lookupType.typeScheme.monoType.kindrep)]
    | _ -> []
    end;
} action {
  insert semantic token IdTypeClass_t at c.nameLoc;
}

concrete production inhOccursConstraint
top::Constraint ::= 'attribute' at::QName attl::BracketedOptTypeExprs 'occurs' 'on' t::TypeExpr
{
  top.unparse = "attribute " ++ at.unparse ++ attl.unparse ++ " occurs on " ++ t.unparse;
  top.contexts = [inhOccursContext(fName, attl.types, attrTy, t.typerep)];
  
  production dcl::AttributeDclInfo = at.lookupAttribute.dcl;
  production fName::String = at.lookupAttribute.fullName;

  top.errors <- at.lookupAttribute.errors;
  top.errors <-
    if at.lookupAttribute.found && !dcl.isInherited
    then [errFromOrigin(at, fName ++ " is not an inherited attribute")]
    else [];
  
  top.errors <-
    if attl.missingCount > 0
    then [errFromOrigin(attl, "Attribute type arguments cannot contain _")]
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

  top.errors <- t.errorsKindStar;

  local atTypeScheme::PolyType = at.lookupAttribute.typeScheme;
  local rewrite :: Substitution = zipVarsAndTypesIntoSubstitution(atTypeScheme.boundVars, attl.types);
  nondecorated production attrTy::Type =
    if map((.kind), atTypeScheme.boundVars) == map((.kindrep), attl.types)
    then performRenaming(atTypeScheme.typerep, rewrite)
    else errorType();

  nondecorated local instDcl::OccursDclInfo = top.constraintPos.occursInstDcl(fName, t.typerep, attrTy);
  top.occursDefs <- [instDcl];
}

concrete production synOccursConstraint
top::Constraint ::= 'attribute' at::QName attl::BracketedOptTypeExprs i::TypeExpr 'occurs' 'on' t::TypeExpr
{
  top.unparse = "attribute " ++ at.unparse ++ attl.unparse ++ " " ++ i.unparse ++ " occurs on " ++ t.unparse;
  top.contexts = [synOccursContext(fName, attl.types, attrTy, i.typerep, t.typerep)];
  
  production dcl::AttributeDclInfo = at.lookupAttribute.dcl;
  production fName::String = at.lookupAttribute.fullName;

  top.errors <- at.lookupAttribute.errors;
  top.errors <-
    if at.lookupAttribute.found && !dcl.isSynthesized
    then [errFromOrigin(at, fName ++ " is not a synthesized attribute")]
    else [];
  
  top.errors <-
    if attl.missingCount > 0
    then [errFromOrigin(attl, "Attribute type arguments cannot contain _")]
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

  top.errors <-
    if i.typerep.kindrep != inhSetKind()
    then [errFromOrigin(i, s"${i.unparse} has kind ${prettyKind(i.typerep.kindrep)}, but kind InhSet is expected here")]
    else [];

  top.errors <- t.errorsKindStar;

  local atTypeScheme::PolyType = at.lookupAttribute.typeScheme;
  local rewrite :: Substitution = zipVarsAndTypesIntoSubstitution(atTypeScheme.boundVars, attl.types);
  nondecorated production attrTy::Type =
    if map((.kind), atTypeScheme.boundVars) == map((.kindrep), attl.types)
    then performRenaming(atTypeScheme.typerep, rewrite)
    else errorType();

  nondecorated local instDcl::OccursDclInfo = top.constraintPos.occursInstDcl(fName, t.typerep, attrTy);
  top.occursDefs <- [instDcl];

  top.lexicalTyVarKinds <-
    case i of
    | typeVariableTypeExpr(tv) -> [(tv.lexeme, inhSetKind())]
    | _ -> []
    end;
}

concrete production annoOccursConstraint
top::Constraint ::= 'annotation' at::QName attl::BracketedOptTypeExprs 'occurs' 'on' t::TypeExpr
{
  top.unparse = "annotation " ++ at.unparse ++ attl.unparse ++ " occurs on " ++ t.unparse;
  top.contexts = [annoOccursContext(fName, attl.types, attrTy, t.typerep)];
  
  production dcl::AttributeDclInfo = at.lookupAttribute.dcl;
  production fName::String = at.lookupAttribute.fullName;

  top.errors <- at.lookupAttribute.errors;
  top.errors <-
    if at.lookupAttribute.found && !dcl.isAnnotation
    then [errFromOrigin(at, fName ++ " is not an annotation")]
    else [];
  
  top.errors <-
    if attl.missingCount > 0
    then [errFromOrigin(attl, "Annotation type arguments cannot contain _")]
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
  
  top.errors <- t.errorsKindStar;
  
  local atTypeScheme::PolyType = at.lookupAttribute.typeScheme;
  local rewrite :: Substitution = zipVarsAndTypesIntoSubstitution(atTypeScheme.boundVars, attl.types);
  nondecorated production attrTy::Type =
    if map((.kind), atTypeScheme.boundVars) == map((.kindrep), attl.types)
    then performRenaming(atTypeScheme.typerep, rewrite)
    else errorType();

  nondecorated local instDcl::OccursDclInfo = top.constraintPos.occursInstDcl(fName, t.typerep, attrTy);
  top.occursDefs <- [instDcl];
}

concrete production typeableConstraint
top::Constraint ::= 'runtimeTypeable' t::TypeExpr
{
  top.unparse = "runtimeTypeable " ++ t.unparse;
  top.contexts = [typeableContext(t.typerep)];
  
  top.errors <- t.errorsTyVars;
  top.errors <- t.errorsKindStar;

  nondecorated local instDcl::InstDclInfo = top.constraintPos.typeableInstDcl(t.typerep);
  top.defs <- [tcInstDef(instDcl)];
}

concrete production inhSubsetConstraint
top::Constraint ::= i1::TypeExpr 'subset' i2::TypeExpr
{
  top.unparse = i1.unparse ++ " subset " ++ i2.unparse;
  top.contexts = [inhSubsetContext(i1.typerep, i2.typerep)];

  top.errors <-
    if i1.typerep.kindrep != inhSetKind()
    then [errFromOrigin(top, s"${top.unparse} has kind ${prettyKind(i1.typerep.kindrep)}, but kind InhSet is expected here")]
    else [];
  top.errors <-
    if i2.typerep.kindrep != inhSetKind()
    then [errFromOrigin(top, s"${top.unparse} has kind ${prettyKind(i2.typerep.kindrep)}, but kind InhSet is expected here")]
    else [];

  nondecorated local instDcl::InstDclInfo = top.constraintPos.inhSubsetInstDcl(i1.typerep, i2.typerep);
  top.defs <-
    case top.constraintPos of
    | classPos(_, _) -> []
    | _ -> [tcInstDef(instDcl)]
    end;
  top.errors <-
    case top.constraintPos of
    | classPos(_, _) -> [errFromOrigin(top, "subset constraint not permitted as superclass")]
    | _ -> []
    end;

  top.lexicalTyVarKinds <-
    case i1 of
    | typeVariableTypeExpr(tv) -> [(tv.lexeme, inhSetKind())]
    | _ -> []
    end;
  top.lexicalTyVarKinds <-
    case i2 of
    | typeVariableTypeExpr(tv) -> [(tv.lexeme, inhSetKind())]
    | _ -> []
    end;
}

concrete production typeErrorConstraint
top::Constraint ::= 'typeError' msg::String_t
{
  top.unparse = "typeError " ++ msg.lexeme;
  top.contexts = [typeErrorContext(unescapeString(substring(1, length(msg.lexeme) - 1, msg.lexeme)))];

  top.errors <-
    case top.constraintPos of
    | instancePos(_, _) -> []
    | _ -> [errFromOrigin(top, "typeError constraint is only permitted on instances")]
    end;
}

synthesized attribute classInstDcl::(InstDclInfo ::= String Type);
synthesized attribute occursInstDcl::(OccursDclInfo ::= String Type Type);
synthesized attribute typeableInstDcl::(InstDclInfo ::= Type);
synthesized attribute inhSubsetInstDcl::(InstDclInfo ::= Type Type);
synthesized attribute classDefName::Maybe<String>;
synthesized attribute instanceHead::Maybe<Context>;
tracked data nonterminal ConstraintPosition
  with sourceGrammar, classInstDcl, occursInstDcl, typeableInstDcl, inhSubsetInstDcl, classDefName, instanceHead;

aspect default production
top::ConstraintPosition ::=
{
  top.classDefName = nothing();
  top.instanceHead = nothing();
}
abstract production instancePos
top::ConstraintPosition ::= instHead::Context tvs::[TyVar]
{
  local loc::Location = getParsedOriginLocationOrFallback(top);
  top.classInstDcl = instConstraintDcl(_, _, tvs, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.occursInstDcl = occursInstConstraintDcl(_, _, _, tvs, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.typeableInstDcl = typeableInstConstraintDcl(_, tvs, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.inhSubsetInstDcl = inhSubsetInstConstraintDcl(_, _, tvs, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.instanceHead = just(^instHead);
}
abstract production classPos
top::ConstraintPosition ::= className::String tvs::[TyVar]
{
  local loc::Location = getParsedOriginLocationOrFallback(top);
  top.classInstDcl = \ fName::String t::Type ->
    instSuperDcl(fName,
      currentInstDcl(className, t, sourceGrammar=top.sourceGrammar, sourceLocation=loc),
      sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.occursInstDcl = \ fName::String ntty::Type atty::Type ->
    occursSuperDcl(fName, atty,
      currentInstDcl(className, ntty, sourceGrammar=top.sourceGrammar, sourceLocation=loc),
      sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.typeableInstDcl = \ t::Type ->
    typeableSuperDcl(
      currentInstDcl(className, t, sourceGrammar=top.sourceGrammar, sourceLocation=loc),
      sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.inhSubsetInstDcl = error("subset constraint not permitted as superclass");
  top.classDefName = just(className);
}
abstract production classMemberPos
top::ConstraintPosition ::= className::String tvs::[TyVar]
{
  local loc::Location = getParsedOriginLocationOrFallback(top);
  top.classInstDcl = instConstraintDcl(_, _, tvs, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.occursInstDcl = occursInstConstraintDcl(_, _, _, tvs, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.typeableInstDcl = typeableInstConstraintDcl(_, tvs, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.inhSubsetInstDcl = inhSubsetInstConstraintDcl(_, _, tvs, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.classDefName = just(className);
  -- A bit strange, but class member constraints are sort of like instance constraints.
  -- However we don't know what the instance type actually is, and want to skip the
  -- decidability check, so just put errorType here for now.
  top.instanceHead = just(instContext(className, errorType()));
}
abstract production signaturePos
top::ConstraintPosition ::= sig::NamedSignature
{
  local loc::Location = getParsedOriginLocationOrFallback(top);
  top.classInstDcl = sigConstraintDcl(_, _, sig, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.occursInstDcl = occursSigConstraintDcl(_, _, _, sig, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.typeableInstDcl = typeableSigConstraintDcl(_, sig, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.inhSubsetInstDcl = inhSubsetSigConstraintDcl(_, _, sig, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
}
abstract production globalPos
top::ConstraintPosition ::= tvs::[TyVar]
{
  local loc::Location = getParsedOriginLocationOrFallback(top);
  -- These are translated the same as instance constraints.
  top.classInstDcl = instConstraintDcl(_, _, tvs, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.occursInstDcl = occursInstConstraintDcl(_, _, _, tvs, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.typeableInstDcl = typeableInstConstraintDcl(_, tvs, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
  top.inhSubsetInstDcl = inhSubsetInstConstraintDcl(_, _, tvs, sourceGrammar=top.sourceGrammar, sourceLocation=loc);
}

function transitiveSuperContexts
[Context] ::= env::Env ty::Type seenClasses::[String] className::String
{
  local dcls::[TypeDclInfo] = getTypeDcl(className, env);
  local dcl::TypeDclInfo = head(dcls);
  dcl.givenInstanceType = ^ty;
  local superClassNames::[String] = catMaybes(map((.contextClassName), dcl.superContexts));
  return
    if null(dcls) || contains(dcl.fullName, seenClasses)
    then []
    else unionsBy(
      sameSuperContext,
      dcl.superContexts ::
      map(transitiveSuperContexts(env, ^ty, dcl.fullName :: seenClasses, _), superClassNames));
}

-- TODO: Should be an equality attribute, maybe?
function sameSuperContext
Boolean ::= c1::Context c2::Context
{
  return
    case c1, c2 of
    | instContext(c1, _), instContext(c2, _) -> c1 == c2
    | inhOccursContext(a1, _, _, _), inhOccursContext(a2, _, _, _) -> a1 == a2
    | synOccursContext(a1, _, _, _, _), synOccursContext(a2, _, _, _, _) -> a1 == a2
    | typeableContext(_), typeableContext(_) -> true
    | _, _ -> false
    end;
}

function transitiveSuperDefs
[Def] ::= env::Env ty::Type seenClasses::[String] instDcl::InstDclInfo
{
  local dcls::[TypeDclInfo] = getTypeDcl(instDcl.fullName, env);
  local dcl::TypeDclInfo = head(dcls);
  dcl.givenInstanceType = ^ty;
  local superClassNames::[String] = catMaybes(map((.contextClassName), dcl.superContexts));
  local superInstDcls::[InstDclInfo] =
    map(
      instSuperDcl(_, ^instDcl, sourceGrammar=instDcl.sourceGrammar, sourceLocation=instDcl.sourceLocation),
      superClassNames);
  return
    if null(dcls) || contains(dcl.fullName, seenClasses)
    then []
    else
      -- This might introduce duplicate defs in "diamond subclassing" cases,
      -- but that shouldn't actually be an issue besides the (minor) added lookup overhead.
      flatMap(\ c::Context -> c.contextSuperDefs(^instDcl, dcl.sourceGrammar, dcl.sourceLocation), dcl.superContexts) ++
      flatMap(transitiveSuperDefs(env, ^ty, dcl.fullName :: seenClasses, _), superInstDcls);
}

function transitiveSuperOccursDefs
[OccursDclInfo] ::= env::Env ty::Type seenClasses::[String] instDcl::InstDclInfo
{
  local dcls::[TypeDclInfo] = getTypeDcl(instDcl.fullName, env);
  local dcl::TypeDclInfo = head(dcls);
  dcl.givenInstanceType = ^ty;
  local superClassNames::[String] = catMaybes(map((.contextClassName), dcl.superContexts));
  local superInstDcls::[InstDclInfo] =
    map(
      instSuperDcl(_, ^instDcl, sourceGrammar=instDcl.sourceGrammar, sourceLocation=instDcl.sourceLocation),
      superClassNames);
  return
    if null(dcls) || contains(dcl.fullName, seenClasses)
    then []
    else
      -- This might introduce duplicate defs in "diamond subclassing" cases,
      -- but that shouldn't actually be an issue besides the (minor) added lookup overhead.
      flatMap(\ c::Context -> c.contextSuperOccursDefs(^instDcl, dcl.sourceGrammar, dcl.sourceLocation), dcl.superContexts) ++
      flatMap(transitiveSuperOccursDefs(env, ^ty, dcl.fullName :: seenClasses, _), superInstDcls);
}
