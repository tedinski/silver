grammar silver:compiler:extension:autoattr;

synthesized attribute propagateDispatcher :: Propagate occurs on AttributeDclInfo;

synthesized attribute emptyVal::Expr occurs on AttributeDclInfo;
synthesized attribute appendProdName::String occurs on AttributeDclInfo;

aspect default production
top::AttributeDclInfo ::=
{
  top.propagateDispatcher = propagateError;
  top.emptyVal = error("Internal compiler error: must be defined for all monoid attribute declarations");
  top.appendProdName = error("Internal compiler error: must be defined for all translation monoid attribute declarations");
}

aspect production inhDcl
top::AttributeDclInfo ::= fn::String bound::[TyVar] ty::Type
{
  top.propagateDispatcher = propagateInh;
}

abstract production functorDcl
top::AttributeDclInfo ::= fn::String
{
  top.fullName = fn;
  propagate compareKey, isEqual;

  production tyVar::TyVar = freshTyVar(starKind());
  top.typeScheme = polyType([tyVar], varType(tyVar));
  top.isSynthesized = true;
  
  top.decoratedAccessHandler = synDecoratedAccessHandler;
  top.undecoratedAccessHandler = accessBounceDecorate(synDecoratedAccessHandler);
  top.dataAccessHandler = synDataAccessHandler;
  top.attrDefDispatcher = synthesizedAttributeDef; -- Allow normal syn equations
  top.attributionDispatcher = functorAttributionDcl;
  top.propagateDispatcher = propagateFunctor;
}

abstract production monoidDcl
top::AttributeDclInfo ::= fn::String bound::[TyVar] ty::Type empty::Expr append::Operation
{
  top.fullName = fn;
  propagate compareTo, compareKey;
  top.isEqual =
    case top.compareTo of
    | monoidDcl(fn2, _, _, empty2, append2) ->
      fn == fn2 && top.typeScheme == top.compareTo.typeScheme && empty.unparse == empty2.unparse && append.isEqual
    | _ -> false
    end;

  top.typeScheme = polyType(bound, ^ty);
  top.isSynthesized = true;
  top.emptyVal = ^empty;
  top.operation = ^append;
  
  top.decoratedAccessHandler = synDecoratedAccessHandler;
  top.undecoratedAccessHandler = accessBounceDecorate(synDecoratedAccessHandler);
  top.dataAccessHandler = synDataAccessHandler;
  top.attrDefDispatcher = monoidErrorRegularAttributeDef;
  top.attrBaseDefDispatcher = synBaseColAttributeDef;
  top.attrAppendDefDispatcher = synAppendColAttributeDef;
  top.attributionDispatcher = defaultAttributionDcl;
  top.propagateDispatcher = propagateMonoid;
}

abstract production monoidTransDcl
top::AttributeDclInfo ::= fn::String bound::[TyVar] ty::Type empty::Expr append::String
{
  top.fullName = fn;
  propagate compareTo, compareKey;
  top.isEqual =
    case top.compareTo of
    | monoidTransDcl(fn2, _, _, empty2, append2) ->
      fn == fn2 && top.typeScheme == top.compareTo.typeScheme && empty.unparse == empty2.unparse && append == append2
    | _ -> false
    end;
  
  top.typeScheme = polyType(bound, ^ty);
  top.isSynthesized = true;
  top.isTranslation = true;
  top.emptyVal = ^empty;
  top.appendProdName = append;

  top.decoratedAccessHandler = transDecoratedAccessHandler;
  top.undecoratedAccessHandler = transUndecoratedAccessErrorHandler;
  top.dataAccessHandler = transUndecoratedAccessErrorHandler;
  top.attrDefDispatcher = synthesizedAttributeDef; -- Allow normal syn equations
  top.attributionDispatcher = defaultAttributionDcl;
  top.propagateDispatcher = propagateMonoidTrans;
}

abstract production destructDcl
top::AttributeDclInfo ::= fn::String
{
  top.fullName = fn;
  propagate compareKey, isEqual;

  production tyVar::TyVar = freshTyVar(starKind());
  production inhsTyVar::TyVar = freshTyVar(inhSetKind());
  top.typeScheme = polyType([tyVar, inhsTyVar], decoratedType(varType(tyVar), varType(inhsTyVar)));
  top.isInherited = true;
  
  top.decoratedAccessHandler = inhDecoratedAccessHandler;
  top.undecoratedAccessHandler = inhUndecoratedAccessErrorHandler;
  top.dataAccessHandler = inhUndecoratedAccessErrorHandler;
  top.attrDefDispatcher = inheritedAttributeDef; -- Allow normal inh equations
  top.attributionDispatcher = destructAttributionDcl;
  top.propagateDispatcher = propagateDestruct;
}

abstract production equalityDcl
top::AttributeDclInfo ::= inh::String syn::String
{
  top.fullName = syn;
  propagate compareKey, isEqual;

  top.typeScheme = monoType(boolType());
  top.isSynthesized = true;
  
  top.decoratedAccessHandler = synDecoratedAccessHandler;
  top.undecoratedAccessHandler = accessBounceDecorate(synDecoratedAccessHandler);
  top.dataAccessHandler = synDataAccessHandler;
  top.attrDefDispatcher = synthesizedAttributeDef; -- Allow normal syn equations
  top.attributionDispatcher = defaultAttributionDcl;
  top.propagateDispatcher = propagateEquality(inh);
}

abstract production orderingKeyDcl
top::AttributeDclInfo ::= syn::String
{
  top.fullName = syn;
  propagate compareKey, isEqual;

  top.typeScheme = monoType(stringType());
  top.isSynthesized = true;
  
  top.decoratedAccessHandler = synDecoratedAccessHandler;
  top.undecoratedAccessHandler = accessBounceDecorate(synDecoratedAccessHandler);
  top.dataAccessHandler = synDataAccessHandler;
  top.attrDefDispatcher = synthesizedAttributeDef; -- Allow normal syn equations
  top.attributionDispatcher = defaultAttributionDcl;
  top.propagateDispatcher = propagateOrderingKey;
}

abstract production orderingDcl
top::AttributeDclInfo ::= inh::String keySyn::String syn::String
{
  top.fullName = syn;
  propagate compareKey, isEqual;

  top.typeScheme = monoType(intType());
  top.isSynthesized = true;
  
  top.decoratedAccessHandler = synDecoratedAccessHandler;
  top.undecoratedAccessHandler = accessBounceDecorate(synDecoratedAccessHandler);
  top.dataAccessHandler = synDataAccessHandler;
  top.attrDefDispatcher = synthesizedAttributeDef; -- Allow normal syn equations
  top.attributionDispatcher = defaultAttributionDcl;
  top.propagateDispatcher = propagateOrdering(inh, keySyn);
}

abstract production biequalityPartialDcl
top::AttributeDclInfo ::= inh::String synPartial::String syn::String
{
  top.fullName = synPartial;
  propagate compareKey, isEqual;

  top.typeScheme = monoType(boolType());
  top.isSynthesized = true;
  
  top.decoratedAccessHandler = synDecoratedAccessHandler;
  top.undecoratedAccessHandler = accessBounceDecorate(synDecoratedAccessHandler);
  top.dataAccessHandler = synDataAccessHandler;
  top.attrDefDispatcher = synthesizedAttributeDef; -- Allow normal syn equations
  top.attributionDispatcher = defaultAttributionDcl;
  top.propagateDispatcher = propagateBiequalitySynPartial(inh, syn);
}

abstract production biequalityDcl
top::AttributeDclInfo ::= inh::String synPartial::String syn::String
{
  top.fullName = syn;
  propagate compareKey, isEqual;

  top.typeScheme = monoType(boolType());
  top.isSynthesized = true;
  
  top.decoratedAccessHandler = synDecoratedAccessHandler;
  top.undecoratedAccessHandler = accessBounceDecorate(synDecoratedAccessHandler);
  top.dataAccessHandler = synDataAccessHandler;
  top.attrDefDispatcher = synthesizedAttributeDef; -- Allow normal syn equations
  top.attributionDispatcher = defaultAttributionDcl;
  top.propagateDispatcher = propagateBiequalitySyn(inh, synPartial);
}

abstract production threadedInhDcl
top::AttributeDclInfo ::= inh::String syn::String bound::[TyVar] ty::Type o::Maybe<Operation> rev::Boolean
{
  top.fullName = inh;
  propagate compareKey;
  top.isEqual =
    case top.compareTo of
    | threadedInhDcl(inh2, syn2, _, _, _, rev2) ->
      inh == inh2 && syn == syn2 && top.typeScheme == top.compareTo.typeScheme && rev == rev2
    | _ -> false
    end;

  top.typeScheme = polyType(bound, ^ty);
  top.isInherited = true;
  top.isCollection = o.isJust;
  top.operation = o.fromJust;
  
  top.decoratedAccessHandler = inhDecoratedAccessHandler;
  top.undecoratedAccessHandler = inhUndecoratedAccessErrorHandler;
  top.dataAccessHandler = inhUndecoratedAccessErrorHandler;
  top.attrDefDispatcher =
    if o.isJust
    then collectionErrorRegularAttributeDef
    else inheritedAttributeDef; -- Allow normal inh equations
  top.attrBaseDefDispatcher = 
    if o.isJust
    then inhBaseColAttributeDef -- Allow normal inh base equations
    else nonCollectionErrorBaseAttributeDef;
  top.attrAppendDefDispatcher = 
    if o.isJust
    then inhAppendColAttributeDef  -- Allow normal inh append equations
    else nonCollectionErrorAppendAttributeDef;
  top.attributionDispatcher = defaultAttributionDcl;
  top.propagateDispatcher = propagateThreadedInh(o.isJust, rev, syn);
}

abstract production threadedSynDcl
top::AttributeDclInfo ::= inh::String syn::String bound::[TyVar] ty::Type o::Maybe<Operation> rev::Boolean
{
  top.fullName = syn;
  propagate compareKey;
  top.isEqual =
    case top.compareTo of
    | threadedSynDcl(inh2, syn2, _, _, _, rev2) ->
      inh == inh2 && syn == syn2 && top.typeScheme == top.compareTo.typeScheme && rev == rev2
    | _ -> false
    end;

  top.typeScheme = polyType(bound, ^ty);
  top.isSynthesized = true;
  top.isCollection = o.isJust;
  top.operation = o.fromJust;
  
  top.decoratedAccessHandler = synDecoratedAccessHandler;
  top.undecoratedAccessHandler = accessBounceDecorate(synDecoratedAccessHandler);
  top.dataAccessHandler = synDataAccessHandler;
  top.attrDefDispatcher =
    if o.isJust
    then collectionErrorRegularAttributeDef
    else synthesizedAttributeDef; -- Allow normal syn equations
  top.attrBaseDefDispatcher = 
    if o.isJust
    then synBaseColAttributeDef -- Allow normal syn base equations
    else nonCollectionErrorBaseAttributeDef;
  top.attrAppendDefDispatcher = 
    if o.isJust
    then synAppendColAttributeDef  -- Allow normal syn append equations
    else nonCollectionErrorAppendAttributeDef;
  top.attributionDispatcher = defaultAttributionDcl;
  top.propagateDispatcher = propagateThreadedSyn(o.isJust, rev, inh);
}
