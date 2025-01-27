grammar silver:compiler:definition:type:syntax;

imports silver:compiler:definition:core;
imports silver:compiler:definition:type;
imports silver:compiler:definition:env;
imports silver:compiler:definition:flow:syntax;
imports silver:compiler:definition:flow:env;

tracked nonterminal TypeExpr  with config, grammarName, errors, env, flowEnv, unparse, typerep, lexicalTypeVariables, lexicalTyVarKinds, errorsTyVars, errorsKindStar, freeVariables, mentionedAliases, onNt, errorsInhSet, typerepInhSet;
tracked nonterminal Signature with config, grammarName, errors, env, flowEnv, unparse, typerep, lexicalTypeVariables, lexicalTyVarKinds, mentionedAliases;
tracked nonterminal SignatureLHS with config, grammarName, errors, env, flowEnv, unparse, maybeType, lexicalTypeVariables, lexicalTyVarKinds, mentionedAliases;
tracked nonterminal TypeExprs with config, grammarName, errors, env, unparse, flowEnv, types, missingCount, lexicalTypeVariables, lexicalTyVarKinds, appArgKinds, appLexicalTyVarKinds, errorsTyVars, errorsKindStar, freeVariables, mentionedAliases;
tracked nonterminal BracketedTypeExprs with config, grammarName, errors, env, flowEnv, unparse, types, missingCount, lexicalTypeVariables, lexicalTyVarKinds, appArgKinds, appLexicalTyVarKinds, errorsTyVars, freeVariables, mentionedAliases, envBindingTyVars, initialEnv;
tracked nonterminal BracketedOptTypeExprs with config, grammarName, errors, env, flowEnv, unparse, types, missingCount, lexicalTypeVariables, lexicalTyVarKinds, appArgKinds, appLexicalTyVarKinds, errorsTyVars, freeVariables, mentionedAliases, envBindingTyVars, initialEnv;
tracked nonterminal NamedTypeExprs with config, grammarName, errors, env, unparse, flowEnv, namedTypes, lexicalTypeVariables, lexicalTyVarKinds, errorsKindStar, freeVariables, mentionedAliases;

synthesized attribute maybeType :: Maybe<Type>;
synthesized attribute types :: [Type];
synthesized attribute missingCount::Integer;

-- Important: These should be IN-ORDER and include ALL type variables that appear, including duplicates!
monoid attribute lexicalTypeVariables :: [String];
-- freeVariables also occurs on TypeExprs, and should be IN ORDER

monoid attribute lexicalTyVarKinds :: [Pair<String Kind>];

inherited attribute appArgKinds :: [Kind];
monoid attribute appLexicalTyVarKinds :: [Pair<String Kind>];

-- These attributes are used if we're using the TypeExprs as type variables-only.
monoid attribute errorsTyVars :: [Message];
-- A new environment, with the type variables in this list appearing bound
inherited attribute initialEnv :: Env;
synthesized attribute envBindingTyVars :: Env;

monoid attribute errorsKindStar::[Message];

-- The set of full names of type aliases that are mentioned by/transitively depended on by this type expression.
monoid attribute mentionedAliases :: [String];


-- Better error checking and type information if this type expression is an inherited attribute set
-- for a particular nonterminal (e.g. the {env} in Decorated Expr with {env}).
-- We can check that the attributes actually occur on the nonterminal,
-- and also can interpret {decorate} or {forward} since we can look up those flow types.
-- The nonterminal type is specified by the attribute onNt, which should only be used by these attributes.
synthesized attribute errorsInhSet::[Message];
synthesized attribute typerepInhSet::Type;
flowtype errorsInhSet {decorate, onNt} on TypeExpr;
flowtype typerepInhSet {decorate, onNt} on TypeExpr;

flowtype TypeExpr =
  decorate {grammarName, env, flowEnv}, forward {decorate},
  freeVariables {decorate}, lexicalTypeVariables {decorate}, lexicalTyVarKinds {decorate},
  errors {decorate}, errorsTyVars {decorate}, errorsKindStar {decorate};

-- typerep requires flowEnv to look up default ref sets
flowtype typerep {grammarName, env, flowEnv} on TypeExpr, Signature;
flowtype maybeType {grammarName, env, flowEnv} on SignatureLHS;
flowtype types {grammarName, env, flowEnv} on TypeExprs, BracketedTypeExprs, BracketedOptTypeExprs;

propagate errors on TypeExpr, Signature, SignatureLHS, TypeExprs, BracketedTypeExprs, BracketedOptTypeExprs, NamedTypeExprs excluding refTypeExpr;
propagate config, grammarName, env, flowEnv, lexicalTypeVariables, lexicalTyVarKinds
  on TypeExpr, Signature, SignatureLHS, TypeExprs, BracketedTypeExprs, BracketedOptTypeExprs, NamedTypeExprs;
propagate appLexicalTyVarKinds on TypeExprs, BracketedTypeExprs, BracketedOptTypeExprs;
propagate errorsTyVars on TypeExprs, BracketedTypeExprs, BracketedOptTypeExprs;
propagate errorsKindStar on TypeExprs, NamedTypeExprs;
propagate mentionedAliases on TypeExpr, Signature, SignatureLHS, TypeExprs, BracketedTypeExprs, BracketedOptTypeExprs, NamedTypeExprs;

function addNewLexicalTyVars
[Def] ::= gn::String lk::[Pair<String Kind>] l::[String]
{
  local loc::Location = getParsedOriginLocationOrFallback(ambientOrigin());
  return map(\ n::String -> lexTyVarDef(gn, loc, n, freshTyVarNamed(n, fromMaybe(starKind(), lookup(n, lk)))), l);
}

aspect default production
top::TypeExpr ::=
{
  -- This has to do with type lists that are type variables only.
  -- We don't have a separate nonterminal for this, because we'd like to produce
  -- "semantic" errors, rather than parse errors for this.
  top.errorsTyVars := [errFromOrigin(top, top.unparse ++ " is not permitted here, only type variables are")];
  top.freeVariables = top.typerep.freeVariables;
  top.errorsKindStar :=
    if top.typerep.kindrep != starKind()
    then [errFromOrigin(top, s"${top.unparse} has kind ${prettyKind(top.typerep.kindrep)}, but kind * is expected here")]
    else [];
  top.errorsInhSet = top.errors;
  top.typerepInhSet = top.typerep;
}

abstract production errorTypeExpr
top::TypeExpr ::= e::[Message]
{
  top.unparse = s"{- Errors:\n${messagesToString(e)} -}";
  
  top.typerep = errorType();
  
  top.errors <- e;
}

abstract production typerepTypeExpr
top::TypeExpr ::= t::Type
{
  top.unparse = prettyType(^t);

  top.typerep = ^t;

  top.errorsTyVars :=
    case t of
    | varType(_) -> []
    | skolemType(_) -> []
    | _ -> [errFromOrigin(top, top.unparse ++ " is not permitted here, only type variables are")]
    end;
}

concrete production integerTypeExpr
top::TypeExpr ::= 'Integer'
{
  top.unparse = "Integer";

  top.typerep = intType();
}

concrete production floatTypeExpr
top::TypeExpr ::= 'Float'
{
  top.unparse = "Float";

  top.typerep = floatType();
}

concrete production stringTypeExpr
top::TypeExpr ::= 'String'
{
  top.unparse = "String";

  top.typerep = stringType();
}

concrete production booleanTypeExpr
top::TypeExpr ::= 'Boolean'
{
  top.unparse = "Boolean";

  top.typerep = boolType();
}

concrete production terminalIdTypeExpr
top::TypeExpr ::= 'TerminalId'
{
  top.unparse = "TerminalId";

  top.typerep = terminalIdType();
}

concrete production inhSetTypeExpr
top::TypeExpr ::= InhSetLCurly_t inhs::FlowSpecInhs '}'
{
  top.unparse = s"{${inhs.unparse}}";
  
  top.typerep = inhSetType(sort(nub(inhs.inhList)));
  inhs.onNt = errorType();

  -- When we are in a refTypeExpr where we know the nonterminal type,
  -- decorate the inhSetTypeExpr with onNt for better errors and lookup disambiguation.
  production ntInhs::FlowSpecInhs = ^inhs;
  ntInhs.config = top.config;
  ntInhs.grammarName = top.grammarName;
  ntInhs.env = top.env;
  ntInhs.flowEnv = top.flowEnv;
  ntInhs.onNt = top.onNt;

  top.errorsInhSet = ntInhs.errors;
  top.typerepInhSet = inhSetType(sort(ntInhs.inhList));
}

concrete production nominalTypeExpr
top::TypeExpr ::= q::QNameType
{
  top.unparse = q.unparse;

  top.mentionedAliases <-
    if q.lookupType.found && q.lookupType.dcl.isTypeAlias
    then q.lookupType.fullName :: q.lookupType.dcl.mentionedAliases
    else [];

  top.errors <- q.lookupType.errors;
  top.errors <-
    if !q.lookupType.found || q.lookupType.dcl.isType then []
    else if q.lookupType.dcl.isTypeAlias  -- Raise a less confusing error if we see an unapplied type alias
    then [errFromOrigin(top, q.name ++ " is a type alias, expecting " ++ toString(length(q.lookupType.dcl.typeScheme.boundVars)) ++ " type arguments.")]
    else [errFromOrigin(top, q.name ++ " is not a type.")];

  top.typerep = q.lookupType.typeScheme.typerep; -- NOT .monoType since this can be a polyType when an error is raised
} action {
  insert semantic token IdType_t at q.nameLoc;
}

concrete production typeVariableTypeExpr
top::TypeExpr ::= tv::IdLower_t
{
  top.unparse = tv.lexeme;
  
  local attribute hack::QNameLookup<TypeDclInfo>;
  hack = customLookup("type", getTypeDcl(tv.lexeme, top.env), tv.lexeme);
  
  top.typerep = hack.typeScheme.monoType;
  top.errors <- hack.errors;
  top.errorsTyVars := [];

  top.lexicalTypeVariables <- [tv.lexeme];
} action {
  insert semantic token IdTypeVar_t at tv.location;
}

concrete production kindSigTypeVariableTypeExpr
top::TypeExpr ::= '(' tv::IdLower_t '::' k::KindExpr ')'
{
  top.unparse = s"(${tv.lexeme} :: ${k.unparse})";
  
  local attribute hack::QNameLookup<TypeDclInfo>;
  hack = customLookup("type", getTypeDcl(tv.lexeme, top.env), tv.lexeme);
  
  top.typerep = hack.typeScheme.monoType;
  top.errors <- hack.errors;
  top.errorsTyVars := [];

  top.lexicalTypeVariables <- [tv.lexeme];
  top.lexicalTyVarKinds <- [(tv.lexeme, k.kindrep)];
} action {
  insert semantic token IdTypeVar_t at tv.location;
}

concrete production appTypeExpr
top::TypeExpr ::= ty::TypeExpr tl::BracketedTypeExprs
{
  top.unparse = ty.unparse ++ tl.unparse;
  
  propagate grammarName, env, flowEnv;
  propagate lexicalTypeVariables; -- Needed to avoid circularity

  forwards to
    case ty of
    | nominalTypeExpr(q) when
        q.lookupType.found && q.lookupType.dcl.isTypeAlias &&
        length(q.lookupType.typeScheme.boundVars) > 0 ->
      aliasAppTypeExpr(q, @tl)
    | _ -> typeAppTypeExpr(ty, @tl)
    end;
}

abstract production aliasAppTypeExpr
top::TypeExpr ::= q::Decorated QNameType with {env}  tl::BracketedTypeExprs
{
  top.unparse = q.unparse ++ tl.unparse;

  production ts::PolyType = q.lookupType.typeScheme;
  top.typerep = performRenaming(ts.typerep, zipVarsAndTypesIntoSubstitution(ts.boundVars, tl.types));

  top.mentionedAliases <- q.lookupType.fullName :: q.lookupType.dcl.mentionedAliases;

  local tlCount::Integer = length(tl.types) + tl.missingCount;
  top.errors <-
    if tlCount != length(ts.boundVars)
    then [errFromOrigin(top, q.lookupType.fullName ++ " expects " ++ toString(length(ts.boundVars)) ++ " type arguments, but there are " ++ toString(tlCount) ++ " supplied here.")]
    else [];
  top.errors <-
    if tl.missingCount > 0
    then [errFromOrigin(tl, q.lookupType.fullName ++ " is a type alias and cannot be partially applied.")]
    else [];
}

abstract production typeAppTypeExpr
top::TypeExpr ::= ty::Decorated TypeExpr tl::BracketedTypeExprs
{
  top.unparse = ty.unparse ++ tl.unparse;

  top.typerep = if null(kindErrors) then appTypes(ty.typerep, tl.types) else errorType();

  top.mentionedAliases <- ty.mentionedAliases;

  top.errors <- ty.errors;

  local tlCount::Integer = length(tl.types) + tl.missingCount;
  local tlKinds::[Kind] = map((.kindrep), tl.types);
  local kindErrors::[Message] =
    if tlCount != length(ty.typerep.kindrep.argKinds)
    then [errFromOrigin(top, ty.unparse ++ " has kind " ++ prettyKind(ty.typerep.kindrep) ++ ", but there are " ++ toString(tlCount) ++ " type arguments supplied here.")]
    else if take(length(tlKinds), ty.typerep.kindrep.argKinds) != tlKinds
    then [errFromOrigin(top, ty.unparse ++ " has kind " ++ prettyKind(ty.typerep.kindrep) ++ ", but argument(s) have kind(s) " ++ implode(", ", map(prettyKind, tlKinds)))]
    else [];
  top.errors <- kindErrors;

  tl.appArgKinds =
    case ty of
    | nominalTypeExpr(q) when q.lookupType.found -> q.lookupType.dcl.kindrep.argKinds
    | _ -> []
    end;
  top.lexicalTyVarKinds <-
    case ty of
    | typeVariableTypeExpr(tv) ->
      -- This assumes that all type args have kind *.
      -- If that is not the case, then an explcit kind signature is needed on ty,
      -- which will shadow this entry in the lexicalTyVarKinds list.
      [(tv.lexeme, constructorKind(tlCount))]

    | nominalTypeExpr(q) when q.lookupType.found -> tl.appLexicalTyVarKinds
    | _ -> []
    end;
}

concrete production refTypeExpr
top::TypeExpr ::= 'Decorated' t::TypeExpr 'with' i::TypeExpr
{
  top.unparse = "Decorated " ++ t.unparse ++ " with " ++ i.unparse;
  
  i.onNt = t.typerep;

  top.typerep = decoratedType(t.typerep, i.typerepInhSet);
  
  top.errors := i.errorsInhSet ++ t.errors;
  top.errors <-
    case t.typerep.baseType of
    | nonterminalType(fn,_,true,_) -> [errFromOrigin(t, s"${fn} is a data nonterminal and cannot be decorated")]
    | nonterminalType(_,_,_,_) -> []
    | skolemType(_) -> []
    | varType(_) -> []
    | _ -> [errFromOrigin(t, t.unparse ++ " is not a nonterminal, and cannot be Decorated.")]
    end;
  top.errors <-
    if i.typerep.kindrep != inhSetKind()
    then [errFromOrigin(i, s"${i.unparse} has kind ${prettyKind(i.typerep.kindrep)}, but kind InhSet is expected here")]
    else [];
  top.errors <- t.errorsKindStar;

  top.lexicalTyVarKinds <-
    case i of
    | typeVariableTypeExpr(tv) -> [(tv.lexeme, inhSetKind())]
    | _ -> []
    end;
}

concrete production refDefaultTypeExpr
top::TypeExpr ::= 'Decorated' t::TypeExpr
{
  top.unparse = "Decorated " ++ t.unparse;

  top.typerep =
    decoratedType(t.typerep,
      inhSetType(sort(concat(getInhsForNtRef(t.typerep.typeName, top.flowEnv)))));
  
  top.errors <-
    case t.typerep.baseType of
    | nonterminalType(fn,_,true,_) -> [errFromOrigin(t, s"${fn} is a data nonterminal and cannot be decorated")]
    | nonterminalType(_,_,_,_) -> []
    | skolemType(_) -> [errFromOrigin(t, "polymorphic Decorated types must specify an explicit reference set")]
    | varType(_) -> [errFromOrigin(t, "polymorphic Decorated types must specify an explicit reference set")]
    | _ -> [errFromOrigin(t, t.unparse ++ " is not a nonterminal, and cannot be Decorated.")]
    end;
}

concrete production funTypeExpr
top::TypeExpr ::= '(' sig::Signature ')'
{
  top.unparse = "(" ++ sig.unparse ++ ")";
  top.typerep = sig.typerep;
}

concrete production signatureEmptyRhs
top::Signature ::= l::SignatureLHS '::='
{
  top.unparse = l.unparse ++ " ::=";
  top.typerep = appTypes(functionType(0, []), case l.maybeType of just(t) -> [t] | nothing() -> [] end);
}

concrete production psignature
top::Signature ::= l::SignatureLHS '::=' list::TypeExprs 
{
  top.unparse = l.unparse ++ " ::= " ++ list.unparse;
  top.typerep =
    appTypes(
      functionType(length(list.types) + list.missingCount, []),
      list.types ++ case l.maybeType of just(t) -> [t] | nothing() -> [] end);
  
  top.errors <- list.errorsKindStar;
  top.errors <-
    if l.maybeType.isJust && list.missingCount > 0
    then [errFromOrigin(l, "Return type cannot be present when argument types are missing")]
    else [];
}

concrete production signatureOnlyNamed
top::Signature ::= l::SignatureLHS '::=' ';' namedList::NamedTypeExprs
{
  top.unparse = l.unparse ++ " ::= ; " ++ namedList.unparse;

  local names::[String] = sort(map(fst, namedList.namedTypes));
  top.typerep =
    appTypes(
      functionType(0, names),
      map((.fromJust), map(lookup(_, namedList.namedTypes), names)) ++
      case l.maybeType of just(t) -> [t] | nothing() -> [] end);

  top.errors <- namedList.errorsKindStar;
}

concrete production signatureNamed
top::Signature ::= l::SignatureLHS '::=' list::TypeExprs ';' namedList::NamedTypeExprs
{
  top.unparse = l.unparse ++ " ::= " ++ list.unparse ++ "; " ++ namedList.unparse;

  local names::[String] = sort(map(fst, namedList.namedTypes));
  top.typerep =
    appTypes(
      functionType(length(list.types) + list.missingCount, names),
      list.types ++
      map((.fromJust), map(lookup(_, namedList.namedTypes), names)) ++
      case l.maybeType of just(t) -> [t] | nothing() -> [] end);
  
  top.errors <- list.errorsKindStar;
  top.errors <- namedList.errorsKindStar;
  top.errors <-
    if list.missingCount > 0
    then [errFromOrigin(namedList, "Named parameters cannot be present when argument types are missing")]
    else [];
}

concrete production presentSignatureLhs
top::SignatureLHS ::= t::TypeExpr
{
  top.unparse = t.unparse;
  top.maybeType = just(t.typerep);

  top.errors <- t.errorsKindStar;
}

concrete production missingSignatureLhs
top::SignatureLHS ::= '_'
{
  top.unparse = "_";
  top.maybeType = nothing();
}

-- Bracketed Optional Type Lists -----------------------------------------------

concrete production botlNone
top::BracketedOptTypeExprs ::=
{
  top.unparse = "";
  forwards to botlSome(bTypeList('<', typeListNone(), '>'));
}

concrete production botlSome
top::BracketedOptTypeExprs ::= btl::BracketedTypeExprs
{
  top.unparse = btl.unparse;
  top.types = btl.types;
  top.missingCount = btl.missingCount;
  top.freeVariables = btl.freeVariables;
  top.envBindingTyVars = btl.envBindingTyVars;
  
  btl.initialEnv = top.initialEnv;
  btl.appArgKinds = top.appArgKinds;
}

concrete production bTypeList
top::BracketedTypeExprs ::= '<' tl::TypeExprs '>'
{
  top.unparse = "<" ++ tl.unparse ++ ">";

  top.types = tl.types;
  top.missingCount = tl.missingCount;

  top.freeVariables = tl.freeVariables;
  
  top.errorsTyVars <-
    if length(tl.lexicalTypeVariables) != length(nub(tl.lexicalTypeVariables))
    then [errFromOrigin(top, "Type parameter list repeats type variable names")]
    else [];
  top.errorsTyVars <-
    if tl.missingCount > 0
    then [errFromOrigin(top, "Type parameter list cannot contain _")]
    else [];

  top.envBindingTyVars =
    newScopeEnv(
      addNewLexicalTyVars(top.grammarName, tl.lexicalTyVarKinds, tl.lexicalTypeVariables),
      top.initialEnv);

  tl.appArgKinds = top.appArgKinds;
}

-- TypeExprs -------------------------------------------------------------------

abstract production typeListNone
top::TypeExprs ::=
{
  top.unparse = "";
  top.types = [];
  top.missingCount = 0;
  top.freeVariables = [];
}

concrete production typeListSingle
top::TypeExprs ::= t::TypeExpr
{
  top.unparse = t.unparse;
  forwards to typeListCons(@t, typeListNone());
}

concrete production typeListSingleMissing
top::TypeExprs ::= '_'
{
  top.unparse = "_";
  forwards to typeListConsMissing($1, typeListNone());
}

concrete production typeListCons
top::TypeExprs ::= t::TypeExpr list::TypeExprs
{
  top.unparse = t.unparse ++ " " ++ list.unparse;
  top.types = t.typerep :: list.types;
  top.missingCount = list.missingCount;
  top.freeVariables = t.freeVariables ++ list.freeVariables;

  list.appArgKinds =
    case top.appArgKinds of
    | [] -> []
    | _ :: t -> t
    end;
  top.appLexicalTyVarKinds <-
    case t, top.appArgKinds of
    | typeVariableTypeExpr(tv), k :: _ -> [(tv.lexeme, k)]
    | _, _ -> []
    end;
}

concrete production typeListConsMissing
top::TypeExprs ::= '_' list::TypeExprs
{
  top.unparse = "_ " ++ list.unparse;
  top.types = list.types;
  top.missingCount = list.missingCount + 1;
  top.freeVariables = list.freeVariables;

  list.appArgKinds =
    case top.appArgKinds of
    | [] -> []
    | _ :: t -> t
    end;
  
  top.errors <-
    if length(list.types) > 0
    then [err($1.location, "Missing type argument cannot be followed by a provided argument")]
    else [];
}

-- NamedTypeExprs -------------------------------------------------------------------

abstract production namedTypeListNone
top::NamedTypeExprs ::=
{
  top.unparse = "";
  top.namedTypes = [];
  top.freeVariables = [];
}

concrete production namedTypeListSingle
top::NamedTypeExprs ::= n::Name '::' t::TypeExpr
{
  top.unparse = t.unparse;
  forwards to namedTypeListCons(@n, $2, @t, namedTypeListNone());
}

concrete production namedTypeListCons
top::NamedTypeExprs ::= n::Name '::' t::TypeExpr list::NamedTypeExprs
{
  top.unparse = n.unparse ++ "::" ++ t.unparse ++ " " ++ list.unparse;
  top.namedTypes = (n.name, t.typerep) :: list.namedTypes;
  top.freeVariables = t.freeVariables ++ list.freeVariables;
}
