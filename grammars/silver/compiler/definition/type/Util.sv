grammar silver:compiler:definition:type;

-- Quick check to see if an error message should be suppressed
synthesized attribute isError :: Boolean;

-- Check for whether the type can be applied
synthesized attribute isApplicable :: Boolean;

synthesized attribute inputTypes :: [Type];
synthesized attribute outputType :: Type;
synthesized attribute namedTypes :: [Pair<String Type>];
synthesized attribute arity :: Integer;
synthesized attribute baseType :: Type;
synthesized attribute argTypes :: [Type];
synthesized attribute inhSetMembers :: [String];
monoid attribute freeSkolemVars :: [TyVar] with [], setUnionTyVars;
monoid attribute freeFlexibleVars :: [TyVar] with [], setUnionTyVars;

-- Used by Expr, could possibly be replaced by pattern matching for decoratedType
-- Also used by 'new()'
synthesized attribute isDecorated :: Boolean;

-- Determines whether a type is an (undecorated) nonterminal type
-- Used in determining whether a type may be supplied with inherited attributes.
synthesized attribute isNonterminal :: Boolean;

-- Determines whether a type is a data nonterminal type
synthesized attribute isData :: Boolean;

-- Determines whether a type is tracked
synthesized attribute isTracked :: Boolean;

-- Used for type checking by 'terminal()'
synthesized attribute isTerminal :: Boolean;

-- Used by 'new' and type-determination for attributes (NOT on regular nonterminals)
synthesized attribute decoratedType :: Type;

-- Freshens a nonterminal PolyType into a decorated nonterminal Type
synthesized attribute asDecoratedType :: Type;

-- Used instead of unify() when we want to just know its decorated or undecorated
synthesized attribute unifyInstanceNonterminal :: Substitution;
synthesized attribute unifyInstanceDecorated :: Substitution;
synthesized attribute unifyInstanceDecorable :: Substitution;  -- non-data NT

attribute arity, isError, isDecorated, isNonterminal, isData, isTerminal, asDecoratedType, compareTo, isEqual occurs on PolyType;

aspect production monoType
top::PolyType ::= ty::Type
{
  top.arity = ty.arity;
  top.isError = ty.isError;
  top.isDecorated = ty.isDecorated;
  top.isNonterminal = ty.isNonterminal;
  top.isData = ty.isData;
  top.isTerminal = ty.isTerminal;
  top.asDecoratedType = ty.asDecoratedType;

  top.isEqual =
    top.compareTo.boundVars == [] &&
    top.compareTo.contexts == [] &&
    top.compareTo.typerep == ^ty;
}

aspect production polyType
top::PolyType ::= bound::[TyVar] ty::Type
{
  top.arity = ty.arity;
  top.isError = ty.isError;
  top.isDecorated = ty.isDecorated;
  top.isNonterminal = ty.isNonterminal;
  top.isData = ty.isData;
  top.isTerminal = ty.isTerminal;
  top.asDecoratedType = error("Only mono types should be possibly-decorated");

  local eqSub::Substitution =
    zipVarsIntoSubstitution(bound, top.compareTo.boundVars);
  top.isEqual =
    top.compareTo.contexts == [] &&
    top.compareTo.typerep == performRenaming(^ty, eqSub);
}

aspect production constraintType
top::PolyType ::= bound::[TyVar] contexts::[Context] ty::Type
{
  top.arity = ty.arity;
  top.isError = ty.isError;
  top.isDecorated = ty.isDecorated;
  top.isNonterminal = ty.isNonterminal;
  top.isData = ty.isData;
  top.isTerminal = ty.isTerminal;
  top.asDecoratedType = error("Only mono types should be possibly-decorated");

  local eqSub::Substitution =
    zipVarsIntoSubstitution(bound, top.compareTo.boundVars);
  top.isEqual =
    top.compareTo.contexts == map(performContextRenaming(_, eqSub), contexts) &&
    top.compareTo.typerep == performRenaming(^ty, eqSub);
}

attribute
  isError, inputTypes, outputType, namedTypes, arity, baseType, argTypes,
  isDecorated, isNonterminal, isData, isTracked, isTerminal, isApplicable,
  decoratedType, asDecoratedType, inhSetMembers, freeSkolemVars, freeFlexibleVars,
  unifyInstanceNonterminal, unifyInstanceDecorated, unifyInstanceDecorable
  occurs on Type;

propagate freeSkolemVars, freeFlexibleVars on Type;

aspect default production
top::Type ::=
{
  top.inputTypes = [];
  top.outputType = errorType();
  top.namedTypes = [];
  top.arity = 0;
  top.baseType = ^top;
  top.argTypes = [];
  top.inhSetMembers = [];
  
  top.isDecorated = false;
  top.isNonterminal = false;
  top.isData = false;
  top.isTracked = false;
  top.isTerminal = false;
  top.isError = false;
  top.isApplicable = false;
  
  top.decoratedType = errorType();
  top.asDecoratedType = errorType();
  
  top.unifyInstanceNonterminal = errorSubst("not nt");
  top.unifyInstanceDecorated = errorSubst("not dec");
  top.unifyInstanceDecorable = errorSubst("not dec");
}

aspect production varType
top::Type ::= tv::TyVar
{
  top.freeFlexibleVars <- [tv];
}

aspect production skolemType
top::Type ::= tv::TyVar
{
  top.freeSkolemVars <- [tv];

  -- Skolems with occurs-on contexts act like nonterminals, so use that behavior in unification
  top.asDecoratedType = decoratedType(^top, freshInhSet());
  top.unifyInstanceNonterminal = emptySubst();
  top.unifyInstanceDecorable = emptySubst();
}

aspect production appType
top::Type ::= c::Type a::Type
{
  top.baseType = c.baseType;
  top.argTypes = c.argTypes ++ [^a];
  top.isNonterminal = c.isNonterminal;
  top.isData = c.isData;
  top.isTracked = c.isTracked;
  top.asDecoratedType = decoratedType(^top, freshInhSet());  -- c.baseType should be a nonterminal or skolem
  top.unifyInstanceNonterminal = c.unifyInstanceNonterminal;
  top.unifyInstanceDecorable = c.unifyInstanceDecorable;
  top.arity = c.arity;
  top.isApplicable = c.isApplicable;
  
  top.inputTypes = take(top.arity, top.argTypes);
  top.outputType =
    case top.baseType of
    | functionType(_, _) -> last(top.argTypes)
    | _ -> errorType()
    end;
  top.namedTypes =
    case top.baseType of
    | functionType(_, nps) -> zip(nps, drop(top.arity, top.argTypes))
    | _ -> []
    end;
}


aspect production errorType
top::Type ::=
{
  top.isError = true;
}

aspect production intType
top::Type ::=
{
}

aspect production boolType
top::Type ::=
{
}

aspect production floatType
top::Type ::=
{
}

aspect production stringType
top::Type ::=
{
}

aspect production nonterminalType
top::Type ::= fn::String ks::[Kind] data::Boolean tracked::Boolean
{
  top.isNonterminal = true;
  top.isData = data;
  top.isTracked = tracked;
  top.asDecoratedType = if data then ^top else decoratedType(^top, freshInhSet());
  top.unifyInstanceNonterminal = emptySubst();
  top.unifyInstanceDecorable = if data then errorSubst("data") else emptySubst();
}

aspect production terminalType
top::Type ::= fn::String
{
  top.isTerminal = true;
}

aspect production inhSetType
top::Type ::= inhs::[String]
{
  top.inhSetMembers = inhs;
}

aspect production decoratedType
top::Type ::= te::Type i::Type
{
  top.isDecorated = true;
  top.decoratedType = ^te;
  top.inhSetMembers = i.inhSetMembers;
  top.unifyInstanceDecorated = emptySubst();
}

aspect production functionType
top::Type ::= params::Integer namedParams::[String]
{
  top.arity = params;
  top.isApplicable = true;
}

aspect production dispatchType
top::Type ::= ns::NamedSignature
{
  top.isApplicable = true;
  top.inputTypes = ns.inputTypes;
  top.outputType = ns.outputElement.typerep;
}

-- Strict type equality, assuming all type vars are skolemized
instance Eq Type {
  eq = \ t1::Type t2::Type -> !unifyDirectional(t1, t2).failure;
}

attribute compareTo, isEqual occurs on Context;
propagate compareTo, isEqual on Context;
