grammar silver:compiler:definition:core;

import silver:compiler:driver;

inherited attribute nonterminalName :: String;

concrete production nonterminalDcl
top::AGDcl ::= quals::NTDeclQualifiers 'nonterminal' id::Name tl::BracketedOptTypeExprs nm::NonterminalModifiers ';'
{
  top.unparse = "nonterminal " ++ id.unparse ++ tl.unparse ++ " " ++ nm.unparse ++ ";";

  production fName :: String = top.grammarName ++ ":" ++ id.name;
  nm.nonterminalName = fName;

  production isThisTracked::Boolean =
    (top.config.forceOrigins || ((!top.config.noOrigins) && quals.tracked)) &&
    !contains(fName, getSpecialCaseNoOrigins());
  
  -- tl.freeVariables is our order list of the bound types for this nonterminal.
  top.defs := [ntDef(top.grammarName,
                    id.nameLoc,
                    fName,
                    map((.kindrep), tl.types),
                    quals.data,
                    quals.closed,
                    isThisTracked)];
  -- TODO: It's probably reasonable to skip listing
  -- tl.freeVariables, and the Type. Assuming we have a proper ntDcl.
  -- And we should consider recording the exact concrete names used... might be nice documentation to use
  
  top.errors <- quals.errors;

  -- Here we ensure that the type list contains only type *variables*
  top.errors <- tl.errorsTyVars;
  
  -- Here we bind those type variables.
  tl.initialEnv = top.env;
  tl.env = tl.envBindingTyVars;

  nm.env = top.env;
  
  -- Redefinition check of the name
  top.errors <- 
    if length(getTypeDclAll(fName, top.env)) > 1 
    then [errFromOrigin(id, "Type '" ++ fName ++ "' is already bound.")]
    else [];

  top.errors <-
    if isLower(substring(0,1,id.name))
    then [errFromOrigin(id, "Types must be capitalized. Invalid nonterminal name " ++ id.name)]
    else [];
} action {
  insert semantic token IdTypeDcl_t at id.nameLoc;
}

tracked nonterminal NTDeclQualifiers with errors, data, closed, tracked;
propagate errors, data, closed, tracked on NTDeclQualifiers;

monoid attribute data :: Boolean with false, ||;
monoid attribute closed :: Boolean with false, ||;
monoid attribute tracked :: Boolean with false, ||;

concrete production nilNTQualifier
top::NTDeclQualifiers ::=
{
}

concrete production dataNTQualifier
top::NTDeclQualifiers ::= 'data' rest::NTDeclQualifiers
{
  top.data <- true;
  top.errors <- if rest.data then [errFromOrigin(top, "Duplicate 'data' qualifier")] else [];
}

concrete production closedNTQualifier
top::NTDeclQualifiers ::= 'closed' rest::NTDeclQualifiers
{
  top.closed <- true;
  top.errors <- if rest.closed then [errFromOrigin(top, "Duplicate 'closed' qualifier")] else [];
}

concrete production trackedNTQualifier
top::NTDeclQualifiers ::= 'tracked' rest::NTDeclQualifiers
{
  top.tracked <- true;
  top.errors <- if rest.tracked then [errFromOrigin(top, "Duplicate 'tracked' qualifier")] else [];
}

tracked nonterminal NonterminalModifiers with config, unparse, errors, env, nonterminalName; -- 0 or some
tracked nonterminal NonterminalModifierList with config, unparse, errors, env, nonterminalName; -- 1 or more
closed tracked nonterminal NonterminalModifier with config, unparse, errors, env, nonterminalName; -- 1

propagate config, errors, env, nonterminalName
  on NonterminalModifiers, NonterminalModifierList, NonterminalModifier;

concrete production nonterminalModifiersNone
top::NonterminalModifiers ::=
{
  top.unparse = "";
}
concrete production nonterminalModifierSome
top::NonterminalModifiers ::= nm::NonterminalModifierList
{
  top.unparse = nm.unparse;
}

concrete production nonterminalModifierSingle
top::NonterminalModifierList ::= nm::NonterminalModifier
{
  top.unparse = nm.unparse;
}
concrete production nonterminalModifiersCons
top::NonterminalModifierList ::= h::NonterminalModifier ',' t::NonterminalModifierList
{
  top.unparse = h.unparse ++ ", " ++ t.unparse;
}

-- These types will not have origins (will not be TrackedNodes) even if built with --force-origins
function getSpecialCaseNoOrigins
[String] ::=
{
  production attribute names::[String] with ++;
  names := [
    -- These are forced to be untracked to prevent circularity
    "silver:core:OriginInfo",
    "silver:core:OriginInfoType",
    "silver:core:OriginNote"
  ];
  return names;
}
