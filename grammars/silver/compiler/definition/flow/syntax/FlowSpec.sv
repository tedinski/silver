grammar silver:compiler:definition:flow:syntax;

imports silver:compiler:definition:core;
imports silver:compiler:definition:flow:ast;
imports silver:compiler:definition:flow:env;
imports silver:compiler:definition:flow:driver only FlowType, inhDepsForSyn;
imports silver:compiler:definition:env;
imports silver:compiler:definition:type;
imports silver:compiler:driver:util only isExportedBy;
imports silver:util:treeset as set;

-- unfortunate...
import silver:compiler:analysis:warnings only warnAll;
import silver:compiler:analysis:warnings:flow only warnMissingInh;

terminal Flowtype 'flowtype' lexer classes {KEYWORD};

concrete production flowtypeDcl
top::AGDcl ::= 'flowtype' nt::QName '=' specs::FlowSpecs ';'
{
  top.unparse = "flowtype " ++ nt.unparse ++ " = " ++ specs.unparse ++ ";";
  propagate config, grammarName, compiledGrammars, env, flowEnv;

  top.errors :=
    if nt.lookupType.found
    then specs.errors
    else nt.lookupType.errors;
  top.specDefs :=
    if nt.lookupType.found
    then specs.specDefs
    else [];

  specs.onNt = nt.lookupType.typeScheme.typerep;
}

concrete production flowtypeAttrDcl
top::AGDcl ::= 'flowtype' attr::FlowSpec 'on' nts::NtList ';'
{
  top.unparse = "flowtype " ++ attr.unparse ++ " on " ++ nts.unparse ++ ";";
  propagate config, grammarName, compiledGrammars, env, flowEnv;

  top.errors := nts.errors;
  top.specDefs := nts.specDefs;
  
  nts.flowSpecSpec = ^attr;
}


tracked nonterminal FlowSpecs with config, grammarName, errors, env, unparse, onNt, specDefs, compiledGrammars, flowEnv;

propagate config, grammarName, errors, env, onNt, specDefs, compiledGrammars, flowEnv on FlowSpecs;

concrete production oneFlowSpec
top::FlowSpecs ::= h::FlowSpec
{
  top.unparse = h.unparse;
}
concrete production snocFlowSpec
top::FlowSpecs ::= h::FlowSpecs  ','  t::FlowSpec
{
  top.unparse = h.unparse ++ ", " ++ t.unparse;
}

tracked nonterminal FlowSpec with config, grammarName, errors, env, unparse, onNt, specDefs, compiledGrammars, flowEnv;

inherited attribute onNt :: Type;

propagate config, grammarName, errors, env, onNt, compiledGrammars, flowEnv on FlowSpec;

concrete production flowSpecDcl
top::FlowSpec ::= attr::FlowSpecId  '{' inhs::FlowSpecInhs '}'
{
  top.unparse = attr.unparse ++ " {" ++ inhs.unparse ++ "}";
  
  top.errors <-
    if !attr.found ||
       isExportedBy(top.grammarName, [attr.authorityGrammar], top.compiledGrammars)
    then []
    else [errFromOrigin(attr, "flow type for " ++ attr.name ++ " must be exported by " ++ attr.authorityGrammar)];

  top.errors <-
    if attr.found &&
       length(filter(eq(attr.synName, _), getSpecifiedSynsForNt(top.onNt.typeName, top.flowEnv))) > 1
    then [errFromOrigin(attr, "duplicate specification of flow type for " ++ attr.name ++ " on " ++ top.onNt.typeName)]
    else [];

  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local missingFt :: [String] =
    set:toList(set:removeAll(inhs.inhList, inhDepsForSyn("forward", top.onNt.typeName, myFlow)));

  top.errors <-
    if !attr.found ||
       !top.config.warnMissingInh || -- we don't want to compute flow graphs unless told to
       isExportedBy(attr.authorityGrammar, [hackGramFromFName(top.onNt.typeName)], top.compiledGrammars) ||
       null(missingFt)
    then []
    else [errFromOrigin(attr, attr.name ++ " is an extension synthesized attribute, and must contain at least the forward flow type. It is missing " ++ implode(", ", missingFt))];

  top.errors <-
    if attr.found && contains(attr.synName, inhs.refList)
    then [errFromOrigin(top, s"circularity in flow specification for ${attr.name} on ${top.onNt.typeName}")]
    else [];
  
  -- We want to put the spec in even if there are errors in 'inhs' so that
  -- we can look up specs from inhs.
  top.specDefs :=
    if !attr.found then []
    else [(top.onNt.typeName, attr.synName, if contains(attr.synName, inhs.refList) then [] else inhs.inhList, inhs.refList)];
}

tracked nonterminal FlowSpecId with config, grammarName, errors, env, unparse, onNt, synName, authorityGrammar, found, name;

synthesized attribute synName :: String;
synthesized attribute authorityGrammar :: String;

propagate config, grammarName, errors, env, compiledGrammars, flowEnv on FlowSpecId;

concrete production qnameSpecId
top::FlowSpecId ::= syn::QNameAttrOccur
{
  top.name = syn.name;
  top.unparse = syn.unparse;
  top.synName = syn.attrDcl.fullName;
  top.authorityGrammar = syn.dcl.sourceGrammar;
  top.found = syn.found && syn.attrDcl.isSynthesized;
  
  syn.attrFor = top.onNt;
  
  top.errors <-
    if !syn.found || syn.attrDcl.isSynthesized then []
    else [errFromOrigin(syn, syn.name ++ " is not a synthesized attribute, and so cannot have a flow type")];
}

concrete production forwardSpecId
top::FlowSpecId ::= 'forward'
{
  top.name = "forward";
  top.unparse = top.name;
  top.synName = "forward";
  top.authorityGrammar = hackGramFromFName(top.onNt.typeName);
  top.found = true;
}

concrete production decorateSpecId
top::FlowSpecId ::= 'decorate'
{
  top.name = "decorate";
  top.unparse = top.name;
  top.synName = "decorate";
  top.authorityGrammar = hackGramFromFName(top.onNt.typeName);
  top.found = true;
}


tracked nonterminal FlowSpecInhs with config, grammarName, errors, env, unparse, onNt, inhList, refList, flowEnv;

monoid attribute inhList :: [String];  -- The attributes in the flow specification
monoid attribute refList :: [String];  -- Flow specifications referenced in this one (currently can only contain "decorate" / "forward")

propagate config, grammarName, errors, env, onNt, inhList, refList, flowEnv on FlowSpecInhs;

concrete production nilFlowSpecInhs
top::FlowSpecInhs ::=
{
  top.unparse = "";
}
concrete production oneFlowSpecInhs
top::FlowSpecInhs ::= h::FlowSpecInh
{
  top.unparse = h.unparse;
}
concrete production consFlowSpecInhs
top::FlowSpecInhs ::= h::FlowSpecInh  ','  t::FlowSpecInhs
{
  top.unparse = h.unparse ++ ", " ++ t.unparse;
}

tracked nonterminal FlowSpecInh with config, grammarName, errors, env, unparse, onNt, inhList, refList, flowEnv;

flowtype FlowSpecInh = forward {grammarName, env, flowEnv}, decorate {forward, onNt}, inhList {decorate}, errors {decorate};

propagate config, grammarName, errors, env, flowEnv on FlowSpecInh;

concrete production flowSpecInh
top::FlowSpecInh ::= inh::QNameAttrOccur
{
  top.unparse = inh.unparse;
  top.inhList := if inh.attrFound then [inh.attrDcl.fullName] else [];
  top.refList := [];
  
  inh.attrFor = top.onNt;

  top.errors <-
    if !inh.found || inh.attrDcl.isInherited then []
    else [errFromOrigin(inh, inh.name ++ " is not an inherited attribute and so cannot be within a flow type")];
}

concrete production flowSpecTrans
top::FlowSpecInh ::= transSyn::QNameAttrOccur '.' inh::FlowSpecInh
{
  top.unparse = s"${transSyn.unparse}.${inh.unparse}";
  top.inhList :=
    if transSyn.attrFound
    then map(\ i -> s"${transSyn.attrDcl.fullName}.${i}", filter(notTransAttr, inh.inhList))
    else [];
  top.refList := [];  -- TODO: Technically, we could have cycles involving translation attr flow specs

  transSyn.attrFor = top.onNt;
  inh.onNt = transSyn.typerep;

  top.errors <-
    if !transSyn.found || transSyn.attrDcl.isSynthesized && transSyn.attrDcl.isTranslation then []
    else [errFromOrigin(transSyn, transSyn.name ++ " is not a translation attribute and so cannot be within a flow type")];
  top.errors <-
    if all(map(notTransAttr, inh.inhList)) then []
    else [errFromOrigin(inh, "Chained translation attributes are not currently supported in flow types")];
}

fun notTransAttr Boolean ::= a::String = indexOf(".", a) == -1;

{--
 - Inherit a flow spec from another flow spec.
 -
 - 1. This is exclusively for other things given explicit specifications:
 -    (a) by design: we want things documented in the code.
 -    (b) because it dramatically simplifies the implementation.
 -        We can do everything here, and not have to worry about having
 -        to somehow make this work in the inference process. (Which would
 -        be kinda tricky: probably we'd need to remove this attribute
 -        from the normal 'infer' process EXCEPT on the phantom production,
 -        where we'd stash the info given here as edges...)
 - 2. We only support 'decorate' and 'forward' here, not syns.
 -    It's the only version demanded so far, let's wait until there's
 -    motivation to consider that extension.
 -}
concrete production flowSpecDec
top::FlowSpecInh ::= 'decorate'
{
  top.unparse = "decorate";
  
  local specs :: [(String, [String], [String])] = getFlowTypeSpecFor(top.onNt.typeName, top.flowEnv);
  local decSpec :: Maybe<([String], [String])> = lookup("decorate", specs);
  
  -- This error message also shows up for Decorated Foo when Foo lacks a spec for 'decorate',
  -- so be sufficiently general here.
  top.errors <-
    case top.onNt, decSpec of
    | nonterminalType(_, _, _, _), just(_) -> []
    | nonterminalType(_, _, _, _), nothing() -> 
      [errFromOrigin(top, s"to use the default reference set for nonterminal ${top.onNt.typeName}, 'decorate' must also have an explicit flow type")]
    | errorType(), _ -> []
    | _, _ -> [errFromOrigin(top, s"default reference set can only be used with nonterminal types, not ${prettyType(top.onNt)}")]
    end;
  
  top.inhList := fromMaybe(([], []), decSpec).fst;
  top.refList := "decorate" :: fromMaybe(([], []), decSpec).snd;
}

concrete production flowSpecForward
top::FlowSpecInh ::= 'forward'
{
  top.unparse = "forward";
  
  local specs :: [(String, [String], [String])] = getFlowTypeSpecFor(top.onNt.typeName, top.flowEnv);
  local forwardSpec :: Maybe<([String], [String])> = lookup("forward", specs);
  
  top.errors <-
    case forwardSpec of
    | just(_) -> []
    | nothing() -> 
      [errFromOrigin(top, s"to use the forward set for nonterminal ${top.onNt.typeName} in a flow type, 'forward' must also have an explicit flow type")]
    end;
  
  top.inhList := fromMaybe(([], []), forwardSpec).fst;
  top.refList := "forward" :: fromMaybe(([], []), forwardSpec).snd;
}


tracked nonterminal NtList with config, grammarName, errors, env, unparse, flowSpecSpec, specDefs, compiledGrammars, flowEnv;

propagate config, grammarName, errors, env, flowSpecSpec, specDefs, compiledGrammars, flowEnv on NtList;

concrete production nilNtList
top::NtList ::=
{
  top.unparse = "";
}
concrete production oneNtList
top::NtList ::= h::NtName
{
  top.unparse = h.unparse;
}
concrete production consNtList
top::NtList ::= h::NtName  ','  t::NtList
{
  top.unparse = h.unparse ++ ", " ++ t.unparse;
}

tracked nonterminal NtName with config, grammarName, errors, env, unparse, flowSpecSpec, specDefs, compiledGrammars, flowEnv;

propagate config, grammarName, env, compiledGrammars, flowEnv on NtName;

inherited attribute flowSpecSpec :: FlowSpec;

concrete production ntName
top::NtName ::= nt::QName
{
  top.unparse = nt.unparse;
  top.errors :=
    if nt.lookupType.found
    then myCopy.errors
    else nt.lookupType.errors;
  
  top.specDefs :=
    if nt.lookupType.found
    then myCopy.specDefs
    else [];
  
  local myCopy :: FlowSpec = top.flowSpecSpec;
  myCopy.config = top.config;
  myCopy.grammarName = top.grammarName;
  myCopy.env = top.env;
  myCopy.compiledGrammars = top.compiledGrammars;
  myCopy.flowEnv = top.flowEnv;
  
  myCopy.onNt = nt.lookupType.typeScheme.typerep;
}

