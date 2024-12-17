grammar silver:compiler:analysis:typechecking:core;

aspect production defaultAttributionDcl
top::AGDcl ::= at::QName attl::BracketedOptTypeExprs nt::QName nttl::BracketedOptTypeExprs
{
  local checkNT::TypeCheck = checkNonterminal(top.env, false, protoatty);
  checkNT.downSubst = emptySubst();
  checkNT.finalSubst = emptySubst();
  
  top.errors <-
    if at.lookupAttribute.found && at.lookupAttribute.dcl.isTranslation && checkNT.typeerror
    then [errFromOrigin(top, s"Occurrence of translation attribute ${at.lookupAttribute.fullName} must have a nonterminal type.  Instead it is of type " ++ checkNT.leftpp)]
    else [];
  
  local transTargets :: [String] = getTranslationAttrTargets([], protoatty, top.env);
  top.errors <-
    if nt.lookupType.found && at.lookupAttribute.found && at.lookupAttribute.dcl.isTranslation && !checkNT.typeerror
    && contains(nt.lookupType.fullName, transTargets)
    then [errFromOrigin(top, s"Cycle in translation attributes! ${at.lookupAttribute.fullName} translates ${nt.lookupType.fullName} to ${protoatty.typeName}, but this nonterminal has translation attributes to ${implode(", ", transTargets)}.")]
    else [];
}
