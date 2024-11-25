grammar silver:compiler:extension:autoattr;

concrete production functorTransAttributeDcl
top::AGDcl ::= 'functor' 'translation' 'attribute' a::Name ';'
{
  top.unparse = "functor translation attribute " ++ a.unparse ++ ";";
  top.moduleNames := [];

  production attribute fName :: String;
  fName = top.grammarName ++ ":" ++ a.name;
  
  top.errors <-
    if length(getAttrDclAll(fName, top.env)) > 1
    then [errFromOrigin(a, "Attribute '" ++ fName ++ "' is already bound.")]
    else [];
  
  forwards to
    defsAGDcl(
      [attrDef(defaultEnvItem(functorTransDcl(fName, sourceGrammar=top.grammarName, sourceLocation=a.nameLoc)))]);
}

{--
 - Propagate a functor translation attribute on the enclosing production
 - @param attr  The name of the attribute to propagate
 -}
abstract production propagateFunctorTrans implements Propagate
top::ProductionStmt ::= includeShared::Boolean @attr::QName
{
  top.unparse = s"propagate ${if includeShared then "@" else ""}{attr.unparse};";
  
  -- No explicit errors, for now.  The only conceivable issue is the attribute not
  -- occuring on the LHS but this should be caught by the forward errors.  
  
  -- Generate the arguments for the constructor
  local inputs :: [Expr] = 
    map(makeSharedArg(top.env, attr, _), top.frame.signature.inputElements);
  local annotations :: [Pair<String Expr>] = 
    map(
      makeAnnoArg(top.frame.signature.outputElement.elementName, _),
      top.frame.signature.namedInputElements);

  -- Construct an attribute def and call with the generated arguments
  forwards to
    attributeDef(
      concreteDefLHS(qName(top.frame.signature.outputElement.elementName)),
      '.',
      qNameAttrOccur(^attr),
      '=',
      mkFullFunctionInvocation(baseExpr(qName(top.frame.fullName)), inputs, annotations),
      ';');
}

{--
 - Generates the expression we should use for an argument
 - @param env      The environment
 - @param attrName The name of the attribute being propagated
 - @param input    The NamedSignatureElement being propagated
 - @return Either this the child, or accessing `attrName` on the child
 -}
function makeSharedArg
Expr ::= env::Env attrName::Decorated QName input::NamedSignatureElement
{
  -- Check if the attribute occurs on the first child
  local attrOccursOnHead :: Boolean =
    !null(getOccursDcl(attrName.lookupAttribute.dcl.fullName, input.typerep.typeName, env));
  local inputDecorable :: Boolean = isDecorable(input.typerep, env);
  local validTypeHead :: Boolean = inputDecorable || input.typerep.isNonterminal;
  
  return
    if validTypeHead && attrOccursOnHead
    then Silver_Expr { @$name{input.elementName}.$QName{^attrName} }
    else if inputDecorable
    then Silver_Expr { silver:core:new($name{input.elementName}) }
    else Silver_Expr { $name{input.elementName} };
}
