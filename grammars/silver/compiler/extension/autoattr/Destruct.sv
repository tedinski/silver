grammar silver:compiler:extension:autoattr;

concrete production destructAttributeDcl
top::AGDcl ::= 'destruct' 'attribute' inh::Name 'with' i::TypeExpr ';'
{
  top.unparse = s"destruct attribute ${inh.unparse} with ${i.unparse};";
  top.moduleNames := [];

  production attribute inhFName :: String;
  inhFName = top.grammarName ++ ":" ++ inh.name;
  
  top.errors <-
    if length(getAttrDclAll(inhFName, top.env)) > 1
    then [err(inh.location, "Attribute '" ++ inhFName ++ "' is already bound.")]
    else [];
  top.errors <- i.errors;
  
  forwards to
    defsAGDcl(
      [attrDef(defaultEnvItem(destructDcl(inhFName, i.typerep.inhSetMembers, sourceGrammar=top.grammarName, sourceLocation=inh.location)))],
      location=top.location);
}

{--
 - Propagate a destruct inherited attribute on the enclosing production
 - @param attr  The name of the attribute to propagate
 -}
abstract production propagateDestruct
top::ProductionStmt ::= attr::Decorated QName
{
  top.unparse = s"propagate ${attr.unparse};";
  
  local numChildren::Integer = length(top.frame.signature.inputElements);
  forwards to
    foldr(
      productionStmtAppend(_, _, location=top.location),
      errorProductionStmt([], location=top.location), -- No emptyProductionStmt?
      map(
        \ ie::Pair<Integer NamedSignatureElement> ->
          Silver_ProductionStmt {
            $name{ie.snd.elementName}.$QName{new(attr)} =
              case $name{top.frame.signature.outputElement.elementName}.$QName{new(attr)} of
              | $Pattern{
                  prodAppPattern(
                    qName(top.location, top.frame.signature.fullName),
                    '(',
                    foldr(
                      patternList_more(_, ',', _, location=top.location),
                      patternList_nil(location=top.location),
                      repeat(wildcPattern('_', location=top.location), ie.fst) ++
                      Silver_Pattern { a } ::
                      repeat(wildcPattern('_', location=top.location), numChildren - (ie.fst + 1)) ),
                    ')',
                    location=top.location)} -> a
              | a ->
                error(
                  "Destruct attribute " ++ $Expr{stringConst(terminal(String_t, s"\"${attr.name}\"", top.location), location=top.location)} ++
                  " demanded on child " ++ $Expr{stringConst(terminal(String_t, s"\"${ie.snd.elementName}\"", top.location), location=top.location)} ++
                  " of production " ++ $Expr{stringConst(terminal(String_t, s"\"${top.frame.signature.fullName}\"", top.location), location=top.location)} ++
                  " when given value " ++ silver:core:hackUnparse(a) ++ " does not match.")
              end;
          },
        filter(
          \ ie::Pair<Integer NamedSignatureElement> ->
            !null(getOccursDcl(attr.lookupAttribute.dcl.fullName, ie.snd.typerep.typeName, top.env)),
          zipWith(pair, range(0, numChildren), top.frame.signature.inputElements))));
}

