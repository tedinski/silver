grammar silver:compiler:extension:autoattr;

concrete production equalityAttributeDcl
top::AGDcl ::= 'equality' 'attribute' syn::Name 'with' inh::QName ';'
{
  top.unparse = s"equality attribute ${syn.unparse} with ${inh.unparse};";
  top.moduleNames := [];

  propagate env;

  production attribute inhFName :: String;
  inhFName = inh.lookupAttribute.fullName;
  production attribute synFName :: String;
  synFName = top.grammarName ++ ":" ++ syn.name;
  
  top.errors <-
    if length(getAttrDclAll(synFName, top.env)) > 1
    then [errFromOrigin(syn, "Attribute '" ++ synFName ++ "' is already bound.")]
    else [];
  
  forwards to
    defsAGDcl(
      [attrDef(defaultEnvItem(equalityDcl(inhFName, synFName, sourceGrammar=top.grammarName, sourceLocation=syn.nameLoc)))]);
}

{--
 - Propagate a equality synthesized attribute on the enclosing production
 - @param attr  The name of the attribute to propagate
 -}
abstract production propagateEquality implements Propagate
top::ProductionStmt ::= includeShared::Boolean @syn::QName inh::String
{
  top.unparse = s"propagate ${if includeShared then "@" else ""}${syn.unparse};";
  
  forwards to
    Silver_ProductionStmt {
      $name{top.frame.signature.outputElement.elementName}.$QName{^syn} =
        case $name{top.frame.signature.outputElement.elementName}.$name{inh} of
        | $Pattern{
            prodAppPattern(
              qName(top.frame.signature.fullName),
              '(',
              foldr(
                patternList_more(_, ',', _),
                patternList_nil(),
                map(
                  \ ie::NamedSignatureElement -> Silver_Pattern { $name{ie.elementName ++ "2"} },
                  top.frame.signature.inputElements)),
              ')')} ->
          $Expr{
            foldr(
              -- and(_, '&&', _), -- luke removal, replace with `_ && _` when jars build
              \e1::Expr e2::Expr -> Silver_Expr { silver:core:conj(e1, e2) }, -- luke addition for build
              trueConst('true'),
              map(
                \ ie::NamedSignatureElement ->
                  if !null(getOccursDcl(syn.lookupAttribute.dcl.fullName, ie.typerep.typeName, top.env))
                  then Silver_Expr { $name{ie.elementName}.$QName{^syn} }
                  else if isDecorable(ie.typerep, top.env)
                  then Silver_Expr {
                    silver:core:eq(silver:core:new($name{ie.elementName}), silver:core:new($name{ie.elementName ++ "2"}))
                  }
                  else Silver_Expr {
                    silver:core:eq($name{ie.elementName}, $name{ie.elementName ++ "2"})
                  },
                top.frame.signature.inputElements))}
        | _ -> false
        end;
    };
}
