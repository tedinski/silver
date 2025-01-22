grammar silver:compiler:extension:autoattr;

concrete production biequalityAttributeDcl
top::AGDcl ::= 'biequality' 'attribute' synPartial::Name ',' syn::Name 'with' inh::QName ';'
{
  top.unparse = s"biequality attribute ${synPartial.unparse}, ${syn.unparse} with ${inh.unparse};";
  top.moduleNames := [];

  propagate grammarName, env, flowEnv;

  production attribute inhFName :: String;
  inhFName = inh.lookupAttribute.fullName;
  production attribute synPartialFName :: String;
  synPartialFName = top.grammarName ++ ":" ++ synPartial.name;
  production attribute synFName :: String;
  synFName = top.grammarName ++ ":" ++ syn.name;

  top.errors <-
    if length(getAttrDclAll(synPartialFName, top.env)) > 1
    then [errFromOrigin(syn, "Attribute '" ++ synPartialFName ++ "' is already bound.")]
    else [];
  top.errors <-
    if length(getAttrDclAll(synFName, top.env)) > 1
    then [errFromOrigin(syn, "Attribute '" ++ synFName ++ "' is already bound.")]
    else [];

  forwards to
    defsAGDcl(
      [attrDef(defaultEnvItem(biequalityPartialDcl(inhFName, synPartialFName, synFName, sourceGrammar=top.grammarName, sourceLocation=synPartial.nameLoc))),
       attrDef(defaultEnvItem(biequalityDcl(inhFName, synPartialFName, synFName, sourceGrammar=top.grammarName, sourceLocation=syn.nameLoc)))]);
}

abstract production propagateBiequalitySynPartial implements Propagate
top::ProductionStmt ::= includeShared::Boolean @synPartial::QName inh::String syn::String
{
  top.unparse = s"propagate ${synPartial.unparse};";
  
  forwards to
    Silver_ProductionStmt {
      $name{top.frame.signature.outputElement.elementName}.$QName{^synPartial} =
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
                  if !null(getOccursDcl(syn, ie.typerep.typeName, top.env))
                  then Silver_Expr { $name{ie.elementName}.$name{syn} }
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

abstract production propagateBiequalitySyn implements Propagate
top::ProductionStmt ::= includeShared::Boolean @syn::QName inh::String synPartial::String
{
  top.unparse = s"propagate ${syn.unparse};";
  
  forwards to
    Silver_ProductionStmt {
      $name{top.frame.signature.outputElement.elementName}.$QName{^syn} =
        $name{top.frame.signature.outputElement.elementName}.$qName{synPartial} ||
        $name{top.frame.signature.outputElement.elementName}.$qName{inh}.$qName{synPartial};
    };
}
