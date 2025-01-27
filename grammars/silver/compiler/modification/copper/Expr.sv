grammar silver:compiler:modification:copper;

import silver:util:treeset as ts;

terminal DisambiguationFailure_t 'disambiguationFailure' lexer classes {KEYWORD, RESERVED};

-- TODO: This can be a foreign function, no need to have it as syntax.
concrete production failureTerminalIdExpr
top::Expr ::= 'disambiguationFailure'
{
  top.unparse = "disambiguationFailure";
  propagate freeVars;
  top.errors := [];
  top.typerep = terminalIdType();

  top.translation = "(-1)";
  top.lazyTranslation = top.translation;

  propagate upSubst, upSubst2;
}

abstract production actionChildReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars := ts:fromList([q.name]);

  top.errors := []; -- Should only ever be in scope when valid

  top.typerep = q.lookupValue.typeScheme.monoType;

  top.translation = "((" ++ top.typerep.transType ++ ")((common.Node)RESULTfinal).getChild(" ++ top.frame.className ++ ".i_" ++ q.lookupValue.fullName ++ "))";
  top.lazyTranslation = top.translation; -- never, but okay!

  propagate upSubst, upSubst2;
}

abstract production pluckTerminalReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars := ts:fromList([q.name]);

  top.errors := []; -- Should only be referenceable from a context where its valid.

  -- TODO: It would be nice to have a more specific type here, see comment below.
  top.typerep = terminalIdType();
  
  top.translation = makeCopperName(q.lookupValue.fullName); -- Value right here?
  top.lazyTranslation = top.translation; -- never, but okay!
  
  propagate upSubst, upSubst2;
}

-- TODO: Distinct from pluckTerminalReference (since this can occur in any action block and
-- reference any terminal), but maybe it shouldn't be?  These productions do almost the same
-- thing.  Also having type classes would let us use a more specific type than generic TerminalId,
-- and pluckTerminalReference wouldn't need to cheat with a fresh type.
abstract production terminalIdReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars := ts:fromList([q.name]);

  top.errors := if !top.frame.permitActions
                then [errFromOrigin(top,  "References to terminal identifiers can only be made in action blocks")]
                else [];

  top.typerep = terminalIdType();

  top.translation = s"Terminals.${makeCopperName(q.lookupValue.fullName)}.num()";
  top.lazyTranslation = top.translation; -- never, but okay!

  propagate upSubst, upSubst2;
}

abstract production lexerClassReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars := ts:fromList([q.name]);

  top.errors := if !top.frame.permitActions
                then [errFromOrigin(top,  "References to lexer class members can only be made in action blocks")]
                else [];

  -- TODO: This should be a more specific type with type classes
  top.typerep = listType(terminalIdType());
  
  top.translation = makeCopperName(q.lookupValue.fullName);
  top.lazyTranslation = top.translation; -- never, but okay!
  
  propagate upSubst, upSubst2;
}

abstract production parserAttributeReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars := ts:fromList([q.name]);

  top.errors := if !top.frame.permitActions
                then [errFromOrigin(top,  "References to parser attributes can only be made in action blocks")]
                else [];

  top.typerep = q.lookupValue.typeScheme.monoType;

  top.translation =
    s"""(${makeCopperName(q.lookupValue.fullName)} == null? (${top.typerep.transType})common.Util.error("Uninitialized parser attribute ${q.name}") : ${makeCopperName(q.lookupValue.fullName)})""";
  top.lazyTranslation = top.translation; -- never, but okay!

  propagate upSubst, upSubst2;
}

abstract production termAttrValueReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars := ts:fromList([q.name]);

  top.errors := []; -- Should only ever be in scope in action blocks

  top.typerep = q.lookupValue.typeScheme.monoType;

  -- Yeah, it's a big if/then/else block, but these are all very similar and related.
  top.translation =
    if q.name == "lexeme" then "new common.StringCatter(lexeme)" else
    if q.name == "shiftable" then "shiftableList" else
    if q.name == "line" then "virtualLocation.getLine()" else
    if q.name == "column" then "virtualLocation.getColumn()" else
    if q.name == "filename" then "new common.StringCatter(virtualLocation.getFileName())" else
    error("unknown actionTerminalReference " ++ q.name); -- should never be called, but here for safety
  top.lazyTranslation = top.translation; -- never, but okay!

  propagate upSubst, upSubst2;
}
