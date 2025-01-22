grammar silver:compiler:extension:opersection;

-- sectioned operator syntax



-- antiquoteAppExpr

{-concrete production antiquoteAppExpr
top::AppExpr ::= '$AppExpr' '{' e::Expr '}'
{
  top.unparse = s"$$AppExpr{${e.unparse}}";
  forwards to
    presentAppExpr(
      errorExpr(
        [errFromOrigin(top, "$AppExpr should not occur outside of quoted Silver literal")]));
}

aspect production nonterminalAST
top::AST ::= prodName::String children::ASTs annotations::NamedASTs
{
  directAntiquoteProductions <-
    ["silver:compiler:extension:silverconstruction:antiquoteAppExpr"];
}-}
