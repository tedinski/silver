grammar silver:compiler:extension:silverconstruction;

imports silver:reflect;
imports silver:compiler:metatranslation;

aspect production nonterminalAST
top::AST ::= prodName::String children::ASTs annotations::NamedASTs
{
  directAntiquoteProductions <-
    ["silver:compiler:extension:silverconstruction:antiquoteExpr",
     "silver:compiler:extension:silverconstruction:antiquoteExprInhs",
     "silver:compiler:extension:silverconstruction:antiquoteTypeExpr",
     "silver:compiler:extension:silverconstruction:antiquoteConstraintList",
     "silver:compiler:extension:silverconstruction:antiquotePattern",
     "silver:compiler:extension:silverconstruction:antiquoteFunctionSignature",
     "silver:compiler:extension:silverconstruction:antiquoteProductionRHS",
     "silver:compiler:extension:silverconstruction:antiquoteAspectRHS",
     "silver:compiler:extension:silverconstruction:antiquoteProductionStmt",
     "silver:compiler:extension:silverconstruction:antiquoteQName",
     "silver:compiler:extension:silverconstruction:antiquoteQNameAttrOccur",
     "silver:compiler:extension:silverconstruction:antiquoteName"];
  
  -- "Indirect" antiquote productions
  antiquoteTranslation <-
    case prodName, children of
    | "silver:compiler:extension:silverconstruction:antiquote_qName",
      consAST(_, consAST(_, consAST(a, consAST(_, nilAST())))) ->
        case reify(^a) of
        | right(e) ->
          just(
            mkFullFunctionInvocation(
              baseExpr(qName("silver:compiler:metatranslation:makeQName")),
              [e, translate(reflect(givenLocation))],
              []))
        | left(msg) -> error(s"Error in reifying child of production ${prodName}:\n${msg}")
        end
    | "silver:compiler:extension:silverconstruction:antiquote_qName", _ ->
        error(s"Unexpected antiquote production arguments: ${show(80, top.pp)}")
    | "silver:compiler:extension:silverconstruction:antiquote_name",
      consAST(_, consAST(_, consAST(a, consAST(_, nilAST())))) ->
        case reify(^a) of
        | right(e) ->
          just(
            mkFullFunctionInvocation(
              baseExpr(qName("silver:compiler:metatranslation:makeName")),
              [e, translate(reflect(givenLocation))],
              []))
        | left(msg) -> error(s"Error in reifying child of production ${prodName}:\n${msg}")
        end
    | "silver:compiler:extension:silverconstruction:antiquote_name", _ ->
        error(s"Unexpected antiquote production arguments: ${show(80, top.pp)}")
    | _, _ -> nothing()
    end;
}
