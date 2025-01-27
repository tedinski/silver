grammar silver:compiler:extension:templating;

imports silver:compiler:definition:core;
imports silver:compiler:definition:env;
imports silver:compiler:definition:type;
imports silver:compiler:definition:type:syntax;
imports silver:compiler:metatranslation;
imports silver:reflect;
imports silver:langutil:pp;
imports silver:langutil:lsp as lsp;

imports silver:compiler:translation:java:core;

exports silver:compiler:extension:templating:syntax;

import silver:util:treeset as ts;

terminal Template_kwd   's"""' lexer classes {LITERAL, lsp:String_};
terminal SLTemplate_kwd 's"'   lexer classes {LITERAL, lsp:String_};

concrete production templateExpr
top::Expr ::= Template_kwd t::TemplateString
layout {}
{
  forwards to foldr1(stringAppendCall(_, _), t.stringTemplate);
}

concrete production singleLineTemplateExpr
top::Expr ::= SLTemplate_kwd t::SingleLineTemplateString
layout {}
{
  forwards to foldr1(stringAppendCall(_, _), t.stringTemplate);
}

production stringAppendCall
top::Expr ::= a::Expr b::Expr
{
  top.unparse = s"${a.unparse} ++ ${b.unparse}";

  -- TODO: We really need strictness analysis in Silver.
  -- Otherwise the translation for a large string template block contains
  -- new common.Thunk<Object>(new common.Thunk.Evaluable() { public final Object eval() { return ((common.StringCatter)silver.core.PstringAppend.invoke(${a.translation}, ${b.translation}); } })
  -- a ridiculous number of times, when it can just be translated as:
  top.translation = s"new common.StringCatter(${a.translation}, ${b.translation})";
  top.lazyTranslation = wrapThunk(top.translation, top.frame.lazyApplication);

  forwards to application(
    baseExpr(
      qName("silver:core:stringAppend")), '(',
    snocAppExprs(
      snocAppExprs(
        emptyAppExprs(), ',',
        presentAppExpr(@a)), ',',
      presentAppExpr(@b)),
    ',',
    emptyAnnoAppExprs(),
    ')');
}

terminal PPTemplate_kwd   'pp"""' lexer classes {LITERAL, lsp:String_};
terminal SLPPTemplate_kwd 'pp"'   lexer classes {LITERAL, lsp:String_};

-- These are translated by building a Document value and meta-translating the whole thing into an Expr
concrete production pptemplateExpr
top::Expr ::= PPTemplate_kwd t::TemplateString
layout {}
{
  forwards to translate(reflect(t.ppTemplate));
}

concrete production singleLinepptemplateExpr
top::Expr ::= SLPPTemplate_kwd t::SingleLineTemplateString
layout {}
{
  forwards to translate(reflect(t.ppTemplate));
}

-- Antiquote production used in translating nonwater Exprs that should get directly embedded in the result.
-- See fig 9 of https://doi.org/10.1016/j.cola.2021.101033 (https://www-users.cse.umn.edu/~evw/pubs/kramer21cola/kramer21cola.pdf)
production antiquoteDoc
top::Document ::= e::Expr
{ forwards to error("No forward"); }

aspect production nonterminalAST
top::AST ::= _ _ _
{
  directAntiquoteProductions <- ["silver:compiler:extension:templating:antiquoteDoc"];
}

synthesized attribute stringTemplate :: [Expr] occurs on TemplateString, SingleLineTemplateString,
                                                         TemplateStringBody, SingleLineTemplateStringBody,
                                                         TemplateStringBodyItem, SingleLineTemplateStringBodyItem, NonWater;
synthesized attribute ppTemplate :: Document occurs on TemplateString, SingleLineTemplateString,
                                                       TemplateStringBody, SingleLineTemplateStringBody,
                                                       TemplateStringBodyItem, SingleLineTemplateStringBodyItem, NonWater;

aspect production templateString
top::TemplateString ::= b::TemplateStringBody _
{
  top.stringTemplate = b.stringTemplate;
  top.ppTemplate = b.ppTemplate;
}

aspect production templateStringEmpty
top::TemplateString ::= _
{
  top.stringTemplate = [Silver_Expr { "" }];
  top.ppTemplate = notext();
}

aspect production singleLineTemplateString
top::SingleLineTemplateString ::= b::SingleLineTemplateStringBody _
{
  top.stringTemplate = b.stringTemplate;
  top.ppTemplate = b.ppTemplate;
}

aspect production singleLineTemplateStringEmpty
top::SingleLineTemplateString ::= _
{
  top.stringTemplate = [Silver_Expr { "" }];
  top.ppTemplate = notext();
}

aspect production bodyCons
top::TemplateStringBody ::= h::TemplateStringBodyItem  t::TemplateStringBody
{
  top.stringTemplate = h.stringTemplate ++ t.stringTemplate;
  top.ppTemplate = cat(h.ppTemplate, t.ppTemplate);
}

aspect production bodyOne
top::TemplateStringBody ::= h::TemplateStringBodyItem
{
  top.stringTemplate = h.stringTemplate;
  top.ppTemplate = h.ppTemplate;
}

aspect production bodyOneWater
top::TemplateStringBody ::= w::Water
{
  top.stringTemplate = [stringConst(terminal(String_t, "\"" ++ w.waterString ++ "\""))];
  top.ppTemplate = w.waterDoc;
}

aspect production singleLineBodyCons
top::SingleLineTemplateStringBody ::= h::SingleLineTemplateStringBodyItem  t::SingleLineTemplateStringBody
{
  top.stringTemplate = h.stringTemplate ++ t.stringTemplate;
  top.ppTemplate = cat(h.ppTemplate, t.ppTemplate);
}

aspect production singleLineBodyOne
top::SingleLineTemplateStringBody ::= h::SingleLineTemplateStringBodyItem
{
  top.stringTemplate = h.stringTemplate;
  top.ppTemplate = h.ppTemplate;
}

aspect production singleLineBodyOneWater
top::SingleLineTemplateStringBody ::= w::SingleLineWater
{
  top.stringTemplate = [stringConst(terminal(String_t, "\"" ++ w.waterString ++ "\""))];
  top.ppTemplate = w.waterDoc;
}

aspect production itemWaterEscape
top::TemplateStringBodyItem ::= w::Water nw::NonWater
{
  top.stringTemplate = [
    stringConst(terminal(String_t, "\"" ++ w.waterString ++ "\""))] ++
      nw.stringTemplate;
  top.ppTemplate = cat(w.waterDoc, nw.ppTemplate);
}

aspect production itemEscape
top::TemplateStringBodyItem ::= nw::NonWater
{
  top.stringTemplate = nw.stringTemplate;
  top.ppTemplate = nw.ppTemplate;
}

aspect production singleLineItemWaterEscape
top::SingleLineTemplateStringBodyItem ::= w::SingleLineWater nw::NonWater
{
  top.stringTemplate = [
    stringConst(terminal(String_t, "\"" ++ w.waterString ++ "\""))] ++
      nw.stringTemplate;
  top.ppTemplate = cat(w.waterDoc, nw.ppTemplate);
}

aspect production singleLineItemEscape
top::SingleLineTemplateStringBodyItem ::= nw::NonWater
{
  top.stringTemplate = nw.stringTemplate;
  top.ppTemplate = nw.ppTemplate;
}

aspect production nonwater
top::NonWater ::= '${' e::Expr '}'
{
  top.stringTemplate = [^e];
  top.ppTemplate = antiquoteDoc(mkStrFunctionInvocation("silver:langutil:pp:pp", [^e]));
}
