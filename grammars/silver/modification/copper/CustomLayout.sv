grammar silver:modification:copper;

-- It would be nice if this weren't a keyword, but...
terminal Layout_kwd 'layout' lexer classes {KEYWORD,RESERVED};

concrete production productionModifierLayout
top::ProductionModifier ::= 'layout' '{' terms::TermPrecList '}'
{
  top.unparse = "layout {" ++ terms.unparse ++ "}";

  top.productionModifiers = [prodLayout(terms.precTermList)];
  top.errors := terms.errors;
}

concrete production productionModifierLayoutNone
top::ProductionModifier ::= 'layout' '{' '}'
{
  top.unparse = "layout {}";

  top.productionModifiers = [prodLayout([])];
  top.errors := [];
}

concrete production nonterminalModifierLayout
top::NonterminalModifier ::= 'layout' '{' terms::TermPrecList '}'
{
  top.unparse = "layout {" ++ terms.unparse ++ "}";
  
  top.nonterminalModifiers = [ntLayout(terms.precTermList)];
  top.errors := terms.errors;
}

concrete production nonterminalModifierLayoutNone
top::NonterminalModifier ::= 'layout' '{' '}'
{
  top.unparse = "layout {}";
  
  top.nonterminalModifiers = [ntLayout([])];
  top.errors := [];
}

attribute customLayout occurs on ParserComponents, ParserComponent;

aspect production nilParserComponent
top::ParserComponents ::=
{
  top.customLayout = nothing();
}

aspect production consParserComponent
top::ParserComponents ::= c1::ParserComponent  c2::ParserComponents
{
  top.customLayout = orElse(c1.customLayout, c2.customLayout);
}

aspect default production
top::ParserComponent ::=
{
  top.customLayout = nothing();
}

concrete production parserComponentLayout
top::ParserComponent ::= 'layout' '{' terms::TermPrecList '}' ';'
{
  top.unparse = "layout {" ++ terms.unparse ++ "};";
  top.errors := terms.errors;
  top.customLayout = just(terms.precTermList);
}

concrete production parserComponentLayoutNone
top::ParserComponent ::= 'layout' '{' '}' ';'
{
  top.unparse = "layout {};";
  top.errors := [];
  top.customLayout = just([]);
}

