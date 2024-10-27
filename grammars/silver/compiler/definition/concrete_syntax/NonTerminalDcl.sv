grammar silver:compiler:definition:concrete_syntax;

import silver:compiler:driver only noOrigins, forceOrigins;

aspect production nonterminalDcl
top::AGDcl ::= quals::NTDeclQualifiers 'nonterminal' id::Name tl::BracketedOptTypeExprs nm::NonterminalModifiers ';'
{
  -- TODO: We are building this for every nonterminal declaration, when it should
  -- be the same for all nonterminals in the grammar
  local med :: ModuleExportedDefs =
    moduleExportedDefs(top.compiledGrammars, top.grammarDependencies, [top.grammarName], []);
  local syntax::Syntax = foldr(consSyntax, nilSyntax(), med.syntaxAst);
  
  local exportedLayoutTerms::[String] = syntax.allIgnoreTerminals;
  local exportedProds::[String] = syntax.allProductionNames;
  
  top.syntaxAst :=
    [ syntaxNonterminal(
        nonterminalType(fName, map((.kindrep), tl.types), quals.data, isThisTracked),
        nilSyntax(), exportedProds, exportedLayoutTerms,
        foldr(consNonterminalMod, nilNonterminalMod(), nm.nonterminalModifiers),
        location=getParsedOriginLocationOrFallback(top), sourceGrammar=top.grammarName)
    ];
}

monoid attribute nonterminalModifiers :: [SyntaxNonterminalModifier];
attribute nonterminalModifiers occurs on NonterminalModifiers, NonterminalModifierList, NonterminalModifier;
propagate nonterminalModifiers on NonterminalModifiers, NonterminalModifierList;
