grammar silver:compiler:definition:concrete_syntax;

import silver:langutil:pp;
import silver:regex as abs;
import silver:regex:concrete_syntax;

terminal Ignore_kwd      'ignore'      lexer classes {MODIFIER};
terminal Marking_kwd     'marking'     lexer classes {MODIFIER};
terminal Named_kwd       'named'       lexer classes {MODIFIER};
terminal Left_kwd        'left'        lexer classes {MODIFIER};
terminal Association_kwd 'association' lexer classes {MODIFIER};
terminal Right_kwd       'right'       lexer classes {MODIFIER};
terminal None_kwd        'none'        lexer classes {MODIFIER};
terminal RepeatProb_kwd  'repeatProb'  lexer classes {MODIFIER};  -- For use by the treegen extension

-- We actually need to reserved this due to its appearance in PRODUCTION modifiers.
terminal Precedence_kwd  'precedence'  lexer classes {MODIFIER,RESERVED};

abstract production terminalDclDefault
top::AGDcl ::= t::TerminalKeywordModifier id::Name r::RegExpr tm::TerminalModifiers
{
  top.unparse = t.unparse ++ "terminal " ++ id.unparse ++ " " ++ r.unparse ++ " " ++ tm.unparse ++ ";";

  production attribute fName :: String;
  fName = top.grammarName ++ ":" ++ id.name;

  top.defs := [termDef(top.grammarName, id.nameLoc, fName, r.terminalRegExprSpec, r.easyName, tm.genRepeatProb)];

  top.errors <-
    if length(getTypeDclAll(fName, top.env)) > 1
    then [errFromOrigin(id, "Type '" ++ fName ++ "' is already bound.")]
    else [];

  top.errors <-
    if isLower(substring(0,1,id.name))
    then [errFromOrigin(id, "Types must be capitalized. Invalid terminal name " ++ id.name)]
    else [];

  -- This is a crude check, but effective.
  top.errors <-
    if indexOf("\n", unescapeString(r.unparse)) != -1 && indexOf("\r", unescapeString(r.unparse)) == -1
    then [wrnFromOrigin(r, "Regex contains '\\n' but not '\\r'. This is your reminder about '\\r\\n' newlines.")]
    else [];

  propagate config, grammarName, compiledGrammars, env, errors;

  top.syntaxAst := [
    syntaxTerminal(fName, r.terminalRegExprSpec,
      foldr(consTerminalMod, nilTerminalMod(), t.terminalModifiers ++ tm.terminalModifiers),
      location=getParsedOriginLocationOrFallback(top), sourceGrammar=top.grammarName)];
}

concrete production terminalDclKwdModifiers
top::AGDcl ::= t::TerminalKeywordModifier 'terminal' id::Name r::RegExpr ';'
{
  forwards to terminalDclDefault(@t, @id, @r, terminalModifiersNone());
} action {
  insert semantic token IdTypeDcl_t at id.nameLoc;
}

concrete production terminalDclAllModifiers
top::AGDcl ::= t::TerminalKeywordModifier 'terminal' id::Name r::RegExpr tm::TerminalModifiers ';'
{
  forwards to terminalDclDefault(@t, @id, @r, @tm);
} action {
  insert semantic token IdTypeDcl_t at id.nameLoc;
}

{--
 - This exists as a catch-all for representing regular expressions for terminals.
 - There's only one option here, but it's an extension point.
 -}
tracked nonterminal RegExpr with config, grammarName, unparse, terminalRegExprSpec, easyName;

synthesized attribute terminalRegExprSpec :: abs:Regex;
synthesized attribute easyName :: Maybe<String>;

terminal RegexSlash_t '/' lexer classes {lsp:Regexp};

concrete production regExpr_c
top::RegExpr ::= '/' r::Regex '/'
layout {}
{
  top.unparse = "/" ++ r.unparse ++ "/";
  forwards to regExpr(r.ast);
}

abstract production regExpr
top::RegExpr ::= r::abs:Regex
{
  top.unparse = "/" ++ show(80, r.pp) ++ "/";
  top.terminalRegExprSpec = ^r;
  top.easyName = nothing();
}


closed tracked nonterminal TerminalKeywordModifier with unparse, terminalModifiers;

concrete production terminalKeywordModifierIgnore
top::TerminalKeywordModifier ::= 'ignore'
{
  top.unparse = "ignore ";

  top.terminalModifiers := [termIgnore()];
}

concrete production terminalKeywordModifierMarking
top::TerminalKeywordModifier ::= 'marking'
{
  top.unparse = "marking ";

  top.terminalModifiers := [termMarking()];
}

concrete production terminalKeywordModifierNone
top::TerminalKeywordModifier ::=
{
  top.unparse = "";

  top.terminalModifiers := [];
}


tracked nonterminal TerminalModifiers with config, unparse, terminalModifiers, genRepeatProb, errors, env, grammarName, compiledGrammars, flowEnv;
closed tracked nonterminal TerminalModifier with config, unparse, terminalModifiers, genRepeatProb, errors, env, grammarName, compiledGrammars, flowEnv;

monoid attribute terminalModifiers :: [SyntaxTerminalModifier];
monoid attribute genRepeatProb :: Maybe<Float> with nothing(), orElse;

propagate config, grammarName, compiledGrammars, flowEnv, terminalModifiers, genRepeatProb, errors, env
  on TerminalModifiers;

aspect default production
top::TerminalModifier ::=
{
  top.genRepeatProb := nothing();
}

abstract production terminalModifiersNone
top::TerminalModifiers ::=
{
  top.unparse = "";
}
concrete production terminalModifierSingle
top::TerminalModifiers ::= tm::TerminalModifier
{
  top.unparse = tm.unparse;
}
concrete production terminalModifiersCons
top::TerminalModifiers ::= h::TerminalModifier ',' t::TerminalModifiers
{
  top.unparse = h.unparse ++ ", " ++ t.unparse;
}

concrete production terminalModifierLeft
top::TerminalModifier ::= 'association' '=' 'left'
{
  top.unparse = "association = left";

  top.terminalModifiers := [termAssociation("left")];
  top.errors := [];
}
concrete production terminalModifierRight
top::TerminalModifier ::= 'association' '=' 'right'
{
  top.unparse = "association = right";

  top.terminalModifiers := [termAssociation("right")];
  top.errors := [];
}
concrete production terminalModifierNone
top::TerminalModifier ::= 'association' '=' 'none'
{
  top.unparse = "association = none";

  top.terminalModifiers := [termAssociation("none")];
  top.errors := [];
}

concrete production terminalModifierPrecedence
top::TerminalModifier ::= 'precedence' '=' i::Int_t
{
  top.unparse = "precedence = " ++ i.lexeme;

  top.terminalModifiers := [termPrecedence(toInteger(i.lexeme))];
  top.errors := [];
}

-- For use by the treegen extension.
-- Has to be in the "host language" since it goes in the regular env and not the CST AST.
concrete production terminalModifierRepeatProb
top::TerminalModifier ::= 'repeatProb' '=' f::Float_t
{
  top.unparse = "repeatProb = " ++ f.lexeme;

  top.terminalModifiers := [];
  top.genRepeatProb := just(toFloat(f.lexeme));
  top.errors :=
    if toFloat(f.lexeme) >= 1.0
    then [errFromOrigin(f, "Repeat probability must be < 1.0")]
    else [];
}

concrete production terminalModifierNamed
top::TerminalModifier ::= 'named' name::String_t
{
  top.unparse = "named " ++ name.lexeme;

  top.terminalModifiers := [termPrettyName(substring(1, length(name.lexeme) - 1, name.lexeme))];
  top.errors := [];
}
