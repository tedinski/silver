grammar silver:compiler:modification:copper;

terminal Dominates_t 'dominates' lexer classes {MODIFIER};
terminal Submits_t   'submits'   lexer classes {MODIFIER};
terminal Classes_kwd 'classes'   lexer classes {MODIFIER};

monoid attribute lexerClasses :: [String];
attribute lexerClasses occurs on TerminalModifier, TerminalModifiers;
propagate lexerClasses on TerminalModifiers, TerminalModifier;

concrete production terminalModifierDominates
top::TerminalModifier ::= 'dominates' terms::TermPrecs
{
  top.unparse = "dominates { " ++ terms.unparse ++ " } ";
  propagate env, errors;

  top.terminalModifiers := [termDominates(terms.precTermList)];
}

concrete production terminalModifierSubmitsTo
top::TerminalModifier ::= 'submits' 'to' terms::TermPrecs
{
  top.unparse = "submits to { " ++ terms.unparse ++ " } " ;
  propagate env, errors;

  top.terminalModifiers := [termSubmits(terms.precTermList)];
}

concrete production terminalModifierClassSpec
top::TerminalModifier ::= 'lexer' 'classes' cl::LexerClasses
{
  top.unparse = "lexer classes { " ++ cl.unparse ++ " } " ;
  propagate env, errors;

  top.terminalModifiers := [termClasses(cl.lexerClasses)];
}

concrete production terminalModifierActionCode
top::TerminalModifier ::= 'action' acode::ActionCode_c
{
  top.unparse = "action " ++ acode.unparse;
  propagate config, grammarName, compiledGrammars, flowEnv, errors;

  top.terminalModifiers := [termAction(acode.actionCode)];

  -- oh no again!
  local myFlow :: EnvTree<FlowType> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).grammarFlowTypes;
  local myProds :: EnvTree<ProductionGraph> = head(searchEnvTree(top.grammarName, top.compiledGrammars)).productionFlowGraphs;

  local myFlowGraph :: ProductionGraph = 
    constructAnonymousGraph(acode.flowDefs, top.env, myProds, myFlow);

  acode.frame = actionContext(myFlowGraph, sourceGrammar=top.grammarName);
  acode.env = newScopeEnv(terminalActionVars ++ acode.defs, top.env);
}

monoid attribute precTermList :: [String];

tracked nonterminal TermPrecs with config, grammarName, unparse, precTermList, errors, env;
propagate config, grammarName, env, errors, precTermList on TermPrecs;

concrete production termPrecsOne
top::TermPrecs ::= t::QName
{
  forwards to termPrecs(termPrecList(@t,termPrecListNull()));
} action {
  insert semantic token IdType_t at t.nameLoc;
}

concrete production termPrecsList
top::TermPrecs ::= '{' terms::TermPrecList '}'
{
  forwards to termPrecs(@terms);
}

abstract production termPrecs
top::TermPrecs ::= terms::TermPrecList
{
  top.unparse = s"{${terms.unparse}}";
}

tracked nonterminal TermPrecList with config, grammarName, unparse, precTermList, errors, env;
propagate config, grammarName, env, errors, precTermList on TermPrecList;

abstract production termPrecList
top::TermPrecList ::= h::QName t::TermPrecList
{
  top.unparse = if t.unparse == ""
             then h.unparse
             else h.unparse ++ ", " ++ t.unparse;

  production fName::String = if null(h.lookupType.dcls) then h.lookupLexerClass.dcl.fullName else h.lookupType.dcl.fullName;

  top.precTermList <- if h.lookupType.found || h.lookupLexerClass.found then [fName] else [];
  
  -- Since we're looking it up in two ways, do the errors ourselves
  top.errors <- if null(h.lookupType.dcls) && null(h.lookupLexerClass.dcls)
                then [errFromOrigin(h, "Undeclared terminal or lexer class '" ++ h.name ++ "'.")]
                else if length(h.lookupType.dcls) + length(h.lookupLexerClass.dcls) > 1
                then [errFromOrigin(h, "Ambiguous reference to terminal or lexer class '" ++ h.name ++ "'. Possibilities are:\n" ++
                            printPossibilities(h.lookupType.dcls) ++ if !null(h.lookupLexerClass.dcls) then ", " ++ printPossibilities(h.lookupLexerClass.dcls) else "")]
                else [];
}

abstract production termPrecListNull
top::TermPrecList ::=
{
  top.unparse = "";
}

concrete production termPrecListOne
top::TermPrecList ::= t::QName
{
  forwards to termPrecList(@t, termPrecListNull());
} action {
  insert semantic token IdType_t at t.nameLoc;
}

concrete production termPrecListCons
top::TermPrecList ::= t::QName ',' terms_tail::TermPrecList
{
  forwards to termPrecList(@t, @terms_tail);
} action {
  insert semantic token IdType_t at t.nameLoc;
}

tracked nonterminal LexerClasses with config, unparse, lexerClasses, errors, env;
propagate config, env, errors, lexerClasses on LexerClasses;

concrete production lexerClassesOne
top::LexerClasses ::= n::QName
{
  forwards to lexerClasses(lexerClassListMain(@n, lexerClassListNull()));
} action {
  insert semantic token IdLexerClassDcl_t at n.nameLoc;
}

concrete production lexerClassesList
top::LexerClasses ::= '{' cls::LexerClassList '}'
{
   forwards to lexerClasses(@cls);
}

abstract production lexerClasses
top::LexerClasses ::= cls::LexerClassList
{
  top.unparse = s"{${cls.unparse}}";
}

tracked nonterminal LexerClassList with config, unparse, lexerClasses, errors, env;
propagate config, env, errors, lexerClasses on LexerClassList;

concrete production lexerClassListOne
top::LexerClassList ::= n::QName
{
  forwards to lexerClassListMain(@n,lexerClassListNull());
} action {
  insert semantic token IdLexerClassDcl_t at n.nameLoc;
}

concrete production lexerClassListCons
top::LexerClassList ::= n::QName ',' cl_tail::LexerClassList
{
  forwards to lexerClassListMain(@n,@cl_tail);
} action {
  insert semantic token IdLexerClassDcl_t at n.nameLoc;
}


abstract production lexerClassListMain
top::LexerClassList ::= n::QName t::LexerClassList
{
  top.unparse = if t.unparse == ""
          then n.unparse
          else n.unparse ++ ", " ++ t.unparse;

  top.errors <- n.lookupLexerClass.errors;

  top.lexerClasses <- if n.lookupLexerClass.found then [n.lookupLexerClass.dcl.fullName] else [];
}

abstract production lexerClassListNull
cl::LexerClassList ::=
{
  cl.unparse = "";
}

