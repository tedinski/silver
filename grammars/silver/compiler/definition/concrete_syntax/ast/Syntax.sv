grammar silver:compiler:definition:concrete_syntax:ast;

imports silver:compiler:translation:java:core only makeTerminalName;
import silver:compiler:definition:concrete_syntax:copper as copper;
import silver:util:treemap as tm;
import silver:util:treeset as s;

-- For looking syntax elements up by name.
monoid attribute cstDcls :: [Pair<String Decorated SyntaxDcl>];
inherited attribute cstEnv :: EnvTree<Decorated SyntaxDcl>;
monoid attribute cstErrors :: [String];

-- Transformation that moves productions underneath their respective nonterminals.
monoid attribute cstProds :: [Pair<String SyntaxDcl>];
inherited attribute cstNTProds :: EnvTree<SyntaxDcl>;
monoid attribute cstNormalize :: [SyntaxDcl];

-- Compute and allow lookup of all terminals in a lexer class
monoid attribute classTerminalContribs::[Pair<String String>];
inherited attribute classTerminals::EnvTree<String>;
monoid attribute superClassContribs::[Pair<String String>];
inherited attribute superClasses::EnvTree<String>;
inherited attribute subClasses::EnvTree<String>;

-- Parser attribute action code aspects
monoid attribute parserAttributeAspectContribs::[Pair<String String>];
inherited attribute parserAttributeAspects::EnvTree<String>;

-- TODO: Attributes that lift out various sorts of SyntaxDcls all extract references
-- of type Decorated SyntaxDcl.  The actual set of attributes needed for translation
-- varies between different SyntaxDcl productions, however the flow analysis forces
-- all these references to have the entire set of possible inh attributes.
-- We should perhaps consider factoring out different sorts of SyntaxDcls into seperate
-- nonterminals, e.g. SyntaxNonterminal, SyntaxProduction, etc. and collect references
-- to these various nonterminals with only the relevant attributes instead.
monoid attribute allTerminals :: [Decorated SyntaxDcl];
monoid attribute allIgnoreTerminals :: [String];
monoid attribute allMarkingTerminals :: [String];
monoid attribute allProductions :: [Decorated SyntaxDcl];
monoid attribute allProductionNames :: [String];  -- Doesn't depend on anything
monoid attribute allNonterminals :: [Decorated SyntaxDcl];
monoid attribute disambiguationClasses :: [Decorated SyntaxDcl];
synthesized attribute domContribs :: [Decorated SyntaxDcl];
synthesized attribute subContribs :: [Decorated SyntaxDcl];
monoid attribute memberTerminals :: [Decorated SyntaxDcl];
monoid attribute dominatingTerminalContribs :: [(String, Decorated SyntaxDcl)];
synthesized attribute terminalRegex::Regex;
inherited attribute containingGrammar :: String;
monoid attribute lexerClassRefDcls :: String;
synthesized attribute exportedProds :: [String];
synthesized attribute hasCustomLayout :: Boolean;
monoid attribute layoutContribs :: [Pair<String String>]; -- prod/nt name, prod/nt/term name
inherited attribute layoutTerms::EnvTree<String>;

inherited attribute prefixesForTerminals :: EnvTree<String>;
inherited attribute componentGrammarMarkingTerminals :: EnvTree<[String]>;

-- Creating unambiguous <PP>s; this is a multiset used to accumulate all the
-- names for terminals, and the actual name for <PP> will be modified to
-- disambiguate if it would be ambiguous.
monoid attribute prettyNamesAccum::[Pair<String String>];
inherited attribute prettyNames::tm:Map<String String>;

synthesized attribute copperElementReference::copper:ElementReference;
synthesized attribute copperGrammarElements::[copper:GrammarElement];

{--
 - An abstract syntax tree for representing concrete syntax.
 -}
nonterminal Syntax with
  compareTo, isEqual, cstDcls, cstEnv, cstErrors, cstProds, cstNTProds, cstNormalize,
  allTerminals, allIgnoreTerminals, allMarkingTerminals, allProductions, allProductionNames, allNonterminals,
  disambiguationClasses, memberTerminals, dominatingTerminalContribs, classTerminalContribs, classTerminals,
  superClassContribs, superClasses, subClasses, parserAttributeAspectContribs, parserAttributeAspects,
  lexerClassRefDcls, layoutContribs, layoutTerms, containingGrammar, prefixesForTerminals, componentGrammarMarkingTerminals,
  prettyNamesAccum, prettyNames, copperGrammarElements;

flowtype decorate {
  cstEnv, classTerminals, superClasses, subClasses, containingGrammar,
  layoutTerms, prefixesForTerminals, componentGrammarMarkingTerminals, parserAttributeAspects, prettyNames
} on Syntax, SyntaxDcl;

propagate
  compareTo, isEqual, cstDcls, cstEnv, cstErrors, cstProds, cstNTProds, cstNormalize,
  allTerminals, allIgnoreTerminals, allMarkingTerminals, allProductions, allProductionNames, allNonterminals,
  disambiguationClasses, memberTerminals, dominatingTerminalContribs, classTerminalContribs, classTerminals,
  superClassContribs, superClasses, subClasses, parserAttributeAspectContribs, parserAttributeAspects,
  lexerClassRefDcls, layoutContribs, layoutTerms, containingGrammar, prefixesForTerminals, componentGrammarMarkingTerminals,
  prettyNamesAccum, prettyNames
  on Syntax;

abstract production nilSyntax
top::Syntax ::=
{
  top.copperGrammarElements = [];
}

abstract production consSyntax
top::Syntax ::= s1::SyntaxDcl s2::Syntax
{
  top.copperGrammarElements = s1.copperGrammarElements ++ s2.copperGrammarElements;
}

{--
 - An individual declaration of a concrete syntax element.
 -}
closed nonterminal SyntaxDcl with location, sourceGrammar,
  compareTo, isEqual, cstDcls, cstEnv, cstErrors, cstProds, cstNTProds, cstNormalize,
  fullName, sortKey, allTerminals, allIgnoreTerminals, allMarkingTerminals, allProductions, allProductionNames, allNonterminals,
  disambiguationClasses, memberTerminals, dominatingTerminalContribs, classTerminalContribs, classTerminals,
  superClassContribs, superClasses, subClasses, parserAttributeAspectContribs, parserAttributeAspects,
  lexerClassRefDcls, exportedProds, hasCustomLayout, layoutContribs, layoutTerms,
  domContribs, subContribs, terminalRegex, prefixSeperator, containingGrammar, prefixesForTerminals, componentGrammarMarkingTerminals,
  prettyNamesAccum, prettyNames, copperElementReference, copperGrammarElements;

synthesized attribute sortKey :: String;

propagate
  compareTo, isEqual, cstEnv, cstErrors, cstNTProds, containingGrammar, layoutTerms, prettyNames, prefixSeperator,
  classTerminals, parserAttributeAspects, prefixesForTerminals, componentGrammarMarkingTerminals, subClasses, superClasses
  on SyntaxDcl;

aspect default production
top::SyntaxDcl ::=
{
  -- Empty values as defaults
  propagate cstProds, allTerminals, allIgnoreTerminals, allMarkingTerminals, allProductions, allProductionNames, allNonterminals, disambiguationClasses, memberTerminals, dominatingTerminalContribs, classTerminalContribs, superClassContribs, parserAttributeAspectContribs, lexerClassRefDcls, layoutContribs, prettyNamesAccum;
  top.domContribs = error("Internal compiler error: should only ever be demanded of lexer classes");
  top.subContribs = error("Internal compiler error: should only ever be demanded of lexer classes");
  top.exportedProds = error("Internal compiler error: should only ever be demanded of nonterminals");
  top.terminalRegex = error("Internal compiler error: should only ever be demanded of terminals");
  top.hasCustomLayout = false;
}


{--
 - A nonterminal. Using Type instead of String, because we'll be doing parameterization later.
 - subdcls is empty to start. A transformed version of the tree will move all
 - productions for this nonterminal under subdcls.
 -}
abstract production syntaxNonterminal
top::SyntaxDcl ::= t::Type subdcls::Syntax exportedProds::[String] exportedLayoutTerms::[String] modifiers::SyntaxNonterminalModifiers
{
  top.fullName = t.typeName;
  top.sortKey = "EEE" ++ t.typeName;
  top.cstDcls := [(t.typeName, top)] ++ subdcls.cstDcls;
  top.allNonterminals := [top];
  
  top.cstErrors <- if length(searchEnvTree(t.typeName, top.cstEnv)) == 1 then []
                   else ["Name conflict with nonterminal " ++ t.typeName];
  top.cstProds := subdcls.cstProds;
  top.cstNormalize :=
    let myProds :: [SyntaxDcl] = searchEnvTree(t.typeName, top.cstNTProds)
    in if null(myProds) then [] -- Eliminate "Useless nonterminals" as these are expected in Silver code (non-syntax)
       else [ syntaxNonterminal(^t, foldr(consSyntax, nilSyntax(), myProds),
                exportedProds, exportedLayoutTerms, ^modifiers,
                location=top.location, sourceGrammar=top.sourceGrammar)
            ]
    end;
  
  top.exportedProds = exportedProds;
  top.hasCustomLayout = modifiers.customLayout.isJust;
  top.layoutContribs := map(pair(fst=t.typeName, snd=_), fromMaybe(exportedLayoutTerms, modifiers.customLayout));

  top.copperElementReference = copper:elementReference(top.sourceGrammar,
    top.location, top.containingGrammar, makeCopperName(t.typeName));
  top.copperGrammarElements =
    [ copper:nonterminal_(top.sourceGrammar, top.location,
        makeCopperName(t.typeName), t.typeName, makeNTName(t.typeName))
    ] ++ subdcls.copperGrammarElements;

  modifiers.nonterminalName = t.typeName;

  t.boundVariables = t.freeVariables;
}

{--
 - A terminal, and regular expression.
 -}
abstract production syntaxTerminal
top::SyntaxDcl ::= n::String regex::Regex modifiers::SyntaxTerminalModifiers
{
  top.fullName = n;
  top.sortKey = "CCC" ++ n;
  top.cstDcls := [(n, top)];
  top.cstErrors <-
    if length(searchEnvTree(n, top.cstEnv)) == 1 then []
    else ["Name conflict with terminal " ++ n];

  modifiers.terminalName = n;

  top.allTerminals := [top];
  top.allIgnoreTerminals := if modifiers.ignored then [top.fullName] else [];
  top.allMarkingTerminals := if modifiers.marking then [top.fullName] else [];
  top.classTerminalContribs := modifiers.classTerminalContribs;
  top.memberTerminals := [top];
  top.dominatingTerminalContribs :=
    map(pair(fst=n, snd=_), flatMap((.memberTerminals), modifiers.submits_)) ++
    map(pair(fst=_, snd=top), map((.fullName), flatMap((.memberTerminals), modifiers.dominates_)));
  top.terminalRegex = ^regex;

  -- left(terminal name) or right(string prefix)
  production pfx::[String] = searchEnvTree(n, top.prefixesForTerminals);
  top.cstErrors <-
    if length(pfx) <= 1 then []
    else ["Multiple prefixes for terminal " ++ n];
  
  top.cstNormalize :=
    case modifiers.prefixSeperatorToApply of
    | just(sep) ->
        [ syntaxTerminal(n, seq(^regex, regexLiteral(sep)), ^modifiers,
            location=top.location, sourceGrammar=top.sourceGrammar)
        ]
    | nothing() -> [^top]
    end;

  local prettyName :: String = fromMaybe(fromMaybe(n, asPrettyName(^regex)), modifiers.prettyName);
  top.prettyNamesAccum := [(prettyName, n)];
  local disambiguatedPrettyName :: String =
    case length(tm:lookup(prettyName, top.prettyNames)) of
    | 1 -> prettyName
    | _ -> prettyName ++ " (" ++ n ++ ")"
    end;

  top.copperElementReference = copper:elementReference(top.sourceGrammar,
    top.location, top.containingGrammar, makeCopperName(n));
  top.copperGrammarElements =
    [ copper:terminal_(top.sourceGrammar, top.location, makeCopperName(n),
        disambiguatedPrettyName, regex.copperRegex,
        modifiers.opPrecedence.isJust, modifiers.opPrecedence.fromJust,
        fromMaybe("", modifiers.opAssociation), makeTerminalName(n), 
        "RESULT = new " ++ makeTerminalName(n) ++ "(lexeme,virtualLocation,(int)getStartRealLocation().getPos(),(int)getEndRealLocation().getPos());tokenList.add(RESULT);\n" ++ modifiers.acode,
        map((.copperElementReference), modifiers.lexerClasses), !null(pfx),
        copper:elementReference(top.sourceGrammar, top.location,
          top.containingGrammar, head(pfx)),
        map((.copperElementReference), modifiers.submits_), map((.copperElementReference), modifiers.dominates_))
    ];
}

{--
 - A (named) production. Using types for later parameterization.
 -}
abstract production syntaxProduction
top::SyntaxDcl ::= ns::NamedSignature  modifiers::SyntaxProductionModifiers
{
  top.fullName = ns.fullName;
  top.sortKey = "FFF" ++ ns.fullName;
  top.cstDcls := [(ns.fullName, top)];
  top.allProductions := [top];
  top.allProductionNames := [ns.fullName];
  
  modifiers.productionSig = ns;

  production lhsRef :: [Decorated SyntaxDcl] =
    searchEnvTree(ns.outputElement.typerep.typeName, top.cstEnv);
  production rhsRefs :: [[Decorated SyntaxDcl]] =
    lookupStrings(map((.typeName), map((.typerep), ns.inputElements)), top.cstEnv);

  top.cstErrors <- if length(searchEnvTree(ns.fullName, top.cstEnv)) == 1 then []
                   else ["Name conflict with production " ++ ns.fullName];

  top.cstErrors <- if length(lhsRef) == 1 then
                   case head(lhsRef) of
                   | syntaxNonterminal(_,_,_,_,_) -> []
                   | _ -> ["LHS of production " ++ ns.fullName ++ " is not a nonterminal"] end
                   else ["Nonterminal " ++ ns.outputElement.typerep.typeName ++ " was referenced but " ++
                         "this grammar was not included in this parser. (Referenced from LHS of production " ++ ns.fullName ++ ")"];

  top.cstErrors <- checkRHS(ns.fullName, map((.typerep), ns.inputElements), rhsRefs);

  top.cstProds := [(ns.outputElement.typerep.typeName, ^top)];
  top.cstNormalize := [];
  
  top.hasCustomLayout = modifiers.customLayout.isJust;
  top.layoutContribs :=
    map(pair(fst=ns.fullName, snd=_), fromMaybe([], modifiers.customLayout)) ++
    -- The production inherits its LHS nonterminal's layout, unless overridden.
    (if top.hasCustomLayout then [] else [(ns.fullName, head(lhsRef).fullName)]) ++
    -- All nonterminals on the RHS that export this production inherit this
    -- production's layout, unless overriden on the nonterminal.
    flatMap(
      \ rhsRef::[Decorated SyntaxDcl] ->
        case head(rhsRef) of
        | syntaxNonterminal(_,_,_,_,_)
          when !head(rhsRef).hasCustomLayout &&
               contains(top.fullName, head(rhsRef).exportedProds) ->
          [(head(rhsRef).fullName, ns.fullName)]
        | _ -> []
        end,
      rhsRefs);
  
  -- Copper doesn't support default layout on nonterminals, so we specify layout on every production.
  production prodLayout::[copper:ElementReference] =
    map(\dcl::[Decorated SyntaxDcl] -> head(dcl).copperElementReference,
        lookupStrings(searchEnvTree(ns.fullName, top.layoutTerms), top.cstEnv));

  local isTracked :: Boolean =
    case head(lhsRef) of
    | syntaxNonterminal(nonterminalType(_, _, _, tracked), _, _, _, _) -> tracked
    | _ -> error("LHS is not a nonterminal")
    end;
  local commaIfArgsOrAnnos :: String = if length(ns.inputElements) + length(ns.namedInputElements)!= 0 then "," else "";
  local originImpl :: String = if isTracked then
                               "new silver.core.PparsedOriginInfo(common.Terminal.createSpan(_children, virtualLocation, (int)_pos.getPos()), common.ConsCell.nil, common.OriginsUtil.SET_FROM_PARSER_OIT)"  ++ commaIfArgsOrAnnos
                               else "";

  local code::String =
    -- Annoying workaround for if a lambda in an action block needs to capture RESULT when accessing a child.
    -- Java complains when we capture something that is non-final.
    "final " ++ makeProdName(ns.fullName) ++ " RESULTfinal = new " ++ makeProdName(ns.fullName) ++ "(" ++ originImpl ++ fetchChildren(0, ns.inputElements) ++ insertLocationAnnotation(ns) ++ ");\n" ++
    "RESULT = RESULTfinal;\n" ++
    modifiers.acode;

  top.copperElementReference = copper:elementReference(top.sourceGrammar,
    top.location, top.containingGrammar, makeCopperName(ns.fullName));
  top.copperGrammarElements =
    [ copper:production_(top.sourceGrammar, top.location,
        makeCopperName(ns.fullName), modifiers.productionPrecedence.isJust,
        modifiers.productionPrecedence.fromJust,
        modifiers.productionOperator.isJust,
        modifiers.productionOperator.fromJust.copperElementReference, code,
        head(lhsRef).copperElementReference,
        map((.copperElementReference), map(head, rhsRefs)), prodLayout)
    ];
}

fun fetchChildren String ::= i::Integer  ns::[NamedSignatureElement] =
  if null(ns) then ""
  else if null(tail(ns)) then "_children[" ++ toString(i) ++ "]"
  else "_children[" ++ toString(i) ++ "], " ++ fetchChildren(i + 1, tail(ns));

function insertLocationAnnotation
String ::= ns::NamedSignature
{
  local pfx :: String = if null(ns.inputElements) then "" else ", ";

  return if null(ns.namedInputElements) then ""
  else if length(ns.namedInputElements) > 1 then pfx ++ "multiple_annotation_problem" -- TODO
  else if head(ns.namedInputElements).elementName != "silver:core:location" then pfx ++ "unknown_annotation_type_problem"
  else pfx ++ "common.Terminal.createSpan(_children, virtualLocation, (int)_pos.getPos())";
}


fun lookupStrings [[a]] ::= t::[String] e::EnvTree<a> = map(searchEnvTree(_, e), t);
fun checkRHS [String] ::= pn::String rhs::[Type] refs::[[Decorated SyntaxDcl]] =
  if null(rhs) then []
  else (if length(head(refs)) == 1 then
         case head(head(refs)) of
         | syntaxNonterminal(_,_,_,_,_) -> []
         | syntaxTerminal(_,_,_) -> []
         | _ -> ["parameter " ++ head(rhs).typeName ++ " of production " ++ pn ++ " is not syntax."]
         end
       else ["Terminal " ++ head(rhs).typeName ++ " was referenced but " ++
             "this grammar was not included in this parser. (Referenced from RHS of " ++ pn ++ ")"])
       ++ checkRHS(pn, tail(rhs), tail(refs));

{--
 - A lexer class. Copper doesn't take these, so we'll have to translate away
 - the domlist/sublist that appear here.
 -}
abstract production syntaxLexerClass
top::SyntaxDcl ::= n::String modifiers::SyntaxLexerClassModifiers
{
  top.fullName = n;
  top.sortKey = "AAA" ++ n;
  top.cstDcls := [(n, top)];
  top.cstErrors <-
    if length(searchEnvTree(n, top.cstEnv)) == 1 then []
    else ["Name conflict with lexer class " ++ n];
  modifiers.className = n;

  -- TODO: these attributes are on all SyntaxDcls, but only have meaning for this production
  -- that's UUUUGLY.
  top.domContribs = modifiers.dominates_;
  top.subContribs = modifiers.submits_;

  top.cstNormalize := [^top];
  top.superClassContribs := modifiers.superClassContribs;
  top.disambiguationClasses := modifiers.disambiguationClasses;

  production terms :: [String] = searchEnvTree(n, top.classTerminals);
  top.memberTerminals := flatMap(searchEnvTree(_, top.cstEnv), terms);

  local termsInit::String =
    foldr(
      \ term::String rest::String -> s"new common.ConsCell(Terminals.${makeCopperName(term)}.num(), ${rest})",
      "common.ConsCell.nil",
      terms);
  top.lexerClassRefDcls :=
    s"    protected common.ConsCell ${makeCopperName(n)} = ${termsInit};\n";

  top.copperElementReference = copper:elementReference(top.sourceGrammar,
    top.location, top.containingGrammar, makeCopperName(n));
  top.copperGrammarElements =
    [ copper:terminalClass(top.sourceGrammar, top.location, makeCopperName(n))
    ];
}

{--
 - A parser attribute. The acode initializes it.
 -}
abstract production syntaxParserAttribute
top::SyntaxDcl ::= n::String ty::Type acode::String
{
  top.fullName = n;
  top.sortKey = "BBB" ++ n;
  top.cstDcls := [(n, top)];
  top.cstErrors <- if length(searchEnvTree(n, top.cstEnv)) == 1 then []
                   else ["Name conflict with parser attribute " ++ n];

  top.cstNormalize := [^top];

  top.copperElementReference = copper:elementReference(top.sourceGrammar,
    top.location, top.containingGrammar, makeCopperName(n));
  top.copperGrammarElements =
    [ copper:parserAttribute(top.sourceGrammar, top.location,
        makeCopperName(n), ty.transType,
        acode ++ implode("\n", searchEnvTree(n, top.parserAttributeAspects)))
    ];

  -- TODO: technically, there should be no free variables in ty.
  ty.boundVariables = [];
}

{--
 - Additonal action code that should be added to the initialization of
 - a parser attribute. 
 -}
abstract production syntaxParserAttributeAspect
top::SyntaxDcl ::= n::String acode::String
{
  top.fullName = n;
  top.sortKey = "BBB" ++ n;
  top.cstDcls := [];
  top.cstErrors <-
    if !null(searchEnvTree(n, top.cstEnv)) then []
    else ["Parser attribute " ++ n ++ " was referenced but this grammar was not included in this parser."];

  top.cstNormalize := [^top];

  top.parserAttributeAspectContribs := [(n, acode)];
  -- The Copper information for these gets picked up by the main syntaxParserAttribute declaration.
  top.copperElementReference = error("can't demand copperElementReference of an aspect");
  top.copperGrammarElements = [];
}

{--
 - A disambiguation group.
 - The acode distinguished between the listed terminals.
 -}
abstract production syntaxDisambiguationGroup
top::SyntaxDcl ::= n::String terms::[String] applicableToSubsets::Boolean acode::String
{
  top.fullName = n;
  top.sortKey = "DDD" ++ n;
  top.cstDcls := [];

  local trefs::[[Decorated SyntaxDcl]] = lookupStrings(terms, top.cstEnv);

  -- this 'n' here appears to actually hold the line number of the
  -- disambiguation, and the grammar. But we arent supposed to know this?
  top.cstErrors <- flatMap(\p ::Pair<String [Decorated SyntaxDcl]> ->
      if !null(p.snd) then []
      else ["Terminal " ++ p.fst ++ " was referenced but " ++
            "this grammar was not included in this parser. (Referenced from disambiguation group " ++ n ++ ")"],
    zip(terms, trefs));

  top.cstNormalize := [^top];

  top.copperElementReference = copper:elementReference(top.sourceGrammar,
    top.location, top.containingGrammar, makeCopperName(n));
  local members::[copper:ElementReference] =
    map(\dcl::[Decorated SyntaxDcl] -> head(dcl).copperElementReference,
        trefs);
  top.copperGrammarElements =
    [ copper:disambiguationFunction(top.sourceGrammar, top.location,
        makeCopperName(n), acode, members, applicableToSubsets)
    ];
}

{-- Sort key PREFIXES are as follows:
    | syntaxLexerClass(_,_,_)           ->  AAA
    | syntaxParserAttribute(_,_,_)      ->  BBB
    | syntaxTerminal(_,_,_)             ->  CCC
    | syntaxDisambiguationGroup(_,_,_)  ->  DDD
    | syntaxNonterminal(_,_)            ->  EEE
    | syntaxProduction(_,_,_,_)         ->  FFF
-}

function sortKeyLte
Boolean ::= l::SyntaxDcl r::SyntaxDcl
{ return l.sortKey <= r.sortKey; }

