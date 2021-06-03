grammar silver:compiler:definition:concrete_syntax:copper;

-- edu.umn.cs.melt.copper.compiletime.spec.grammarbeans.GrammarElement
type GrammarElement foreign;

-- edu.umn.cs.melt.copper.compiletime.spec.grammarbeans.DisambiguationFunction
function disambiguationFunction
GrammarElement ::= id::String  code::String  members::[ElementReference]
    applicableToSubsets::Boolean
{
  return error("copper FFI function");
} foreign {
  "java" : return "common.CopperUtil.makeDisambiguationFunction(%id%.toString(), %code%.toString(), new common.javainterop.ConsCellCollection(%members%), %applicableToSubsets%)";
}

-- edu.umn.cs.melt.copper.compiletime.spec.grammarbeans.Nonterminal
function nonterminal_
GrammarElement ::= id::String  pp::String  type_::String
{
  return error("copper FFI function");
} foreign {
  "java" : return "common.CopperUtil.makeNonTerminal(%id%.toString(), %pp%.toString(), %type_%.toString())";
}

-- edu.umn.cs.melt.copper.compiletime.spec.grammarbeans.OperatorClass

-- edu.umn.cs.melt.copper.compiletime.spec.grammarbeans.ParserAttribute

-- edu.umn.cs.melt.copper.compiletime.spec.grammarbeans.Production

-- edu.umn.cs.melt.copper.compiletime.spec.grammarbeans.Terminal
function terminal_
GrammarElement ::= id::String  pp::String  regex::Regex  hasPrecedence::Boolean
    precedence_::Integer  hasAssociativity::Boolean associativity::String
    type_::String  code::String  classes_::[ElementReference] hasPrefix::Boolean
    prefix_::ElementReference submits_::[ElementReference]  dominates_::[ElementReference]
{
  return error("copper FFI function");
} foreign {
  "java" : return "common.CopperUtil.makeTerminal(%id%.toString(), %pp%.toString(), (edu.umn.cs.melt.copper.compiletime.spec.grammarbeans.Regex)%regex%, %hasPrecedence% ? %precedence_% : null, %hasAssociativity% ? %associativity%.toString() : null, %type_%.toString(), %code%.toString(), new common.javainterop.ConsCellCollection(%classes_%), %hasPrefix% ? (edu.umn.cs.melt.copper.compiletime.spec.grammarbeans.CopperElementReference)%prefix_% : null, new common.javainterop.ConsCellCollection(%submits_%), new common.javainterop.ConsCellCollection(%dominates_%))";
}

-- edu.umn.cs.melt.copper.compiletime.spec.grammarbeans.TerminalClass
function terminalClass
GrammarElement ::= id::String
{
  return error("copper FFI function");
} foreign {
  "java" : return "common.CopperUtil.makeTerminalClass(%id%.toString())";
}