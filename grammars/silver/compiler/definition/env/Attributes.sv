grammar silver:compiler:definition:env;

-- TODO: it'd be nice to find a way to rejigger things so these imports can go away.
import silver:util:cmdargs only CmdArgs;
import silver:compiler:definition:flow:driver only ProductionGraph, FlowType;
import silver:compiler:driver:util only RootSpec;

{- This grammar contains common definitions of attributes that
   are widely used in the Silver compiler.
   
   Attributes should NOT be added here lightly!
   Include a justification for each one.
   
   These are truely cross-cutting attributes, not simple
   things that occurs on a few pieces of syntax.
   A good rule of thumb is: is it used by RootSpec Root and IRoot?
 --------------------------------------------------------------------}

--
-- RootSpec, Root and IRoot grammar graph-related attributes.
--

{--
 - The name of the grammar this RootSpec represents.
 -}
synthesized attribute declaredName :: String;
{--
 - Grammars directly depended upon by this grammar.
 - i.e. imports, exports, parser components, etc.
 - NOT options, or triggers, or transitive dependencies.
 -}
monoid attribute moduleNames :: [String];
{--
 - Grammars DIRECTLY exported by this grammar.
 -}
monoid attribute exportedGrammars :: [String];
{--
 - Grammars this grammar specifies as optional modifications.
 - (i.e. grammars that introduce more productions that do not forward)
 -}
monoid attribute optionalGrammars :: [String];
{--
 - A list of triggered builds. Format is actually [ [build x, with gram], ... ]
 -}
monoid attribute condBuild :: [[String]];
{--
 - A list of TRUE dependencies of this grammar.
 - Closes over moduleNames using exports & triggers.
 -}
monoid attribute allGrammarDependencies :: [String];
{--
 - A list of attribute occurences that are exported by this particular grammar.
 - Seperate from defs as a workaround for circular dependency issues.
 -}
monoid attribute occursDefs :: [OccursDclInfo];


--
-- Standard "little attributes," used almost universally in the compiler.
--

{--
 - A list of definitions exported by this particular grammar.
 -}
monoid attribute defs :: [Def];
{--
 - The environment. Dun dun dunnn.
 -}
inherited attribute env :: Env;

--
-- Top-level, compiler-wide information passed down by the build process
-- TODO: these don't necessarily make sense. Can we move them pleaaase?!

{--
- All grammars Silver looked at. Despite the name, including interface files.
-}
inherited attribute compiledGrammars :: EnvTree<Decorated RootSpec>;
{--
- Compiler configuration information, made available everywhere.
-}
inherited attribute config :: Decorated CmdArgs;
{--
- Flow information computed for this grammar
-}
inherited attribute productionFlowGraphs :: EnvTree<ProductionGraph>;
inherited attribute grammarFlowTypes :: EnvTree<FlowType>;

{--
 - The path to the origin of this root spec
 -}
synthesized attribute grammarSource :: String;
