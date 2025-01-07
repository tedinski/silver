grammar silver:compiler:host;

{- Silver is built as an extensible language with a core "host" language and a
 - number of extensions and modifications containing additional features.
 - However many of these extensions we typically always want to include by
 - when building extended versions of Silver, and it becomes cumbersome to list
 - them repeatedly.
 - Thus we provide this grammar that exports all the components of the
 - "default" Silver host language in one place.
 - Note that this list may grow over time.
 -} 

-- The "core" host language:
exports silver:compiler:host:core;

-- Modifications to Silver = optional features that are not pure extensions.
-- These are explicitly annotated as "options" within the core host language
exports silver:compiler:modification:let_fix;
exports silver:compiler:modification:lambda_fn;
exports silver:compiler:modification:concisefunctions;
exports silver:compiler:modification:collection;
exports silver:compiler:modification:primitivepattern;
exports silver:compiler:modification:ffi;
exports silver:compiler:modification:copper;
exports silver:compiler:modification:defaultattr;
exports silver:compiler:modification:list;
-- slight hacks, for the moment
exports silver:compiler:modification:copper_mda;

-- Pure extensions to Silver
exports silver:compiler:extension:doc;
exports silver:compiler:extension:convenience;
exports silver:compiler:extension:easyterminal;
exports silver:compiler:extension:deprecation;
exports silver:compiler:extension:testing;
exports silver:compiler:extension:auto_ast;
exports silver:compiler:extension:templating;
exports silver:compiler:extension:patternmatching;
exports silver:compiler:extension:treegen;
exports silver:compiler:extension:autoattr;
exports silver:compiler:extension:strategyattr;
exports silver:compiler:extension:do_notation;
exports silver:compiler:extension:rewriting;
exports silver:compiler:extension:silverconstruction;
exports silver:compiler:extension:astconstruction;
exports silver:compiler:extension:constructparser;
exports silver:compiler:extension:tuple;
exports silver:compiler:extension:regex;
exports silver:compiler:extension:convenienceaspects;
exports silver:compiler:extension:attrsection;
exports silver:compiler:extension:implicit_monads;
exports silver:compiler:extension:data;
exports silver:compiler:extension:deriving;
exports silver:compiler:extension:opersection;

-- Other generally useful stuff:
exports silver:compiler:translation:java;
exports silver:compiler:driver;
exports silver:compiler:analysis:warnings:flow;
exports silver:compiler:analysis:warnings:exporting;
exports silver:compiler:langserver;
exports silver:compiler:refactor;
