{- A Universal set of common attributes for use in language descriptions -}
grammar silver:langutil;

exports silver:langutil:reflect with silver:core; -- Contains pp definitions for AST

import silver:langutil:pp;
import silver:langutil:lsp;  -- Make sure it gets built in the langutil artifact

{--
 - The unparse of a syntax tree.
 -}
synthesized attribute unparse :: String;

{--
 - The pretty print of a syntax tree.
 -}
synthesized attribute pp :: Document;

{--
 - The pretty prints of a 'list' syntax tree.
 -}
synthesized attribute pps :: [Document];

{--
 - For computing the abstract syntax tree from a concrete syntax tree
 -}
synthesized attribute ast<a> :: a;

{--
 - For accumulating error/warning messages over a syntax tree
 -}
monoid attribute errors :: [Message];

