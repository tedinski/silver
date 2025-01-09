grammar silver:compiler:extension:doc:core;

import silver:compiler:driver;

synthesized attribute genFiles :: [Pair<String String>] with ++;

@{-
 - Used for getting doc comments on AGDcls to emit.
 - Note that not every item really should be emitted, see doEmit.
 -}
monoid attribute docs :: [CommentItem] occurs on Grammar, File, AGDcls, AGDcl, ClassBodyItem, InstanceBodyItem, ClassBody, InstanceBody, DataConstructors, DataConstructor;

@@{-
 - Doc config is managed in both a per-file, and per-grammar way. Directives are either file-scope
 - or grammar-scope. A file-scoped directive for the same setting beats a grammar-scoped one. To do
 - this, directives flow up via @link[upDocConfig] from AGDcls to reach `grammarRootSpec` and
 - then flow back down via @link[downDocConfig]. However, when passing through `File` the only
 - doc directives that flow up to the Grammar scope are those with .fileScope = true. Then when
 - flowing back down, those with .fileScope = false are re-added in front of grammar scope directives
 - in @link[downDocConfig] (and stored on the `File` as @link[localDocConfig].) -}

@{- Final doc config flowing back down, inside files (Files) will include file scoped settings first. -}
inherited attribute downDocConfig :: [DocConfigSetting] occurs on Grammar, File, AGDcls, AGDcl, ClassBodyItem, InstanceBodyItem, ClassBody, InstanceBody, DataConstructors, DataConstructor;

@{- Doc config information flowing up. File scoped settings are stripped at the File level. -}
monoid attribute upDocConfig :: [DocConfigSetting] occurs on Grammar, File, AGDcls, AGDcl, ClassBodyItem, InstanceBodyItem, ClassBody, InstanceBody, DataConstructors, DataConstructor;

@{- Snapshot of @link[downDocConfig] stored on `File`. -}
synthesized attribute localDocConfig :: [DocConfigSetting] occurs on File;

synthesized attribute undocumentedNamed :: [String] occurs on File, Grammar;
synthesized attribute documentedNamed :: [String] occurs on File, Grammar;

@{-
 - Declarations of documented AGDcls, flowing up. Used for linking and counting documented items.
 - Flows back down as @link[docEnv].
 -}
monoid attribute docDcls :: [Pair<String DocDclInfo>] occurs on Grammar, File, AGDcls, AGDcl, ClassBodyItem, InstanceBodyItem, ClassBody, InstanceBody, DataConstructors, DataConstructor;

@{- Environment of all documented AGDcls, flowing back down after being computed from @link[docDcls].  -}
inherited attribute docEnv :: tm:Map<String DocDclInfo>;
attribute docEnv occurs on File, AGDcls, AGDcl, ClassBodyItem, InstanceBodyItem, ClassBody, InstanceBody, DataConstructors, DataConstructor;
propagate docEnv on AGDcls, AGDcl, ClassBodyItem, InstanceBodyItem, ClassBody, InstanceBody, DataConstructors, DataConstructor;

@{- Errors arising from ill-formed doc comments.  -}
monoid attribute docErrors :: [Message];
attribute docErrors occurs on File, AGDcls, AGDcl, ClassBodyItem, InstanceBodyItem, ClassBody, InstanceBody, DataConstructors, DataConstructor;
propagate docErrors on File, AGDcls, AGDcl, ClassBodyItem, InstanceBodyItem, ClassBody, InstanceBody, DataConstructors, DataConstructor;

@{-
 - All file names in a grammar, paired with their documentation-related error messages.
 -}
synthesized attribute allFileDocErrors::[(String, [Message])] occurs on Grammar;

aspect production fileRoot
top::File ::= gdcl::GrammarDcl ms::ModuleStmts ims::ImportStmts ags::AGDcls
{
  top.docs := ags.docs;
  top.localDocConfig = ags.downDocConfig;
  top.upDocConfig := filter((\x::DocConfigSetting -> !x.fileScope), ags.upDocConfig);
  top.docDcls := ags.docDcls;
  top.undocumentedNamed = flatMap((.undocNames), top.docs);
  top.documentedNamed = flatMap((.docNames), top.docs);

  ags.downDocConfig = filter((\x::DocConfigSetting -> x.fileScope), ags.upDocConfig) ++ top.downDocConfig;
  ags.docEnv = tm:add(flatMap((.docDcls), searchEnvTree(top.grammarName, top.compiledGrammars)), tm:empty());
}

aspect production nilAGDcls
top::AGDcls ::=
{
  top.docs := [];
  top.upDocConfig := [];
  top.docDcls := [];
}

aspect production consAGDcls
top::AGDcls ::= h::AGDcl t::AGDcls
{
  top.docs := h.docs ++ t.docs;
  h.downDocConfig = top.downDocConfig;
  t.downDocConfig = top.downDocConfig;
  top.upDocConfig := h.upDocConfig ++ t.upDocConfig;
  top.docDcls := h.docDcls ++ t.docDcls;
}

aspect default production
top::AGDcl ::=
{
  top.upDocConfig := [];
  -- top.docs := [mkUndocumentedItem(s"<default AGDcl production `${head(explode("(", genericShow(top)))}`(fwd)@${top.location.unparse}>", top)];
  top.docDcls := [];
  -- top.docUnparse = head(explode("\n", top.unparse)) ++ "\n{{< hint danger >}}\nNo docUnparse defined for `" ++ genericShow(top) ++ "`\n{{< /hint >}}\n\n";
}

aspect production appendAGDcl
top::AGDcl ::= h::AGDcl t::AGDcl
{
  top.docs := h.docs ++ t.docs;
  h.downDocConfig = top.downDocConfig;
  t.downDocConfig = top.downDocConfig;
  top.upDocConfig := h.upDocConfig ++ t.upDocConfig;
  top.docDcls := h.docDcls ++ t.docDcls;
}

aspect production nilGrammar
top::Grammar ::=
{
  top.docs := [];
  top.upDocConfig := [];
  top.docDcls := [];
  top.undocumentedNamed = [];
  top.documentedNamed = [];
  top.allFileDocErrors = [];
}

aspect production consGrammar
top::Grammar ::= c1::File  c2::Grammar
{
  top.docs := c1.docs ++ c2.docs;
  top.upDocConfig := c1.upDocConfig ++ c2.upDocConfig;
  c1.downDocConfig = top.downDocConfig;
  c2.downDocConfig = top.downDocConfig;
  top.docDcls := c1.docDcls ++ c2.docDcls;
  top.undocumentedNamed = c1.undocumentedNamed ++ c2.undocumentedNamed;
  top.documentedNamed = c1.documentedNamed ++ c2.documentedNamed;
  top.allFileDocErrors = (getParsedOriginLocation(c1).fromJust.filename, c1.docErrors) :: c2.allFileDocErrors;
}

-- consGrammar(FILE1, consGrammar(FILE2, nilGrammar()))
