grammar silver:compiler:extension:doc:core;

import silver:compiler:driver:util;

attribute genFiles occurs on RootSpec;
attribute docDcls occurs on RootSpec;

aspect production interfaceRootSpec
top::RootSpec ::= _ _ _
{
  top.genFiles := [];
  top.docDcls := [];
}

aspect production errorRootSpec
top::RootSpec ::= _ _ _ _ _
{
  top.genFiles := [];
  top.docDcls := [];
}

aspect production grammarRootSpec
top::RootSpec ::= g::Grammar  _ _ _ _ _
{
  top.genFiles := toSplitFiles(g, g.upDocConfig, [], []);
  top.docDcls := g.docDcls;
  extraFileErrors <- g.allFileDocErrors;

  g.downDocConfig = g.upDocConfig;
}

fun silverToMdFilename String ::= fileName::String =
  foldr(
    \ ext::String file::String ->
      if endsWith(ext, file) then substitute(ext, ".md", file) else file,
    fileName, allowedSilverFileExtensions);

@{- 
 - Turn the files in a grammar into zero or more single-file docs pages, and collect the rest of the docs
 - (possibly zero) into the index file.
 -}
fun toSplitFiles
[Pair<String String>] ::= g::Decorated Grammar with {decorate, downDocConfig} grammarConf::[DocConfigSetting] forIndex::[CommentItem] soFar::[Pair<String String>] =
  case g of
  | consGrammar(this, rest) ->
    let filename::String = getParsedOriginLocation(this).fromJust.filename
    in if getSplit(this.localDocConfig) then toSplitFiles(rest, grammarConf, forIndex, formatFile(
        silverToMdFilename(filename),
        getFileTitle(this.localDocConfig, silverToMdFilename(filename)),
        getFileWeight(this.localDocConfig), true,
        s"In grammar `${g.grammarName}` file `${filename}`: "++(if getToc(this.localDocConfig) then "{{< toc >}}" else ""), 
        this.docs) ++ soFar) else toSplitFiles(rest, grammarConf, forIndex ++ this.docs, soFar)
    end
  | nilGrammar() -> let skel::Boolean = (length(soFar) == 0 && length(grammarConf) == 0 && length(forIndex) == 0) in
        formatFile("_index.md",
          getGrammarTitle(grammarConf, "["++g.grammarName++"]"++(if skel then " (skel)" else "")),
          getGrammarWeight(grammarConf) + (if skel then 10000 else 0),
          false, s"Contents of `[${g.grammarName}]`: {{< toc-tree >}} \n\nDefined in this grammar:", forIndex) ++ soFar end
  end;

function formatFile
[Pair<String String>] ::= fileName::String title::String weight::Integer
                          skipIfEmpty::Boolean pfxText::String
                          comments::[CommentItem]
{
  local realDocs::[CommentItem] = filter((.doEmit), comments);
  local stubDocs::[CommentItem] = filter((.stub), realDocs);
  local nonStubDocs::[CommentItem] = filter((\x::CommentItem->!x.stub), realDocs);
  return if length(realDocs) == 0 && skipIfEmpty then [] else [(fileName, s"""---
title: "${title}"
weight: ${toString(weight)}
geekdocBreadcrumb: false
---

${pfxText}

${implode("\n\n<hr/>\n\n", map((.body), nonStubDocs))}


"""
++ (if length(stubDocs)!=0 then s"""
{{< expand "Undocumented Items" "..." >}}

${implode("\n\n<hr/>\n\n", map((.body), stubDocs))}

{{< /expand >}}
""" else ""
))];
}

fun lastPart String ::= s::String = last(explode(":", s));
