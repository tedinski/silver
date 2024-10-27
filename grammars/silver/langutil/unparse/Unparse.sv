grammar silver:langutil:unparse;

imports silver:reflect;
imports silver:langutil;
imports silver:langutil:pp;
imports silver:util:treemap as map;

@{--
 - Unparse a tree, preserving layout from its parse tree via origin tracking.
 - The productions in the tree should only consist of nonterminal and terminal symbols;
 - in a language with seperate concrete and abstract syntax, this may require defining a
 - translation from abstract back to concrete syntax.
 -
 - This is intended for use in e.g. refactoring tools, where transformations can be applied
 - on the tree, but one would like to turn the tree back into a string without affecting
 - layout in otherwise-unchanged portions of the tree.
 -
 - Layout preceeding and following the root of the tree is included in the output.
 - 
 - @param origText  The original text of the file that was parsed to create the origin of tree.
 - @param tree  The concrete syntax tree to unparse.
 - @return The unparse of the tree, with layout from origText inserted in unchanged portions of the tree.
 -}
function unparseFile
Document ::= origText::String  tree::a
{
  local parseTree::AST = getParseTree(tree);
  parseTree.origText = origText;
  parseTree.lineIndent = map:fromList(enumerate(map(countIndent, explode("\n", origText))));
  parseTree.initialIndent = parseTree.indent;

  local ast::AST = reflect(tree);
  ast.origText = origText;
  ast.lineIndent = parseTree.lineIndent;
  ast.parseTree = just(parseTree);

  local preLayout::String = substring(0, parseTree.originLoc.index, origText);
  local postLayout::String = substring(parseTree.originLoc.endIndex, length(origText), origText);

  return
    blobPP(0, preLayout) ++
    maybeNest(parseTree.indent,
      ast.unparseWithLayout ++
      blobPP(parseTree.indent, postLayout));
}

@{--
 - Like unparseFile, but intended for unparsing a tree corresponding to a fragment of a file.
 - Layout preceeding and following the root of the tree is not included.
 - 
 - @param origText  The original text of the file that was parsed to create the origin of tree.
 - @param tree  The concrete syntax tree to unparse.
 - @return The unparse of the tree, with layout from origText inserted in unchanged portions of the tree.
 -}
function unparseFragment
Document ::= origText::String  tree::a
{
  local parseTree::AST = getParseTree(tree);
  parseTree.origText = origText;
  parseTree.lineIndent = map:fromList(enumerate(map(countIndent, explode("\n", origText))));
  parseTree.initialIndent = parseTree.indent;

  local ast::AST = reflect(tree);
  ast.origText = origText;
  ast.lineIndent = parseTree.lineIndent;
  ast.parseTree = just(parseTree);

  return ast.unparseWithLayout;
}

fun getParseTree AST ::= ast::a =
  case getOriginInfo(ast) of
  | just(parsedOriginInfo(l)) -> reflect(ast)
  | just(originOriginInfo(o, _)) -> getParseTree(o)
  | just(originAndRedexOriginInfo(o, _, _, _)) -> getParseTree(o)
  | _ -> error("Tree does not have a parsed origin: " ++ showOriginInfoChain(ast))
  end;

-- Attributes computed on parseTree
inherited attribute origText::String occurs on AST, ASTs;
inherited attribute lineIndent::map:Map<Integer Integer> occurs on AST, ASTs;
inherited attribute initialIndent::Integer occurs on AST, ASTs;
propagate origText, lineIndent on AST, ASTs;

synthesized attribute originLoc::Location occurs on AST;
synthesized attribute indent::Integer occurs on AST;
flowtype indent {lineIndent} on AST;
monoid attribute indents::[Integer] occurs on ASTs, AST;
propagate indents on ASTs, AST;
flowtype indents {lineIndent} on AST, ASTs;
synthesized attribute isBox::Boolean occurs on AST;
synthesized attribute origNest::Integer occurs on ASTs;
synthesized attribute origLayoutPP::Document occurs on ASTs;

-- Attributes computed on the unparse AST
inherited attribute parseTree<a>::Maybe<a>;  -- This is like a destruct attribute except it's a Maybe
attribute parseTree<Decorated AST with {origText, lineIndent, initialIndent}> occurs on AST;
attribute parseTree<Decorated ASTs with {origText, lineIndent, initialIndent}> occurs on ASTs;

synthesized attribute unparseWithLayout::Document occurs on AST, ASTs;
synthesized attribute defaultPreLayout::Maybe<Document> occurs on AST, ASTs;
synthesized attribute defaultPostLayout::Maybe<Document> occurs on AST, ASTs;
inherited attribute childIndex::Integer occurs on ASTs;
inherited attribute childLayout::[(Integer, Document)] occurs on ASTs;
inherited attribute childIndent::[(Integer, Integer)] occurs on ASTs;
inherited attribute childGroup::[(Integer, Integer)] occurs on ASTs;
propagate childLayout, childIndent, childGroup on ASTs;

inherited attribute currentGroup::Maybe<Integer> occurs on ASTs;
synthesized attribute groupUnparse::Document occurs on ASTs;

aspect default production
top::AST ::=
{
  top.originLoc = error(genericShow(top) ++ " cannot appear in a parse tree");
  top.indent =
    case map:lookup(top.originLoc.line - 1, top.lineIndent) of
    | i :: _ -> i
    | [] -> error(s"Line ${toString(top.originLoc.line)} out of bounds for supplied text!")
    end;
  top.indents <- [top.indent];
  top.isBox = false;
  top.unparseWithLayout = error("Can't unparse " ++ genericShow(top));
  top.defaultPreLayout = nothing();
  top.defaultPostLayout = nothing();
}

aspect production nonterminalAST
top::AST ::= prodName::String children::ASTs annotations::NamedASTs
{
  -- On parseTree
  top.originLoc =
    case getParsedOriginLocation(top) of
    | just(l) -> l
    | nothing() -> error("Tree does not have a parsed origin: " ++ showOriginInfoChain(top))
    end;
  top.isBox =
    top.originLoc.endLine > top.originLoc.line &&
    all(map(\ i::Integer -> i == top.indent || i >= top.originLoc.column, children.indents));
  children.initialIndent = if top.isBox then top.originLoc.column else top.initialIndent;

  -- On unparse AST
  top.unparseWithLayout =
    if fromMaybe(false, map((.isBox), top.parseTree))
    then box(children.unparseWithLayout)
    else children.unparseWithLayout;

  local parseTree::AST = getParseTree(top);
  parseTree.origText = top.origText;
  parseTree.lineIndent = top.lineIndent;
  parseTree.initialIndent = parseTree.indent;
  children.parseTree =
    case fromMaybe(parseTree, top.parseTree) of
    | nonterminalAST(p, c, _) when prodName == p -> just(c)
    | _ -> nothing()
    end;
  top.defaultPreLayout = children.defaultPreLayout;
  top.defaultPostLayout = children.defaultPostLayout;

  children.childIndex = 0;

  -- Map of productions and child indices to default layout after the child
  production attribute prodChildLayout::[(String, Integer, Document)] with ++;
  prodChildLayout := [];
  children.childLayout = lookupAll(prodName, prodChildLayout);

  -- Map of productions and child indices to default indentation in the child
  production attribute prodChildIndent::[(String, Integer, Integer)] with ++;
  prodChildIndent := [];
  children.childIndent = lookupAll(prodName, prodChildIndent);

  -- Map of productions to start/end indices of children that should be grouped
  production attribute prodChildGroup::[(String, Integer, Integer)] with ++;
  prodChildGroup := [];
  children.childGroup = lookupAll(prodName, prodChildGroup);
  children.currentGroup = nothing();
}

aspect production terminalAST
top::AST ::= terminalName::String lexeme::String location::Location
{
  top.originLoc = location;

  -- If there is a *syntactic* newline, then force anything enclosing this to not be boxed.
  top.indents <- if indexOf("\n", lexeme) != -1 then [-1] else [];

  top.unparseWithLayout = blobPP(top.indent, lexeme);

  -- Map of terminal names to default layout after the terminal
  production attribute termPreLayout::[(String, Document)] with ++;
  termPreLayout := [];
  -- Map of terminal names to default layout before the terminal
  production attribute termPostLayout::[(String, Document)] with ++;
  termPostLayout := [];

  top.defaultPreLayout = lookup(terminalName, termPreLayout);
  top.defaultPostLayout = lookup(terminalName, termPostLayout);
}

aspect production consAST
top::ASTs ::= h::AST t::ASTs
{
  -- On parseTree
  top.origLayoutPP =
    case t of
    | consAST(h2, _) ->
        blobPP(h2.indent,
          substring(h.originLoc.endIndex, h2.originLoc.index, top.origText))
    | nilAST() -> pp""
    end;
  top.origNest =
    case t of
    | consAST(h2, _) when h2.originLoc.line > h.originLoc.line ->
      h2.indent - top.initialIndent
    | _ -> 0
    end;
  h.initialIndent = top.initialIndent;
  t.initialIndent =
    case t of
    | consAST(h2, _) when h2.originLoc.line > h.originLoc.line -> h2.indent
    | _ -> top.initialIndent
    end;

  -- On unparse AST
  h.parseTree =
    case top.parseTree of
    | just(consAST(a, _)) -> just(a)
    | _ -> nothing()
    end;
  t.parseTree =
    case top.parseTree of
    | just(consAST(_, a)) -> just(a)
    | _ -> nothing()
    end;
  top.defaultPreLayout = h.defaultPreLayout;
  top.defaultPostLayout = alt(
    t.defaultPostLayout,
    case t of nilAST() -> h.defaultPostLayout | _ -> empty end);
  t.childIndex = top.childIndex + 1;

  local nestAmount::Integer =
    fromMaybe(0,
      alt(map((.origNest), top.parseTree),
        lookup(t.childIndex, top.childIndent)));
  nondecorated local thisLayout::Document =
    fromMaybe(pp"",
      alt(map((.origLayoutPP), top.parseTree),
        alt(lookup(top.childIndex, top.childLayout),
          alt(case t of consAST(_, _) -> h.defaultPostLayout | _ -> empty end,
            t.defaultPreLayout))));

  -- These should be mutually exclusive:
  local endGroup::Boolean = top.currentGroup == just(top.childIndex);
  local inGroup::Maybe<Integer> = if endGroup then empty else top.currentGroup;
  local newGroup::Maybe<Integer> = lookup(top.childIndex, top.childGroup);
  t.currentGroup =
    if top.currentGroup.isJust && newGroup.isJust
    then error("Overlapping groups!")
    else alt(inGroup, newGroup);
  top.unparseWithLayout =
    if t.currentGroup.isJust
    then
      (if newGroup.isJust then group(top.groupUnparse) else pp"") ++
      maybeNest(nestAmount, t.unparseWithLayout)
    else
      (if endGroup then pp"" else h.unparseWithLayout) ++
      maybeNest(nestAmount, thisLayout ++ t.unparseWithLayout);
  top.groupUnparse =
    h.unparseWithLayout ++
    if endGroup then pp"" else maybeNest(nestAmount, thisLayout ++ t.groupUnparse);
}

aspect production nilAST
top::ASTs ::=
{
  top.origLayoutPP = pp"";
  top.origNest = 0;

  top.unparseWithLayout = pp"";
  top.groupUnparse = error("Group end index ${toString(top.currentGroup.fromJust)} out of bounds");
  top.defaultPreLayout = nothing();
  top.defaultPostLayout = nothing();
}

-- Count the number of spaces at the start of a line
fun countIndent  Integer ::= s::String = length(takeWhile(eq(" ", _), explode("", s)));

fun blobPP  Document ::= indent::Integer str::String =
  concat(
    case explode("\n", str) of
    | [] -> []
    | pre :: lines -> text(pre) ::
        map(\ l::String ->
          maybeNest(
            countIndent(l) - indent,
            realLine() ++ text(concat(dropWhile(eq(" ", _), explode("", l))))),
          lines)
    end);

fun maybeNest  Document ::= n::Integer d::Document = if n == 0 then d else nest(n, d);
