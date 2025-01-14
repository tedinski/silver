grammar silver:util:rbt;

-- Based on http://matt.might.net/articles/red-black-delete/

-- TODO: Should these all be functions?
synthesized attribute blacken<a>::RBT<a>;
synthesized attribute redden<a>::RBT<a>;
synthesized attribute blacker<a>::a;
synthesized attribute redder<a>::a;
synthesized attribute isDoubleBlack::Boolean;
nonterminal RBT<a> with blacken<a>, blacker<RBT<a>>, isDoubleBlack, redden<a>, redder<RBT<a>>;

abstract production blackLeaf
top::RBT<a> ::=
{
  top.blacken = blackLeaf();
  top.blacker = doubleBlackLeaf();
  top.isDoubleBlack = false;
  top.redden = error("Cannot redden leaf");
  top.redder = error("Cannot make black leaf redder");
}

abstract production doubleBlackLeaf
top::RBT<a> ::=
{
  top.blacken = blackLeaf();
  top.blacker = error("Cannot make double black leaf blacker");
  top.isDoubleBlack = true;
  top.redden = error("Cannot redden double black leaf");
  top.redder = blackLeaf();
}

abstract production tree
top::RBT<a> ::= color::Color  l::RBT<a>  x::a  r::RBT<a>
{
  top.blacken = tree(black(), l, x, r);
  top.blacker = tree(color.blacker, l, x, r);
  top.isDoubleBlack =
    case color of
    | doubleBlack() -> true
    | _ -> false
    end;
  top.redden = tree(red(), l, x, r);
  top.redder = tree(color.redder, l, x, r);
}

function singleton
RBT<a> ::= value::a
{ return tree(black(), blackLeaf(), value, blackLeaf()); }

function balance
RBT<a> ::= color::Color  l::RBT<a>  x::a  r::RBT<a>
{
  return case color, l, x, r of
  -- Okasaki
  | black(), tree(red(), tree(red(), a, x, b), y, c), z, d ->
      tree(red(), tree(black(), a, x, b), y, tree(black(), c, z, d))
  | black(), tree(red(), a, x, tree(red(), b, y, c)), z, d ->
      tree(red(), tree(black(), a, x, b), y, tree(black(), c, z, d))
  | black(), a, x, tree(red(), tree(red(), b, y, c), z, d) ->
      tree(red(), tree(black(), a, x, b), y, tree(black(), c, z, d))
  | black(), a, x, tree(red(), b, y, tree(red(), c, z, d)) ->
      tree(red(), tree(black(), a, x, b), y, tree(black(), c, z, d))
  -- Might
  | doubleBlack(), tree(red(), tree(red(), a, x, b), y, c), z, d ->
      tree(black(), tree(black(), a, x, b), y, tree(black(), c, z, d))
  | doubleBlack(), tree(red(), a, x, tree(red(), b, y, c)), z, d ->
      tree(black(), tree(black(), a, x, b), y, tree(black(), c, z, d))
  | doubleBlack(), a, x, tree(red(), tree(red(), b, y, c), z, d) ->
      tree(black(), tree(black(), a, x, b), y, tree(black(), c, z, d))
  | doubleBlack(), a, x, tree(red(), b, y, tree(red(), c, z, d)) ->
      tree(black(), tree(black(), a, x, b), y, tree(black(), c, z, d))
  | doubleBlack(), a, x, tree(negativeBlack(), tree(black(), b, y, c), z, tree(black(), dl, dx, dr)) ->
      tree(black(), tree(black(), a, x, b), y, balance(black(), c, z, tree(red(), dl, dx, dr)))
  | doubleBlack(), tree(negativeBlack(), tree(black(), al, ax, ar), x, tree(black(), b, y, c)), z, d ->
      tree(black(), balance(black(), tree(red(), al, ax, ar), x, b), y, tree(black(), c, z, d))
  -- Fallback
  | color, l, x, r -> tree(color, l, x, r)
  end;
}

function bubble
RBT<a> ::= color::Color  l::RBT<a>  x::a  r::RBT<a>
{
  return
    if l.isDoubleBlack || r.isDoubleBlack then
      balance(color.blacker, l.redder, x, r.redder)
    else
      balance(color, l, x, r);
}

function delete
Ord a => RBT<a> ::= xs::RBT<a>  x::a
{
  return deleteHelper(x, xs).blacken;
}

function deleteHelper
Ord a => RBT<a> ::= x::a  xs::RBT<a>
{
  return case xs of
  | blackLeaf() -> blackLeaf()
  | doubleBlackLeaf() -> error("cannot delete from double black leaf")
  | tree(color, l, y, r) ->
      let compareResult::Integer = compare(x, y) in
        if compareResult < 0 then
          bubble(color, deleteHelper(x, l), y, r)
        else if compareResult == 0 then
          remove(xs)
        else
          bubble(color, l, y, deleteHelper(x, r))
      end
  end;
}

function insert
Ord a => RBT<a> ::= xs::RBT<a>  x::a
{
  return insertHelper(x, xs).blacken;
}

function insertHelper
Ord a => RBT<a> ::= x::a  xs::RBT<a>
{
  return case xs of
  | blackLeaf() -> tree(red(), blackLeaf(), x, blackLeaf())
  | doubleBlackLeaf() -> error("cannot insert to double black leaf")
  | tree(color, l, y, r) ->
      let compareResult::Integer = compare(x, y) in
        if compareResult < 0 then
          balance(color, insertHelper(x, l), y, r)
        else if compareResult == 0 then
          tree(color, l, x, r)
        else
          balance(color, l, y, insertHelper(x, r))
      end
  end;
}

-- _NOT_ an interface function (because it's partial on well-formed trees).
function max
a ::= xs::RBT<a>
{
  return case xs of
  | blackLeaf() -> error("cannot find max of leaf")
  | doubleBlackLeaf() -> error("cannot find max of double black leaf")
  | tree(_, _, x, blackLeaf()) -> x
  | tree(_, _, _, r) -> max(r)
  end;
}

function member
Ord a => Maybe<a> ::= xs::RBT<a>  x::a
{
  return case xs of
  | blackLeaf() -> nothing()
  | doubleBlackLeaf() -> error("cannot find member on double black leaf")
  | tree(_, l, y, r) ->
      let compareResult::Integer = compare(x, y) in
        if compareResult < 0 then
          member(l, x)
        else if compareResult == 0 then
          just(y)
        else
          member(r, x)
      end
  end;
}

function remove
RBT<a> ::= xs::RBT<a>
{
  return case xs of
  | blackLeaf() -> blackLeaf()
  | doubleBlackLeaf() -> error("cannot remove double black leaf")
  | tree(red(), blackLeaf(), _, blackLeaf()) -> blackLeaf()
  | tree(black(), blackLeaf(), _, blackLeaf()) -> doubleBlackLeaf()
  | tree(black(), blackLeaf(), _, tree(red(), l, x, r)) -> tree(black(), l, x, r)
  | tree(black(), tree(red(), l, x, r), _, blackLeaf()) -> tree(black(), l, x, r)
  | tree(color, l, _, r) -> bubble(color, removeMax(l), max(l), r)
  end;
}

function removeMax
RBT<a> ::= xs::RBT<a>
{
  return case xs of
  | blackLeaf() -> error("cannot remove max of leaf")
  | doubleBlackLeaf() -> error("cannot remove max of double black leaf")
  | tree(_, _, _, blackLeaf()) -> remove(xs)
  | tree(color, l, x, r) -> bubble(color, l, x, removeMax(r))
  end;
}

function size
Integer ::= xs::RBT<a>
{
  return case xs of
  | blackLeaf() -> 0
  | doubleBlackLeaf() -> error("cannot take size of double black leaf")
  | tree(_, l, _, r) -> size(l) + 1 + size(r)
  end;
}

function toList
[a] ::= xs::RBT<a>
{
  return toListHelper(xs, []);
}

function toListHelper
[a] ::= xs::RBT<a>  suffix::[a]
{
  return case xs of
  | blackLeaf() -> suffix
  | doubleBlackLeaf() -> error("cannot convert double black leaf to list")
  | tree(_, l, x, r) -> toListHelper(l, x :: toListHelper(r, suffix))
  end;
}

nonterminal Color with blacker<Color>, redder<Color>;

abstract production doubleBlack
top::Color ::=
{
  top.blacker = error("There's no color darker than double black!");
  top.redder = black();
}

abstract production black
top::Color ::=
{
  top.blacker = doubleBlack();
  top.redder = red();
}

abstract production red
top::Color ::=
{
  top.blacker = black();
  top.redder = negativeBlack();
}

abstract production negativeBlack
top::Color ::=
{
  top.blacker = red();
  top.redder = error("There's no color redder than negative black!");
}
