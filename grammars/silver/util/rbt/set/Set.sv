grammar silver:util:rbt:set;

import silver:util:rbt as rbt;

nonterminal Set<a>;

abstract production mkSet
top::Set<a> ::= inner::rbt:RBT<a>
{}

instance Eq a => Eq Set<a> { eq = \l::Set<a>  r::Set<a> -> toList(l) == toList(r); }
instance Ord a => Ord Set<a> { compare = \l::Set<a>  r::Set<a> -> compare(toList(l), toList(r)); }
instance Ord a => Semigroup Set<a> { append = union; }
instance Ord a => Monoid Set<a> { silver:core:empty = empty(); }

function setFoldMap
Monoid m => m ::= f::(m ::= a)  xs::Set<a>
{
  return error("TODO");
}



function empty
Set<a> ::=
{ return mkSet(rbt:blackLeaf()); }

function singleton
Set<a> ::= value::a
{ return mkSet(rbt:singleton(value)); }

function ofList
Ord a => Set<a> ::= lst::[a]
{
  return mkSet(foldl(rbt:insert, rbt:blackLeaf(), lst));
}

function toList
[a] ::= xs::Set<a>
{
  return case xs of
  | mkSet(inner) -> rbt:toList(inner)
  end;
}

function delete
Ord a => Set<a> ::= xs::Set<a>  x::a
{
  return case xs of
  | mkSet(inner) -> mkSet(rbt:delete(inner, x))
  end;
}

function map
Ord b => Set<b> ::= f::(b ::= a)  xs::Set<a>
{ return ofList(silver:core:map(f, toList(xs))); }

function size
Integer ::= xs::Set<a>
{
  return case xs of
  | mkSet(inner) -> rbt:size(inner)
  end;
}

function insert
Ord a => Set<a> ::= xs::Set<a>  x::a
{
  return case xs of
  | mkSet(inner) -> mkSet(rbt:insert(inner, x))
  end;
}

function member
Ord a => Boolean ::= xs::Set<a>   x::a
{
  return case xs of
  | mkSet(inner) -> rbt:member(inner, x).isJust
  end;
}

-- TODO: The functions below this line can be made more efficient with join/split, see
-- https://en.wikipedia.org/wiki/Red-black_tree#Set_operations_and_bulk_operations

function difference
Ord a => Set<a> ::= l::Set<a>  r::Set<a>
{
  return
    if size(l) < size(r) then
      difference(r, l)
    else
      foldl(delete, l, toList(r));
}

function intersection
Ord a => Set<a> ::= l::Set<a>  r::Set<a>
{
  return case l of
  | mkSet(_) ->
      ofList(filter(member(l, _), filter(member(r, _), toList(union(l, r)))))
  end;
}

function union
Ord a => Set<a> ::= l::Set<a>  r::Set<a>
{
  return
    if size(l) < size(r) then
      union(r, l)
    else
      foldl(insert, l, toList(r));
}
