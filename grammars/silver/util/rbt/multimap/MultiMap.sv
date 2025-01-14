grammar silver:util:rbt:multimap;

import silver:util:rbt as rbt;

nonterminal MultiMap<k v>;

abstract production mkMultiMap
top::MultiMap<k v> ::= inner::rbt:RBT<MultiMapEntry<k v>>
{}

function empty
MultiMap<k v> ::=
{ return mkMultiMap(rbt:blackLeaf()); }

function singleton
MultiMap<k v> ::= key::k  value::v
{ return mkMultiMap(rbt:singleton(mapEntry(key, value))); }

function ofList
Ord k => MultiMap<k v> ::= lst::[Pair<k v>]
{
  return mkMultiMap(foldl(rbt:insert, rbt:blackLeaf(),
    map(\p::Pair<k v> -> mapEntry(p.fst, p.snd), lst)));
}

function toList
[Pair<k v>] ::= xs::MultiMap<k v>
{
  return case xs of
  | mkMultiMap(inner) -> map(
      \e::MultiMapEntry<k v> -> case e of
      | mapEntry(k, v) -> pair(k, v)
      end,
      rbt:toList(inner))
  end;
}

function delete
Ord k => MultiMap<k v> ::= xs::MultiMap<k v>  key::k
{
  return case xs of
  | mkMultiMap(inner) -> mkMultiMap(rbt:delete(inner, mapEntry(key, error("demanded value when deleting from map"))))
  end;
}

function size
Integer ::= xs::MultiMap<k v>
{
  return case xs of
  | mkMultiMap(inner) -> rbt:size(inner)
  end;
}

function insert
Ord k => MultiMap<k v> ::= xs::MultiMap<k v>  key::k  value::v
{
  return case xs of
  | mkMultiMap(inner) -> mkMultiMap(rbt:insert(inner, mapEntry(key, value)))
  end;
}

function lookup
Ord k => Maybe<v> ::= xs::MultiMap<k v>   key::k
{
  return case xs of
  | mkMultiMap(inner) ->
      case rbt:member(inner, mapEntry(key, error("demanded value when lookup up in map"))) of
      | just(mapEntry(_, v)) -> just(v)
      | nothing() -> nothing()
      end
  end;
}
