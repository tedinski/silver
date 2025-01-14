grammar silver:util:rbt:map;

import silver:util:rbt as rbt;

nonterminal Map<k v>;

abstract production mkMap
top::Map<k v> ::= inner::rbt:RBT<MapEntry<k v>>
{}

function empty
Map<k v> ::=
{ return mkMap(rbt:blackLeaf()); }

function singleton
Map<k v> ::= key::k  value::v
{ return mkMap(rbt:singleton(mapEntry(key, value))); }

function ofList
Ord k => Map<k v> ::= lst::[Pair<k v>]
{
  return mkMap(foldl(rbt:insert, rbt:blackLeaf(),
    map(\p::Pair<k v> -> mapEntry(p.fst, p.snd), lst)));
}

function toList
[Pair<k v>] ::= xs::Map<k v>
{
  return case xs of
  | mkMap(inner) -> map(
      \e::MapEntry<k v> -> case e of
      | mapEntry(k, v) -> pair(k, v)
      end,
      rbt:toList(inner))
  end;
}

function delete
Ord k => Map<k v> ::= xs::Map<k v>  key::k
{
  return case xs of
  | mkMap(inner) -> mkMap(rbt:delete(inner, mapEntry(key, error("demanded value when deleting from map"))))
  end;
}

function size
Integer ::= xs::Map<k v>
{
  return case xs of
  | mkMap(inner) -> rbt:size(inner)
  end;
}

function insert
Ord k => Map<k v> ::= xs::Map<k v>  key::k  value::v
{
  return case xs of
  | mkMap(inner) -> mkMap(rbt:insert(inner, mapEntry(key, value)))
  end;
}

function lookup
Ord k => Maybe<v> ::= xs::Map<k v>   key::k
{
  return case xs of
  | mkMap(inner) ->
      case rbt:member(inner, mapEntry(key, error("demanded value when lookup up in map"))) of
      | just(mapEntry(_, v)) -> just(v)
      | nothing() -> nothing()
      end
  end;
}
