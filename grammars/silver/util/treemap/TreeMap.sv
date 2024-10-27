grammar silver:util:treemap;

@@{-
   - One should always import this via 'import silver:util:treemap as ...'
   - The names are too general otherwise.
   -}

type Map<a b> foreign = "java.util.TreeMap<Object,common.ConsCell>";

@{--
 - Returns a new, empty, multimap using Ord for comparison.
 -}
fun empty Ord a => Map<a b> ::= = emptyWith(compare);

@{--
 - Returns a new, empty, multimap using the specified comparator.
 -}
function emptyWith
Map<a b> ::= comparator::(Integer ::= a a)
{
  return error("NYI");
} foreign {
  "java" : return "common.rawlib.RawTreeMap.empty(%comparator%)";
}

@@{- @warning An 'insert' function is deliberating omitted due to its inefficiency, but there's add: -}

@{--
 - Adds a list of elements to a map.
 -}
function add
Map<a b> ::= lst::[Pair<a b>] mp::Map<a b>
{
  return error("NYI");
} foreign {
  "java" : return "common.rawlib.RawTreeMap.addList(%lst%, %mp%)";
}

@{--
 - Returns a list of keys that are present in the map, in sorted order.
 -}
function keys
[a] ::= mp::Map<a b>
{
  return error("NYI");
} foreign {
  "java" : return "common.rawlib.RawTreeMap.keys(%mp%)";
}

@{--
 - Returns a list of values that are present in the map, in key sorted order.
 -}
fun values [b] ::= mp::Map<a b> = map(snd, toList(mp));

@{--
 - Looks up an element from the map, empty list if not contained.
 -}
function lookup
[b] ::= key::a mp::Map<a b>
{
  return error("NYI");
} foreign {
  "java" : return "common.rawlib.RawTreeMap.lookup(%key%, %mp%)";
}

@{--
 - Converts a list of pairs to a multimap.
 -}
fun fromList Ord a => Map<a b> ::= l::[Pair<a b>] = add(l, empty());

@{--
 - Converts a multimap back to a list of pairs, in sorted order by key.
 -}
function toList
[Pair<a b>] ::= mp::Map<a b>
{
  return error("NYI");
} foreign {
  "java" : return "common.rawlib.RawTreeMap.toList(%mp%)";
}

@{--
 - Updates the value returned by a key
 -}
function update
Map<a b> ::= key::a  value::[b]  mp::Map<a b>
{
  return error("NYI");
} foreign {
  "java" : return "common.rawlib.RawTreeMap.update(%key%, %value%, %mp%)";
}

instance Eq a, Eq b => Eq Map<a b> {
  -- TODO: This could be more efficient - eagerly converting both maps to lists before comparison.
  eq = \ m1::Map<a b> m2::Map<a b> -> toList(m1) == toList(m2);
}

instance Ord a, Ord b => Ord Map<a b> {
  -- TODO: This could be more efficient - eagerly converting both maps to lists before comparison.
  compare = \ m1::Map<a b> m2::Map<a b> -> compare(toList(m1), toList(m2));
}
