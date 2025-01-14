grammar silver:util:rbt:multimap;

nonterminal MultiMapEntry<k v>;

instance Eq k => Eq MultiMapEntry<k v> {
  eq = \l::MultiMapEntry<k v>  r::MultiMapEntry<k v> ->
    case l, r of
    | mapEntry(lk, _), mapEntry(rk, _) -> eq(lk, rk)
    end;
}

instance Ord k => Ord MultiMapEntry<k v> {
  compare = \l::MultiMapEntry<k v>  r::MultiMapEntry<k v> ->
    case l, r of
    | mapEntry(lk, _), mapEntry(rk, _) -> compare(lk, rk)
    end;
}

abstract production mapEntry
top::MultiMapEntry<k v> ::= key::k  value::v
{}
