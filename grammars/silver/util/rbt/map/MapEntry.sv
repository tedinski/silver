grammar silver:util:rbt:map;

-- TODO: Replace reorderedLte in
-- grammars/silver/compiler/definition/core/Expr.sv with this?
nonterminal MapEntry<k v>;

instance Eq k => Eq MapEntry<k v> {
  eq = \l::MapEntry<k v>  r::MapEntry<k v> ->
    case l, r of
    | mapEntry(lk, _), mapEntry(rk, _) -> eq(lk, rk)
    end;
}

instance Ord k => Ord MapEntry<k v> {
  compare = \l::MapEntry<k v>  r::MapEntry<k v> ->
    case l, r of
    | mapEntry(lk, _), mapEntry(rk, _) -> compare(lk, rk)
    end;
}

abstract production mapEntry
top::MapEntry<k v> ::= key::k  value::v
{}
