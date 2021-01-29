grammar silver:core;

{-
The Alt type class identifies an associative operation on a type constructor.
It is similar to Semigroup, except that it applies to types of kind arity 1,
like Maybe or [], rather than concrete types String or [a].

Instances should satisfy the following:

Associativity
  alt(alt(x, y), z) == alt(x, alt(y, z))
Distributivity
  map(f, alt(x, y)) == alt(map(f, x), map(f, y))
-}
class Functor f => Alt f {
  alt :: (f<a> ::= f<a> f<a>);
}

instance Alt List {
  alt = append;
}

instance Alt Maybe {
  alt = orElse;
}

instance Alt Either<a _> {
  alt = \ e1::Either<a b> e2::Either<a b> ->
    case e1, e2 of
    | right(x), _ -> right(x)
    | _, right(x) -> right(x)
    -- If they're both left, arbitrarily take the first one
    | _, _ -> e1
    end;
}

{-
The Plus type class extends the Alt type class with a value that should be the
left and right identity for (<|>).

It is similar to Monoid, except that it applies to types of kind arity 1,
like Array or List, rather than concrete types like String or Number.

Instances should satisfy the following laws:

Left identity
  alt(empty, x) == x
Right identity
  alt(x, empty) == x
Annihilation
  map(f, empty) == empty
-}
class Alt f => Plus f {
  empty :: f<a>;
}

instance Plus [] {
  empty = [];
}

instance Plus Maybe {
  empty = nothing();
}

{-
The Alternative class is for members of Plus that are also Applicative functors,
and specifies some additional laws:

Distributivity
  ap(alt(f, g), x) == alt(ap(f, x), ap(g, x))
Annihilation
  ap(empty, x) = empty
-}
class Applicative f, Plus f => Alternative f {}

instance Alternative [] {}
instance Alternative Maybe {}

