grammar silver:core;

fun id a ::= x::a = x;

fun compose (c ::= a) ::= f1::(c ::= b) f2::(b ::= a) = \ x::a -> f1(f2(x));

-- We need specialized versions of all the below utilities, as functions in Silver are not curried.

fun curry ((c ::= b) ::= a) ::= f::(c ::= a b) = \x::a -> \y::b -> f(x, y);

fun curry3 (((d ::= c) ::= b) ::= a) ::= f::(d ::= a b c) = \x::a -> \y::b -> \z::c -> f(x, y, z);

fun curry4 ((((e ::= d) ::= c) ::= b) ::= a) ::= f::(e ::= a b c d) =
  \x::a -> \y::b -> \z::c -> \p::d -> f(x, y, z, p);

fun curry5 (((((f ::= e) ::= d) ::= c) ::= b) ::= a) ::= f::(f ::= a b c d e) =
  \x::a -> \y::b -> \z::c -> \p::d -> \q::e -> f(x, y, z, p, q);

fun uncurry c ::= f::((c ::= b) ::= a)  x::a  y::b = f(x)(y);

fun uncurry3 d ::= f::(((d ::= c) ::= b) ::= a)  x::a  y::b  z::c = f(x)(y)(z);

fun uncurry4 e ::= f::((((e ::= d) ::= c) ::= b) ::= a)  x::a  y::b  z::c  p::d = f(x)(y)(z)(p);

fun uncurry5 f ::= f::(((((f ::= e) ::= d) ::= c) ::= b) ::= a)  x::a  y::b  z::c  p::d  q::e =
  f(x)(y)(z)(p)(q);

instance Functor (_ ::= ) {
  map = \ fn::(b ::= a) x::(a ::= ) -> \ -> fn(x());
}
instance Apply (_ ::= ) {
  ap = \ fn::((b ::= a) ::= ) x::(a ::= ) -> \ -> fn()(x());
}
instance Applicative (_ ::= ) {
  pure = \ x::a -> \ -> x;
}
instance Semigroup a => Semigroup (a ::= ) {
  append = lift2(append, _, _);
}
instance Monoid a => Monoid (a ::= ) {
  mempty = pure(mempty);
}

instance Functor (_ ::= c) {
  map = \ fn::(b ::= a) x::(a ::= c) -> \ c::c -> fn(x(c));
}
instance Apply (_ ::= c) {
  ap = \ fn::((b ::= a) ::= c) x::(a ::= c) -> \ c::c -> fn(c)(x(c));
}
instance Applicative (_ ::= c) {
  pure = \ x::a -> \ _::c -> x;
}
instance Semigroup a => Semigroup (a ::= c) {
  append = lift2(append, _, _);
}
instance Monoid a => Monoid (a ::= c) {
  mempty = pure(mempty);
}

instance Functor (_ ::= c d) {
  map = \ fn::(b ::= a) x::(a ::= c d) -> \ c::c d::d -> fn(x(c, d));
}
instance Apply (_ ::= c d) {
  ap = \ fn::((b ::= a) ::= c d) x::(a ::= c d) -> \ c::c d::d -> fn(c, d)(x(c, d));
}
instance Applicative (_ ::= c d) {
  pure = \ x::a -> \ _::c _::d -> x;
}
instance Semigroup a => Semigroup (a ::= c d) {
  append = lift2(append, _, _);
}
instance Monoid a => Monoid (a ::= c d) {
  mempty = pure(mempty);
}

instance Functor (_ ::= c d e) {
  map = \ fn::(b ::= a) x::(a ::= c d e) -> \ c::c d::d e::e -> fn(x(c, d, e));
}
instance Apply (_ ::= c d e) {
  ap = \ fn::((b ::= a) ::= c d e) x::(a ::= c d e) -> \ c::c d::d e::e -> fn(c, d, e)(x(c, d, e));
}
instance Applicative (_ ::= c d e) {
  pure = \ x::a -> \ _::c _::d _::e -> x;
}
instance Semigroup a => Semigroup (a ::= c d e) {
  append = lift2(append, _, _);
}
instance Monoid a => Monoid (a ::= c d e) {
  mempty = pure(mempty);
}

instance Functor (_ ::= c d e f) {
  map = \ fn::(b ::= a) x::(a ::= c d e f) -> \ c::c d::d e::e f::f -> fn(x(c, d, e, f));
}
instance Apply (_ ::= c d e f) {
  ap = \ fn::((b ::= a) ::= c d e f) x::(a ::= c d e f) -> \ c::c d::d e::e f::f -> fn(c, d, e, f)(x(c, d, e, f));
}
instance Applicative (_ ::= c d e f) {
  pure = \ x::a -> \ _::c _::d _::e _::f -> x;
}
instance Semigroup a => Semigroup (a ::= c d e f) {
  append = lift2(append, _, _);
}
instance Monoid a => Monoid (a ::= c d e f) {
  mempty = pure(mempty);
}

instance Functor (_ ::= c d e f g) {
  map = \ fn::(b ::= a) x::(a ::= c d e f g) -> \ c::c d::d e::e f::f g::g -> fn(x(c, d, e, f, g));
}
instance Apply (_ ::= c d e f g) {
  ap = \ fn::((b ::= a) ::= c d e f g) x::(a ::= c d e f g) -> \ c::c d::d e::e f::f g::g -> fn(c, d, e, f, g)(x(c, d, e, f, g));
}
instance Applicative (_ ::= c d e f g) {
  pure = \ x::a -> \ _::c _::d _::e _::f _::g -> x;
}
instance Semigroup a => Semigroup (a ::= c d e f g) {
  append = lift2(append, _, _);
}
instance Monoid a => Monoid (a ::= c d e f g) {
  mempty = pure(mempty);
}
