grammar silver:core;

@{-
Monads support both lifting functions/values of arbitrary arity and sequential compostion.

Instances should satisfy the following:

Left Identity
  bind(pure(x), f) = f(x)
Right Identity
  bind(x, pure) = x
-}
class Applicative m, Bind m => Monad m {}

-- Prefer `fmap` to this function. However, it can be useful to get a `Functor`
-- instance for free, given an existing `Monad` instance.
fun liftM1 Monad m => m<b> ::= f::(b ::= a)  x::m<a> = bind(x, \x::a -> pure(f(x)));

-- Prefer `ap` to this function. However, it can be useful to get an
-- `Applicative` instance for free, given an existing `Monad` instance.
fun apM Monad m => m<b> ::= f::m<(b ::= a)>  x::m<a> =
  bind(f, \f::(b ::= a) -> bind(x, \x::a -> pure(f(x))));

fun whenM Monad m => m<Unit> ::= cond::m<Boolean>  body::m<Unit> = bind(cond, when_(_, body));

fun unlessM Monad m => m<Unit> ::= cond::m<Boolean>  body::m<Unit> = bind(cond, unless(_, body));

fun doWhile_ Monad m => m<Unit> ::= cond::m<Boolean> = whenM(cond, doWhile_(cond));

fun doUntil_ Monad m => m<Unit> ::= cond::m<Boolean> = unlessM(cond, doUntil_(cond));

@{-
Monads that support failure with an error message.

Instances should satisfy the following:

Annihilation
  bind(fail(s), f) = fail(s)
-}
class Monad m => MonadFail m {
  fail :: (m<a> ::= String);
}

@{-
The MonadZero type class has no members of its own; it just specifies that the type has both Monad and Alternative instances.

Instances should satisfy the following:

Annihilation
  bind(empty, f) = empty
-}
class Monad m, Alternative m => MonadZero m {}

@{-
The MonadPlus type class has no members of its own; it just extends MonadZero with an additional law.

Instances should satisfy the following:

Distributivity
  bind(alt(x, y), f) = alt(bind(x, f), bind(y, f))
-}
class MonadZero m, Alternative m => MonadPlus m {}

@{-
Monads having fixed points with a 'knot-tying' semantics.

Instances should satisfy the following:

Purity
  mfix(compose(pure, h)) = pure(fix(h))

Left shrinking (or Tightening)
  mfix(\x -> bind(a, \y -> f(x, y))) = bind(a, \y -> mfix(\x -> f(x, y)))

Sliding
  mfix(compose(map(h, _), f)) = map(h, (mfix(compose(f, h)))), for strict h.

Nesting
  mfix(\x -> mfix(\y -> f(x, y))) = mfix(\x -> f(x, x))
-}
class Monad m => MonadFix m {
  mfix :: (m<a> ::= (m<a> ::= a));
}

@{-
Monad transformers lift a monadic computation into an additional monad.

Instances should satisfy the following:
  compose(lift, pure) = pure
  lift(bind(m, f)) = bind(lift(m), compose(lift, f))
-}
class MonadTrans (t :: (* -> *) -> * -> *) {
  lift :: Monad m => (t<m a> ::= m<a>);
}

@{-
Can be used to extract the monadic value from a MonadTrans instance value.
 -}
synthesized attribute run<a>::a;
