grammar silver:compiler:extension:do_notation;

concrete production do_c
top::Expr ::= 'do' '{' body::DoBody '}'
{
  top.unparse = s"do {${body.unparse}}";
  propagate frame;

  forwards to body.transform;
}

{-
  Like do, but rewrites mutually recursive bindings using mfix.
  For example
    mdo {
      x :: Integer <- something;
      let y :: Boolean = bar(x, z);
      z :: Expr <- baz(y);
      thing(y);
      return z;
    }
  would transform into
    do {
      x :: Integer <- something;
      _rec_items_123 :: (Boolean, Expr) <-
        mfix(\ _rec_items_123 :: (Boolean, Expr) ->
          do {
            let y :: Boolean = _rec_items_123.1;
            let z :: Expr = _rec_items_123.2;
            let y :: Boolean = bar(x, z);
            z :: Expr <- baz(y);
          });
      let y :: Boolean = _rec_items_123.1;
      let z :: Expr = _rec_items_123.2;
      thing(y);
      return z;
    }
  See https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/recursive_do.html#the-mdo-notation
-}
concrete production mdo_c
top::Expr ::= 'mdo' '{' body::DoBody '}'
{
  top.unparse = s"mdo {${body.unparse}}";
  propagate frame;

  body.boundVarEnv = mempty;
  body.allBoundVars = body.boundVars;
  body.recVars = mempty;
  body.recRes = error("First binding cannot have unbound vars");

  forwards to do_c('do', '{', body.mdoTransform, '}');
}

-- The set of variables that have been bound within this do body so far
inherited attribute boundVarEnv::ts:Set<String>;
-- The set of all variables that will be bound within this do body
inherited attribute allBoundVars::ts:Set<String>;
-- The set of variables that are bound within a binding
monoid attribute boundVars::ts:Set<String>;
-- The set of free variables contained in bindings
synthesized attribute bindingFreeVars::ts:Set<String>;

-- Can this do body be translated using ap/map instead of bind
synthesized attribute isApplicative::Boolean;
-- Parameter bindings that will be used in applicative translation
synthesized attribute appBindings::[LambdaRHSElem];
-- Expressions that will be bound in applicative translation
synthesized attribute appExprs::[Expr];
-- The final result in applicative translation
synthesized attribute appResult::Expr;

-- Translation of a do expression into function calls and lambdas,
-- threaded backwards through a do body
-- TODO: The way this is currently structured isn't amenable to using translation attributes.
inherited attribute transformIn::Expr;
synthesized attribute transform::Expr;

-- The set of variables in this segment (series of mutually-recursive bindings)
-- that refer to a future binding
inherited attribute recVars::ts:Set<String>;
-- Bindings in this segment that are referenced by a previous binding
synthesized attribute recBindings::[(String, TypeExpr)];
-- A do body returning a tuple of all rec bindings,
-- to be inserted at the end of the do body generated for a segment 
inherited attribute recRes::DoBody;
-- The do body generated for a segment 
synthesized attribute recBody::DoBody;
-- A transformation on a do body, wrapping segments in mfix
synthesized attribute mdoTransform::DoBody;

tracked nonterminal DoBody with
  unparse, frame, boundVarEnv, allBoundVars, boundVars, bindingFreeVars,
  isApplicative, appBindings, appExprs, appResult, transform,
  recVars, recBindings, recRes, recBody, mdoTransform;

tracked nonterminal DoBinding with
  unparse, frame, boundVars, freeVars,
  isApplicative, appBindings, appExprs,
  transform, transformIn,
  recBindings;

propagate frame, boundVars on DoBody, DoBinding;
propagate freeVars on DoBinding;


concrete production consDoBody
top::DoBody ::= b::DoBinding rest::DoBody
{
  top.unparse = s"${b.unparse} ${rest.unparse}";
  top.bindingFreeVars = b.freeVars ++ ts:difference(rest.bindingFreeVars, b.boundVars);
  top.isApplicative =
    b.isApplicative && ts:isEmpty(ts:intersect(b.boundVars, rest.bindingFreeVars)) &&
    rest.isApplicative;
  top.appBindings = b.appBindings ++ rest.appBindings;
  top.appExprs = b.appExprs ++ rest.appExprs;
  top.appResult = rest.appResult;

  rest.boundVarEnv = ts:union(b.boundVars, top.boundVarEnv);
  rest.allBoundVars = top.allBoundVars;

  b.transformIn = rest.transform;
  top.transform =
    if top.isApplicative
    then
      foldl(
        \ trans::Expr e::Expr -> mkStrFunctionInvocation("silver:core:ap", [trans, e]),
        mkStrFunctionInvocation("silver:core:map", [
          foldr(
            \ el::LambdaRHSElem trans::Expr ->
              lambdap(
                lambdaRHSCons(el, lambdaRHSNil()), trans),
            top.appResult, top.appBindings),
          head(top.appExprs)]),
        tail(top.appExprs))
    else b.transform;

  -- Variables in b that are bound in the enclosing do body, but have not yet been bound
  local newRecVars::ts:Set<String> =
    ts:difference(ts:intersect(b.freeVars, top.allBoundVars), top.boundVarEnv);
  -- All recursvely bound variables that have not yet been bound
  local allRecVars::ts:Set<String> = top.recVars ++ newRecVars;
  rest.recVars = ts:difference(allRecVars, b.boundVars);

  top.recBindings =
    b.recBindings ++
    if ts:isEmpty(rest.recVars) then [] else rest.recBindings;

  rest.recRes =
    if ts:isEmpty(top.recVars) && !ts:isEmpty(newRecVars)
    then
      finalReturnDoBody('return',
        foldr1(
          \ e1::Expr e2::Expr -> Silver_Expr { silver:core:pair(fst=$Expr{e1}, snd=$Expr{e2}) },
          map(\ item::(String, TypeExpr) -> Silver_Expr { $name{item.1} }, top.recBindings)),
        ';')
    else top.recRes;

  top.recBody = consDoBody(^b,
    if ts:isEmpty(rest.recVars)
    then rest.recRes
    else rest.recBody);

  local recVarName::String = s"_rec_items_${toString(genInt())}";
  nondecorated local recVarType::TypeExpr =
    foldr1(
      \ t1::TypeExpr t2::TypeExpr ->
        Silver_TypeExpr { silver:core:Pair<$TypeExpr{t1} $TypeExpr{t2}> },
      map(snd, top.recBindings));
  local wrapUnpackRecBindings::(DoBody ::= DoBody) =
    foldr(
      consDoBody(_, _),
      _,
      zipWith(
        \ i::Integer item::(String, TypeExpr) ->
          letDoBindingTy(
            'let', name(item.1), '::', item.2, '=',
            select(Silver_Expr { $name{recVarName} }, 1, i + 1, length(top.recBindings)), ';'),
        range(0, length(top.recBindings)),
        top.recBindings));
  top.mdoTransform =
    if !ts:isEmpty(top.recVars)
    then rest.mdoTransform
    else if !ts:isEmpty(newRecVars)
    then consDoBody(
      bindDoBindingTy(
        name(recVarName), '::', recVarType, '<-',
        Silver_Expr {
          mfix(
            \ $name{recVarName}::$TypeExpr{recVarType} ->
              $Expr{
                do_c('do', '{', wrapUnpackRecBindings(top.recBody), '}')
              })
        }, ';'),
      wrapUnpackRecBindings(rest.mdoTransform))
    else consDoBody(^b, rest.mdoTransform);
}


concrete production finalExprDoBody
top::DoBody ::= e::Expr ';'
{
  top.unparse = s"${e.unparse};";
  top.bindingFreeVars = mempty;
  top.isApplicative = false;
  top.appBindings = error("Not applicative");
  top.appExprs = error("Not applicative");
  top.appResult = error("Not applicative");
  top.transform = ^e;
  top.recBindings = [];
  top.recBody = top.recRes;
  top.mdoTransform = ^top;
}

concrete production finalReturnDoBody
top::DoBody ::= 'return' e::Expr ';'
{
  top.unparse = s"return ${e.unparse};";
  top.bindingFreeVars = mempty;
  top.isApplicative = true;
  top.appBindings = [];
  top.appExprs = [];
  top.appResult = ^e;
  top.transform = mkStrFunctionInvocation("silver:core:pure", [^e]);
  top.recBindings = [];
  top.recBody = top.recRes;
  top.mdoTransform = ^top;
}

concrete production exprDoBinding
top::DoBinding ::= e::Expr ';'
{
  top.unparse = s"${e.unparse};";
  top.isApplicative = true;
  top.appBindings =
    [lambdaRHSElemUnderline('_')];
  top.appExprs = [^e];
  top.transform = mkStrFunctionInvocation("silver:core:applySecond", [^e, top.transformIn]);

  top.recBindings = [];
}

concrete production letDoBinding
top::DoBinding ::= 'let' n::Name '=' e::Expr ';'
{
  top.unparse = s"let ${n.unparse} = ${e.unparse};";
  top.boundVars <- ts:fromList([n.name]);
  top.isApplicative = false;
  top.appBindings = error("Not applicative");
  top.appExprs = error("Not applicative");

  top.transform =
    letp(
      assignExpr(^n, terminal(ColonColon_t, "::"), typerepTypeExpr(freshType()), '=', ^e),
      top.transformIn);

  top.recBindings = [(n.name, typerepTypeExpr(freshType()))];
}

concrete production letDoBindingTy
top::DoBinding ::= 'let' n::Name '::' t::TypeExpr '=' e::Expr ';'
{
  top.unparse = s"let ${n.unparse}::${t.unparse} = ${e.unparse};";
  top.boundVars <- ts:fromList([n.name]);
  top.isApplicative = false;
  top.appBindings = error("Not applicative");
  top.appExprs = error("Not applicative");

  top.transform =
    letp(
      assignExpr(^n, terminal(ColonColon_t, "::"), ^t, '=', ^e),
      top.transformIn);

  top.recBindings = [(n.name, ^t)];
}

concrete production bindDoBinding
top::DoBinding ::= n::Name  '<-' e::Expr ';'
{
  top.unparse = s"${n.unparse} <- ${e.unparse};";
  top.boundVars <- ts:fromList([n.name]);
  top.isApplicative = true;
  top.appBindings = [lambdaRHSElemId(^n)];
  top.appExprs = [^e];

  nondecorated local cont :: Expr =
    lambdap(
      lambdaRHSCons(
        lambdaRHSElemIdTy(^n, terminal(ColonColon_t, "::"), typerepTypeExpr(freshType())),
        lambdaRHSNil()),
      top.transformIn);
  top.transform = mkStrFunctionInvocation("silver:core:bind", [^e, cont]);

  top.recBindings = [(n.name, typerepTypeExpr(freshType()))];
}

concrete production bindDoBindingTy
top::DoBinding ::= n::Name DoDoubleColon_t t::TypeExpr '<-' e::Expr ';'
{
  top.unparse = s"${n.unparse}::${t.unparse} <- ${e.unparse};";
  top.boundVars <- ts:fromList([n.name]);
  top.isApplicative = true;
  top.appBindings = [lambdaRHSElemIdTy(^n, terminal(ColonColon_t, "::"), ^t)];
  top.appExprs = [^e];

  nondecorated local cont :: Expr =
    lambdap(
      lambdaRHSCons(
        lambdaRHSElemIdTy(^n, terminal(ColonColon_t, "::"), ^t),
        lambdaRHSNil()),
      top.transformIn);
  top.transform = mkStrFunctionInvocation("silver:core:bind", [^e, cont]);

  top.recBindings = [(n.name, ^t)];
}

