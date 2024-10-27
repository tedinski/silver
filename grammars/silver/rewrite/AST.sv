grammar silver:rewrite;

inherited attribute givenStrategy::Strategy occurs on AST, ASTs, NamedASTs, NamedAST;
synthesized attribute allResult<a>::Maybe<a>;
synthesized attribute someResult<a>::Maybe<a>;
synthesized attribute oneResult<a>::Maybe<a>;

inherited attribute productionName::String occurs on AST;
inherited attribute childStrategies::[Strategy] occurs on AST, ASTs;
inherited attribute annotationStrategies::[Pair<String Strategy>] occurs on AST, NamedASTs, NamedAST;
synthesized attribute traversalResult<a>::Maybe<a>;
inherited attribute headStrategy::Strategy occurs on AST;
inherited attribute tailStrategy::Strategy occurs on AST;
synthesized attribute consListCongruenceResult::Maybe<AST> occurs on AST;
synthesized attribute nilListCongruenceResult::Maybe<AST> occurs on AST;

attribute allResult<AST> occurs on AST;
attribute someResult<AST> occurs on AST;
attribute oneResult<AST> occurs on AST;
attribute traversalResult<AST> occurs on AST;

propagate givenStrategy on AST, ASTs, NamedASTs, NamedAST;

aspect default production
top::AST ::=
{
  top.allResult = just(^top);
  top.someResult = nothing();
  top.oneResult = nothing();
  top.traversalResult = nothing();
  top.consListCongruenceResult = nothing();
  top.nilListCongruenceResult = nothing();
}

aspect production nonterminalAST
top::AST ::= prodName::String children::ASTs annotations::NamedASTs
{
  top.allResult =
    do {
      childrenResult::ASTs <- children.allResult;
      annotationsResult::NamedASTs <- annotations.allResult;
      return nonterminalAST(prodName, childrenResult, annotationsResult);
    };
  top.someResult =
    case children.someResult, annotations.someResult of
    | just(childrenResult), just(annotationsResult) ->
      just(nonterminalAST(prodName, childrenResult, annotationsResult))
    | just(childrenResult), nothing() ->
      just(nonterminalAST(prodName, childrenResult, ^annotations))
    | nothing(), just(annotationsResult) ->
      just(nonterminalAST(prodName, ^children, annotationsResult))
    | nothing(), nothing() -> nothing()
    end;
  top.oneResult =
    case children.oneResult, annotations.oneResult of
    | just(childrenResult), _ ->
      just(nonterminalAST(prodName, childrenResult, ^annotations))
    | nothing(), just(annotationsResult) ->
      just(nonterminalAST(prodName, ^children, annotationsResult))
    | nothing(), nothing() -> nothing()
    end;
  children.childStrategies = top.childStrategies;
  annotations.annotationStrategies = top.annotationStrategies;
  top.traversalResult =
    do {
      if prodName != top.productionName then nothing() else just(unit());
      childrenResult::ASTs <- children.traversalResult;
      annotationsResult::NamedASTs <- annotations.traversalResult;
      return nonterminalAST(prodName, childrenResult, annotationsResult);
    };
}

aspect production terminalAST
top::AST ::= terminalName::String lexeme::String location::Location
{
  top.allResult = map(terminalAST(terminalName, lexeme, _), rewriteWith(top.givenStrategy, location));
  -- Exactly one rewritable child
  top.someResult = top.allResult;
  top.oneResult = top.allResult;
}

aspect production listAST
top::AST ::= vals::ASTs
{
  nondecorated local h::AST = case vals of consAST(h, _) -> ^h | _ -> error("not consAST") end;
  nondecorated local t::AST = case vals of consAST(_, t) -> listAST(^t) | _ -> error("not consAST") end;
  top.allResult =
    case vals of
    | consAST(_, _) ->
      do {
        hResult::AST <- decorate top.givenStrategy with { term = h; }.result;
        tResult::AST <- decorate top.givenStrategy with { term = t; }.result;
        return
          case tResult of
          | listAST(a) -> listAST(consAST(hResult, ^a))
          | _ -> error("Rewrite type error")
          end;
      }
    | nilAST() -> just(^top)
    end;
  top.someResult =
    case vals of
    | consAST(_, _) ->
      case decorate top.givenStrategy with { term = h; }.result,
           decorate top.givenStrategy with { term = t; }.result of
      | just(hResult), just(listAST(tResult)) -> just(listAST(consAST(hResult, ^tResult)))
      | just(hResult), nothing() -> just(listAST(consAST(hResult, case vals of consAST(_, t) -> ^t | _ -> error("not consAST") end)))
      | nothing(), just(listAST(tResult)) -> just(listAST(consAST(h, ^tResult)))
      | _, _ -> nothing()
      end
    | nilAST() -> nothing()
    end;
  top.oneResult =
    case vals of
    | consAST(_, _) ->
      case decorate top.givenStrategy with { term = h; }.result,
           decorate top.givenStrategy with { term = t; }.result of
      | just(hResult), _ -> just(listAST(consAST(hResult, case vals of consAST(_, t) -> ^t | _ -> error("not consAST") end)))
      | nothing(), just(listAST(tResult)) -> just(listAST(consAST(h, ^tResult)))
      | nothing(), _ -> nothing()
      end
    | nilAST() -> nothing()
    end;
  
  top.consListCongruenceResult =
    case vals of
    | consAST(_, _) ->
      do {
        hResult::AST <- decorate top.headStrategy with { term = h; }.result;
        tResult::AST <- decorate top.tailStrategy with { term = t; }.result;
        return
          case tResult of
          | listAST(a) -> listAST(consAST(hResult, ^a))
          | _ -> error("Rewrite type error")
          end;
      }
    | nilAST() -> nothing()
    end;
  top.nilListCongruenceResult =
    case vals of
    | consAST(_, _) -> nothing()
    | nilAST() -> just(^top)
    end;
}

attribute allResult<ASTs> occurs on ASTs;
attribute someResult<ASTs> occurs on ASTs;
attribute oneResult<ASTs> occurs on ASTs;
attribute traversalResult<ASTs> occurs on ASTs;

aspect production consAST
top::ASTs ::= h::AST t::ASTs
{
  top.allResult =
    do {
      hResult::AST <- decorate top.givenStrategy with { term = ^h; }.result;
      tResult::ASTs <- t.allResult;
      return consAST(hResult, tResult);
    };
  top.someResult =
    case decorate top.givenStrategy with { term = ^h; }.result, t.someResult of
    | just(hResult), just(tResult) -> just(consAST(hResult, tResult))
    | just(hResult), nothing() -> just(consAST(hResult, ^t))
    | nothing(), just(tResult) -> just(consAST(^h, tResult))
    | nothing(), nothing() -> nothing()
    end;
  top.oneResult =
    case decorate top.givenStrategy with { term = ^h; }.result, t.oneResult of
    | just(hResult), _ -> just(consAST(hResult, ^t))
    | nothing(), just(tResult) -> just(consAST(^h, tResult))
    | nothing(), nothing() -> nothing()
    end;
  top.traversalResult =
    do {
      hResult::AST <- decorate head(top.childStrategies) with { term = ^h; }.result;
      tResult::ASTs <- t.traversalResult;
      return consAST(hResult, tResult);
    };
  t.childStrategies = tail(top.childStrategies);
}

aspect production nilAST
top::ASTs ::=
{
  top.allResult = just(^top);
  top.someResult = nothing();
  top.oneResult = nothing();
  top.traversalResult = just(^top);
}

synthesized attribute bindings::[Pair<String AST>] occurs on NamedASTs;

attribute allResult<NamedASTs> occurs on NamedASTs;
attribute someResult<NamedASTs> occurs on NamedASTs;
attribute oneResult<NamedASTs> occurs on NamedASTs;
attribute traversalResult<NamedASTs> occurs on NamedASTs;

aspect production consNamedAST
top::NamedASTs ::= h::NamedAST t::NamedASTs
{
  top.bindings = h.binding :: t.bindings;
  top.allResult =
    do {
      hResult::NamedAST <- h.allResult;
      tResult::NamedASTs <- t.allResult;
      return consNamedAST(hResult, tResult);
    };
  top.someResult =
    case h.someResult, t.someResult of
    | just(hResult), just(tResult) -> just(consNamedAST(hResult, tResult))
    | just(hResult), nothing() -> just(consNamedAST(hResult, ^t))
    | nothing(), just(tResult) -> just(consNamedAST(^h, tResult))
    | nothing(), nothing() -> nothing()
    end;
  top.oneResult =
    case h.oneResult, t.oneResult of
    | just(hResult), _ -> just(consNamedAST(hResult, ^t))
    | nothing(), just(tResult) -> just(consNamedAST(^h, tResult))
    | nothing(), nothing() -> nothing()
    end;
  propagate annotationStrategies;
  top.traversalResult =
    do {
      hResult::NamedAST <- h.traversalResult;
      tResult::NamedASTs <- t.traversalResult;
      return consNamedAST(hResult, tResult);
    };
}

aspect production nilNamedAST
top::NamedASTs ::=
{
  top.bindings = [];
  top.allResult = just(^top);
  top.someResult = nothing();
  top.oneResult = nothing();
  top.traversalResult = just(^top);
}

synthesized attribute binding::Pair<String AST> occurs on NamedAST;

attribute allResult<NamedAST> occurs on NamedAST;
attribute someResult<NamedAST> occurs on NamedAST;
attribute oneResult<NamedAST> occurs on NamedAST;
attribute traversalResult<NamedAST> occurs on NamedAST;

aspect production namedAST
top::NamedAST ::= n::String v::AST
{
  top.binding = (n, ^v);
  top.allResult =
    do {
      vResult::AST <- decorate top.givenStrategy with { term = ^v; }.result;
      return namedAST(n, vResult);
    };
  -- Exactly one rewritable child
  top.someResult = top.allResult;
  top.oneResult = top.allResult;
  
  top.traversalResult =
    -- Look up and apply all strategies for the annotation
    -- (it's easier to just handle duplicates than to disallow them.)
    map(
      namedAST(n, _),
      foldl(
        \ ma::Maybe<AST> s::Strategy ->
          bind(ma, \ a::AST -> decorate s with { term = a; }.result),
        just(^v),
        lookupAll(n, top.annotationStrategies)));
}
