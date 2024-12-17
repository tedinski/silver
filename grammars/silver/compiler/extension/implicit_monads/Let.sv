grammar silver:compiler:extension:implicit_monads;

import silver:compiler:analysis:uniqueness;

aspect production letp
top::Expr ::= la::AssignExpr  e::Expr
{
  top.merrors := la.merrors ++ ne.merrors;

  --We needed to provide our own environment.
  local ne::Expr = ^e;
  ne.config = top.config;
  ne.grammarName = top.grammarName;
  ne.compiledGrammars = top.compiledGrammars;
  ne.flowEnv = top.flowEnv;
  ne.frame = top.frame;
  ne.mDownSubst = la.mUpSubst;
  ne.downSubst = la.mUpSubst;
  ne.finalSubst = top.mUpSubst;
  ne.env = newScopeEnv(la.mdefs, top.env);
  ne.expectedMonad = top.expectedMonad;
  ne.decSiteVertexInfo = top.decSiteVertexInfo;
  ne.alwaysDecorated = top.alwaysDecorated;
  ne.appDecSiteVertexInfo = nothing();
  ne.dispatchFlowDeps = [];
  ne.isRoot = top.isRoot;

  la.mDownSubst = top.mDownSubst;
  top.mUpSubst = ne.mUpSubst;

  top.mtyperep = if null(la.bindInList) || fst(monadsMatch(ne.mtyperep, top.expectedMonad, top.mUpSubst))
                 then ne.mtyperep
                 else monadOfType(top.expectedMonad, ne.mtyperep);

  --I'm not entirely sure if this should be false.  It might be that it should
  --be based on top.monadicallyUsed and whether other things become binds or
  --something.
  ne.monadicallyUsed = false;
  top.monadicNames = la.monadicNames ++ ne.monadicNames;

  nondecorated local mreturn::Expr = monadReturn();
  nondecorated local mbind::Expr = monadBind();

  {-
    Our rewriting here binds in anything after the let to keep names from
    interfering with each other.  For example, if we have
        let a::Ta = ea; b::Tb = eb; c::Tc = ec in d
    where a and c are monadic, we rewrite to
        let a::M<Ta> = ea; b::Tb = eb; c::M<Tc> = ec in a >>= \a::Ta. c >>= \c::Tc. d
    This ensures our names do not interfere with prevous ones.  For example, ec
    might reference an a that existed before the let, so we need to bind all the
    expressions to names at once in a let; after that, we are free to use the
    names to create binds.
  -}
  top.monadRewritten =
     letp(la.fixedAssigns,
          boundIn);
  nondecorated local inside::Expr =
    if isMonad(ne.mtyperep, top.env) || null(la.bindInList)
    then ne.monadRewritten
    else Silver_Expr { $Expr{mreturn}($Expr{ne.monadRewritten}) };
  nondecorated local boundIn::Expr =
    foldr(\x::Pair<Name TypeExpr> y::Expr ->
            buildApplication(mbind,
                [baseExpr(qName(x.fst.name)),
                 buildLambda(x.fst.name,
                             decorate x.snd with
                                {env=top.env; grammarName=top.grammarName; config=top.config; flowEnv=top.flowEnv;}.typerep,
                             y)]),
          inside, la.bindInList);
}


synthesized attribute fixedAssigns::AssignExpr occurs on AssignExpr;
synthesized attribute bindInList::[Pair<Name TypeExpr>] occurs on AssignExpr;
--definitions, but ones that won't cause errors with monad type mismatches in let definitions
synthesized attribute mdefs::[Def] occurs on AssignExpr;

attribute merrors, mDownSubst, mUpSubst, monadicNames, expectedMonad occurs on AssignExpr;
propagate expectedMonad on AssignExpr;

aspect production appendAssignExpr
top::AssignExpr ::= a1::AssignExpr a2::AssignExpr
{
  top.merrors := a1.merrors ++ a2.merrors;

  propagate mDownSubst, mUpSubst;

  top.monadicNames = a1.monadicNames ++ a2.monadicNames;

  top.mdefs = a1.mdefs ++ a2.mdefs;

  top.bindInList = a1.bindInList ++ a2.bindInList;

  top.fixedAssigns = appendAssignExpr(a1.fixedAssigns, a2.fixedAssigns);
}

aspect production assignExpr
top::AssignExpr ::= id::Name '::' t::TypeExpr '=' e::Expr
{
  top.merrors := e.merrors;
  top.merrors <- if isMonad(t.typerep, top.env) && fst(monadsMatch(top.expectedMonad, t.typerep, top.mDownSubst))
                 then [errFromOrigin(top, "Let bindings may not use a monad type")]
                 else [];
  local errCheck::TypeCheck = if isMonad(e.mtyperep, top.env) && fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mDownSubst))
                              then check(t.typerep, monadInnerType(e.mtyperep))
                              else check(t.typerep, e.mtyperep);
  e.mDownSubst = top.mDownSubst;
  errCheck.downSubst = e.mUpSubst;
  top.mUpSubst = errCheck.upSubst;

  --I'm not entirely sure about this vs. false--it should only matter if we are
  --directly redefining a name (doing x::T=y), which would be weird for a person
  --to write (?), and redfining it monadically.  This would happen if the person
  --was putting in a let after let insertion failed, but then this should be the
  --only place where the name occurs, so it wouldn't affect anything then either.
  e.monadicallyUsed = isMonad(e.mtyperep, top.env) && fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mDownSubst)) && !isMonad(t.typerep, top.env);
  top.monadicNames = e.monadicNames;

  top.mdefs = [lexicalLocalDef(top.grammarName, id.nameLoc, fName,
                               performSubstitution(t.typerep, top.mUpSubst),
                               e.flowVertexInfo, e.flowDeps)];

  top.bindInList = if isMonad(e.mtyperep, top.env) && fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                   then [(^id, ^t)]
                   else [];

  top.fixedAssigns = if isMonad(e.mtyperep, top.env) && fst(monadsMatch(e.mtyperep, top.expectedMonad, top.mUpSubst))
                     --use t.typerep to get typechecking when we create the ultimate monadRewritten
                     then assignExpr(^id, '::', typerepTypeExpr(monadOfType(top.expectedMonad, t.typerep)),
                                     '=', e.monadRewritten)
                     else assignExpr(^id, '::', ^t, '=', e.monadRewritten);
}




aspect production lexicalLocalReference
top::Expr ::= @q::QName  _ _
{
  top.merrors := [];
  propagate mDownSubst, mUpSubst;
  top.mtyperep = q.lookupValue.typeScheme.monoType;
  top.monadicNames = if top.monadicallyUsed
                     then [baseExpr(^q)]
                     else [];
  top.monadRewritten = baseExpr(^q);
}
