grammar silver:compiler:definition:core;

--import silver:compiler:analysis:typechecking:core;
import silver:util:treeset as ts;

tracked nonterminal Expr with
  config, grammarName, env, unparse, errors, freeVars, frame, compiledGrammars, typerep, isRoot, originRules;
tracked nonterminal Exprs with
  config, grammarName, env, unparse, errors, freeVars, frame, compiledGrammars, exprs, rawExprs, originRules;

tracked nonterminal ExprInhs with
  config, grammarName, env, unparse, errors, freeVars, frame, compiledGrammars, decoratingnt, suppliedInhs, allSuppliedInhs, originRules;
tracked nonterminal ExprInh with
  config, grammarName, env, unparse, errors, freeVars, frame, compiledGrammars, decoratingnt, suppliedInhs, allSuppliedInhs, originRules;
tracked nonterminal ExprLHSExpr with
  config, grammarName, env, unparse, errors, freeVars, frame, name, typerep, decoratingnt, suppliedInhs, allSuppliedInhs, originRules;

flowtype unparse {} on Expr, Exprs, ExprInhs, ExprInh, ExprLHSExpr;
flowtype freeVars {frame} on Expr, Exprs, ExprInhs, ExprInh, ExprLHSExpr;
flowtype Expr =
  forward {grammarName, env, flowEnv, downSubst, finalSubst, frame, isRoot, compiledGrammars, config, decSiteVertexInfo, appDecSiteVertexInfo, dispatchFlowDeps},
  decorate {forward, alwaysDecorated, originRules},
  errors {forward}, typerep {forward};

flowtype decorate {grammarName, env, flowEnv, downSubst, finalSubst, frame, originRules, compiledGrammars, config} on Exprs;
flowtype decorate {grammarName, env, flowEnv, downSubst, finalSubst, frame, originRules, compiledGrammars, config, decoratingnt, allSuppliedInhs} on ExprInhs, ExprInh;
flowtype decorate {grammarName, env, frame, originRules, config, decoratingnt, allSuppliedInhs} on ExprLHSExpr;
flowtype forward {} on Exprs, ExprInhs, ExprInh, ExprLHSExpr;

flowtype errors {grammarName, env, flowEnv, downSubst, finalSubst, frame, compiledGrammars, config} on Exprs;
flowtype errors {grammarName, env, flowEnv, downSubst, finalSubst, frame, compiledGrammars, config, decoratingnt, allSuppliedInhs} on ExprInhs, ExprInh;
flowtype errors {grammarName, env, frame, config, decoratingnt, allSuppliedInhs} on ExprLHSExpr;

propagate errors on Expr, Exprs, ExprInhs, ExprInh, ExprLHSExpr
  excluding terminalAccessHandler;
propagate config, grammarName, env, freeVars, frame, compiledGrammars
  on Expr, Exprs, ExprInhs, ExprInh, ExprLHSExpr;
propagate originRules on Expr, Exprs, ExprInhs, ExprInh, ExprLHSExpr excluding noteAttachment;
propagate decoratingnt, allSuppliedInhs on ExprInhs, ExprInh, ExprLHSExpr;

{--
 - The nonterminal being decorated. (Used for 'decorate with {}')
 -}
inherited attribute decoratingnt :: Type;
{--
 - The inherited attributes being supplied in a decorate expression
 -}
synthesized attribute suppliedInhs :: [String];
inherited attribute allSuppliedInhs :: [String];
{--
 - A list of decorated expressions from an Exprs.
 -}
monoid attribute exprs :: [Decorated Expr];
{--
 - Get each individual Expr, without decorating them.
 -}
monoid attribute rawExprs :: [Expr];
{--
 - Compute the expression's free (unbound) variables
 -}
monoid attribute freeVars :: ts:Set<String>;

-- Is this Expr the logical "root" of the expression? That is, will it's value be the value computed
--  for the attribute/return value/etc that it is part of?
inherited attribute isRoot :: Boolean;

inherited attribute originRules :: [Decorated Expr];

attribute grammarName, frame occurs on Contexts, Context;
propagate grammarName, frame on Contexts, Context;

abstract production errorExpr
top::Expr ::= e::[Message]
{
  top.unparse = s"{- Errors:\n${messagesToString(e)} -}";
  top.errors <- e;
  top.typerep = errorType();
}

concrete production nestedExpr
top::Expr ::= '(' e::Expr ')'
{
  top.unparse = "(" ++ e.unparse ++ ")";
  
  forwards to @e;
}

concrete production baseExpr
top::Expr ::= q::QName
{
  top.unparse = q.unparse;
  top.freeVars := ts:fromList([q.name]);
  propagate env;
  
  forwards to if null(q.lookupValue.dcls)
              then errorReference(q.lookupValue.errors, q)
              else q.lookupValue.dcl.refDispatcher(q);
} action {
  if (contains(q.name, sigNames)) {
    insert semantic token IdSigName_t at q.nameLoc;
  }
}

abstract production errorReference
top::Expr ::= msg::[Message]  @q::QName
{
  top.unparse = q.unparse;
  top.freeVars <- ts:fromList([q.name]);
  
  top.errors <- msg;
  top.typerep = errorType();
}

dispatch Reference = Expr ::= @q::QName;

abstract production childReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars <- ts:fromList([q.name]);
  
  top.typerep = if isDecorable(q.lookupValue.typeScheme.monoType, top.env)
                then q.lookupValue.typeScheme.asDecoratedType
                else q.lookupValue.typeScheme.monoType;
}

abstract production lhsReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars <- ts:fromList([q.name]);
  
  -- An (non-data) LHS is *always* a decorated (nonterminal) type.
  top.typerep = q.lookupValue.typeScheme.asDecoratedType;
}

abstract production localReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars <- ts:fromList([q.name]);
  
  top.typerep =
    if isDecorable(q.lookupValue.typeScheme.monoType, top.env)
    then q.lookupValue.typeScheme.asDecoratedType
    else q.lookupValue.typeScheme.monoType;
}

abstract production nondecLocalReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars <- ts:fromList([q.name]);
  
  top.typerep = q.lookupValue.typeScheme.monoType;
}

abstract production forwardReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars <- ts:fromList([q.name]);
  
  -- An LHS (and thus, forward) is *always* a decorated (nonterminal) type.
  top.typerep = q.lookupValue.typeScheme.asDecoratedType;
}

-- Note here that production and function *references* are distinguished.
-- Later on, we do *not* distinguish for application.

abstract production productionReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars <- ts:fromList([q.name]);

  production typeScheme::PolyType = q.lookupValue.typeScheme;
  top.typerep = typeScheme.typerep;

  production contexts::Contexts =
    foldContexts(map(performContextSubstitution(_, top.finalSubst), typeScheme.contexts));
  contexts.env = top.env;
  contexts.frame = top.frame;
  contexts.config = top.config;
  contexts.grammarName = top.grammarName;
  contexts.compiledGrammars = top.compiledGrammars;
}

abstract production functionReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars <- ts:fromList([q.name]);

  production typeScheme::PolyType = q.lookupValue.typeScheme;
  top.typerep = typeScheme.typerep;

  production contexts::Contexts =
    foldContexts(map(performContextSubstitution(_, top.finalSubst), typeScheme.contexts));
  contexts.env = top.env;
  contexts.frame = top.frame;
  contexts.config = top.config;
  contexts.grammarName = top.grammarName;
  contexts.compiledGrammars = top.compiledGrammars;
}

abstract production classMemberReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars <- ts:fromList([q.name]);

  production typeScheme::PolyType = q.lookupValue.typeScheme;
  top.typerep = typeScheme.typerep;

  production instHead::Context =
    case typeScheme.contexts of
    | c :: _ -> performContextSubstitution(c, top.finalSubst)
    | _ -> error("Class member should have at least one context!")
    end;
  instHead.env = top.env;
  instHead.frame = top.frame;
  instHead.config = top.config;
  instHead.grammarName = top.grammarName;
  instHead.compiledGrammars = top.compiledGrammars;
  production contexts::Contexts =
    case typeScheme.contexts of
    | _ :: cs -> foldContexts(map(performContextSubstitution(_, top.finalSubst), cs))
    | _ -> error("Class member should have at least one context!")
    end;
  contexts.env = top.env;
  contexts.frame = top.frame;
  contexts.config = top.config;
  contexts.grammarName = top.grammarName;
  contexts.compiledGrammars = top.compiledGrammars;
}

abstract production globalValueReference implements Reference
top::Expr ::= @q::QName
{
  top.unparse = q.unparse;
  top.freeVars <- ts:fromList([q.name]);

  -- Type inference
  production typeScheme::PolyType = q.lookupValue.typeScheme;
  top.typerep = typeScheme.typerep;

  -- Context resolution 
  -- Performs final substitution on all the contexts
  production contexts::Contexts =
    foldContexts(map(performContextSubstitution(_, top.finalSubst), typeScheme.contexts));
  contexts.env = top.env;
  contexts.frame = top.frame;
  contexts.config = top.config;
  contexts.grammarName = top.grammarName;
  contexts.compiledGrammars = top.compiledGrammars;
}

concrete production concreteForwardExpr
top::Expr ::= q::'forward'
{
  top.unparse = "forward";

  -- TODO: we're forwarding to baseExpr just to decorate the tree we create.
  -- That's a bit weird.
  forwards to baseExpr(qName("forward"));
}

concrete production forwardParentReference
top::Expr ::= 'forwardParent'
{
  top.unparse = "forwardParent";

  top.typerep = top.frame.signature.outputElement.typerep.asDecoratedType;
  top.errors <-
    if !any(map((.elementShared), top.frame.signature.inputElements))
    then [errFromOrigin(top, "This production has no shared children, and thus is not known to be the target of forwarding.")]
    else [];
}

concrete production application
top::Expr ::= e::Expr '(' es::AppExprs ',' anns::AnnoAppExprs ')'
{
  top.unparse = e.unparse ++ "(" ++ es.unparse ++ (if es.appExprSize > 0 && anns.appExprSize > 0 then ", " else "") ++ anns.unparse ++ ")";
  propagate config, grammarName, env, freeVars, frame, originRules, compiledGrammars;
  e.isRoot = false;
  
  local correctNumTypes :: [Type] =
    if length(t.inputTypes) > es.appExprSize
    then take(es.appExprSize, t.inputTypes)
    else if length(t.inputTypes) < es.appExprSize
    then t.inputTypes ++ repeat(errorType(), es.appExprSize - length(t.inputTypes))
    else t.inputTypes;
  
  -- NOTE: REVERSED ORDER
  -- We may need to resolve e's type to get at the actual 'function type'
  local t :: Type = performSubstitution(e.typerep, e.upSubst);
  -- TODO: These should maybe be supplied after forwarding?
  es.appExprTypereps = reverse(correctNumTypes);
  es.appExprApplied = e.unparse;
  anns.appExprApplied = e.unparse;
  anns.remainingFuncAnnotations = t.namedTypes;
  anns.funcAnnotations = anns.remainingFuncAnnotations;
  
  top.errors <- 
    if !t.isApplicable
    then []
    else if length(t.inputTypes) > es.appExprSize
    then [errFromOrigin(top, "Too few arguments provided to function '" ++ e.unparse ++ "'")]
    else if length(t.inputTypes) < es.appExprSize && case t.outputType of dispatchType(_) -> false | _ -> true end
    then [errFromOrigin(top, "Too many arguments provided to function '" ++ e.unparse ++ "'")]
    else [];

  -- TODO: You know, since the rule is we can't access .typerep without "first" supplying
  -- .downSubst, perhaps we should just... report .typerep after substitution in the first place!
  forwards to t.applicationDispatcher(e, es, anns);
}

concrete production applicationAnno
top::Expr ::= e::Expr '(' anns::AnnoAppExprs ')'
{
  forwards to application(@e, $2, emptyAppExprs(), ',', @anns, $4);
}
concrete production applicationExpr
top::Expr ::= e::Expr '(' es::AppExprs ')'
{
  forwards to application(@e, $2, @es, ',', emptyAnnoAppExprs(), $4);
}
concrete production applicationEmpty
top::Expr ::= e::Expr '(' ')'
{
  forwards to application(@e, $2, emptyAppExprs(), ',', emptyAnnoAppExprs(), $3);
}

dispatch Application = Expr ::= @e::Expr @es::AppExprs @anns::AnnoAppExprs;

abstract production errorApplication implements Application
top::Expr ::= @e::Expr @es::AppExprs @anns::AnnoAppExprs
{
  top.unparse = e.unparse ++ "(" ++ es.unparse ++ "," ++ anns.unparse ++ ")";

  top.errors <-
    if e.typerep.isError then [] else  
      [errFromOrigin(top, e.unparse ++ " has type " ++ prettyType(performSubstitution(e.typerep, e.upSubst)) ++
        " and cannot be invoked as a function.")];
        -- TODO This error message is cumbersomely generated...

  top.typerep = errorType();
}

-- Note that this applies to both function and productions.
-- We don't distinguish anymore at this point. A production reference
-- becomes a function, effectively.
abstract production functionApplication implements Application
top::Expr ::= @e::Expr @es::AppExprs @anns::AnnoAppExprs
{
  top.unparse = e.unparse ++ "(" ++ es.unparse ++ "," ++ anns.unparse ++ ")";
  top.freeVars := e.freeVars ++ es.freeVars ++ anns.freeVars;

  local t :: Type = performSubstitution(e.typerep, e.upSubst);
  forwards to
    (if es.isPartial || anns.isPartial
     then partialApplication
     else
       case t.outputType of
       | dispatchType(_) when es.appExprSize > length(t.inputTypes) -> curriedDispatchApplication
       | _ -> functionInvocation
       end)(e, es, anns);
}

abstract production functionInvocation implements Application
top::Expr ::= @e::Expr @es::AppExprs @anns::AnnoAppExprs
{
  top.unparse = e.unparse ++ "(" ++ es.unparse ++ "," ++ anns.unparse ++ ")";

  local ety :: Type = performSubstitution(e.typerep, e.upSubst);

  top.typerep = ety.outputType;
}

abstract production partialApplication implements Application
top::Expr ::= @e::Expr @es::AppExprs @anns::AnnoAppExprs
{
  top.unparse = e.unparse ++ "(" ++ es.unparse ++ "," ++ anns.unparse ++ ")";

  local ety :: Type = performSubstitution(e.typerep, e.upSubst);

  top.typerep =
    appTypes(
      functionType(length(es.missingTypereps) + length(anns.partialAnnoTypereps), map(fst, anns.missingAnnotations)),
      es.missingTypereps ++ anns.partialAnnoTypereps ++ map(snd, anns.missingAnnotations) ++ [ety.outputType]);
}

-- Dispatch productions with extra arguments are partially curried,
-- e.g. lexicalLocalReference has type (Reference ::= Maybe<VertexType> [FlowVertex]).
-- This exists to permit all arguments to be supplied directly,
-- e.g. lexicalLocalReference(q, fi, fd) instead of lexicalLocalReference(fi, fd)(q).
abstract production curriedDispatchApplication implements Application
top::Expr ::= @e::Expr @es::AppExprs @anns::AnnoAppExprs
{
  top.unparse = e.unparse ++ "(" ++ es.unparse ++ "," ++ anns.unparse ++ ")";

  local t :: Type = performSubstitution(e.typerep, e.upSubst);

  -- TODO: args are being (unavoidably?) re-decorated here.
  production extraArgs :: AppExprs =
    foldl(snocAppExprs(_, ',', _), emptyAppExprs(),
      map(presentAppExpr, drop(es.appExprSize - length(t.inputTypes), es.rawExprs)));
  production dispatchArgs :: AppExprs =
    foldl(snocAppExprs(_, ',', _), emptyAppExprs(),
      map(presentAppExpr, take(es.appExprSize - length(t.inputTypes), es.rawExprs)));

  forwards to application(
    application(@e, '(', @extraArgs, ',', emptyAnnoAppExprs(), ')'),
    '(', @dispatchArgs, ',', ^anns, ')');
}

abstract production dispatchApplication implements Application
top::Expr ::= @e::Expr @es::AppExprs @anns::AnnoAppExprs
{
  top.unparse = e.unparse ++ "(" ++ es.unparse ++ "," ++ anns.unparse ++ ")";

  top.typerep = performSubstitution(e.typerep, e.upSubst).outputType;
}

concrete production noteAttachment
top::Expr ::= 'attachNote' note::Expr 'on' e::Expr 'end'
{
  top.unparse = "attachNote" ++ note.unparse ++ " on " ++ e.unparse ++ " end";

  top.typerep = e.typerep;

  note.isRoot = false;
  e.isRoot = false;
  note.originRules = top.originRules;
  e.originRules = note :: top.originRules;
}

-- NOTE: this is not intended to be used normally.
-- Its purpose is for test cases. Essentially all other situations should never care what the forward tree is.
concrete production forwardAccess
top::Expr ::= e::Expr '.' 'forward'
{
  top.unparse = e.unparse ++ ".forward";
  top.typerep = e.typerep;

  e.isRoot = false;
}

concrete production access
top::Expr ::= e::Expr '.' q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  propagate config, grammarName, env, freeVars, frame, originRules, compiledGrammars;
  e.isRoot = false;
  
  local eTy::Type = performSubstitution(e.typerep, e.upSubst);
  q.attrFor = if eTy.isDecorated then eTy.decoratedType else ^eTy;
  
  -- Note: we're first consulting the TYPE of the LHS.
  forwards to eTy.accessHandler(e, q);
  -- This jumps to:
  -- errorAccessHandler  (e.g. 1.unparse)
  -- undecoratedAccessHandler
  -- dataAccessHandler
  -- decoratedAccessHandler  (see that production, for how normal attribute access proceeds!)
  -- terminalAccessHandler
}

dispatch Access = Expr ::= @e::Expr @q::QNameAttrOccur;

abstract production errorAccessHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  
  top.typerep = errorType();
  
  top.errors <-
    if e.typerep.isError then [] else
      let ref :: String =
            if length(e.unparse) < 12 then "'" ++ e.unparse ++ "' has" else "LHS of '.' is"
       in [errFromOrigin(top, ref ++ " type " ++ prettyType(q.attrFor) ++ " and cannot have attributes.")]
      end;
}

abstract production terminalAccessHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  
  -- NO use of q.errors, as that become nonsensical here.
  top.errors := e.errors;
  
  top.errors <-
    if q.name == "lexeme" || q.name == "location" || 
       q.name == "filename" || q.name == "line" || q.name == "column"
    then []
    else [errFromOrigin(q, q.name ++ " is not a terminal attribute")];

  top.typerep =
    if q.name == "lexeme" || q.name == "filename"
    then stringType()
    else if q.name == "line" || q.name == "column"
    then intType()
    else if q.name == "location"
    then nonterminalType("silver:core:Location", [], true, false)
    else errorType();
}

abstract production undecoratedAccessHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  
  -- Note: LHS is UNdecorated, here we dispatch based on the kind of attribute.
  forwards to if !q.found then unknownDclAccessHandler(e, q)
              else q.attrDcl.undecoratedAccessHandler(e, q);
  -- annoAccessHandler
  -- accessBouncer
  -- transUndecoratedAccessErrorHandler
  -- unknownDclAccessHandler  -- unknown attribute error raised already.
}

abstract production dataAccessHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  
  -- Note: LHS is data, here we dispatch based on the kind of attribute.
  forwards to if !q.found then unknownDclAccessHandler(e, q)
              else q.attrDcl.dataAccessHandler(e, q);
  -- annoAccessHandler
  -- synDataAccessHandler
  -- unknownDclAccessHandler  -- unknown attribute error raised already.
}

{--
 - Accessing an attribute occasionally demands manipulating the left-hand side.
 - This production is intended to permit that.
 -}
abstract production accessBouncer
top::Expr ::= e::Expr  @q::QNameAttrOccur target::Access
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  propagate config, grammarName, env, freeVars, frame, originRules, compiledGrammars;
  e.isRoot = false;

  -- Basically the only purpose here is to decorate 'e'.
  forwards to target(e, q);
}
production accessBounceDecorate implements Access
Expr ::= @e::Expr @q::QNameAttrOccur target::Access
{
  forwards to
    accessBouncer(decorateExprWithEmpty('decorate', @e, 'with', '{', '}'), q, target);
}
-- Note that this performs the access on the term that was originally decorated, rather than properly undecorating.
production accessBounceUndecorate implements Access
Expr ::= @e::Expr @q::QNameAttrOccur target::Access
{
  forwards to accessBouncer(
    application(
      baseExpr(qName("silver:core:getTermThatWasDecorated")), '(',
      oneAppExprs(
        presentAppExpr(@e)), ',',
      emptyAnnoAppExprs(), ')'),
    q, target);
}

abstract production decoratedAccessHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  
  -- Note: LHS is decorated, here we dispatch based on the kind of attribute.
  forwards to if !q.found then unknownDclAccessHandler(e, q)
              else q.attrDcl.decoratedAccessHandler(e, q);
  -- From here we go to:
  -- synDecoratedAccessHandler
  -- inhDecoratedAccessHandler
  -- unknownDclAccessHandler  -- unknown attribute error raised already.
}

abstract production synDecoratedAccessHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  
  top.typerep = q.typerep;
}

abstract production inhDecoratedAccessHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  
  top.typerep = q.typerep;
}

abstract production transDecoratedAccessHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  
  top.typerep = q.typerep.asDecoratedType;
}

abstract production annoAccessHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  
  production index :: Integer =
    findNamedSigElem(q.name, annotationsForNonterminal(q.attrFor, top.env), 0);

  top.typerep = q.typerep;
}

abstract production synDataAccessHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;

  top.typerep = q.typerep;
}

abstract production inhUndecoratedAccessErrorHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  
  top.typerep = q.typerep;

  top.errors <- [errFromOrigin(top, s"Cannot access inherited attribute ${q.attrDcl.fullName} from an undecorated type")];
}

abstract production transUndecoratedAccessErrorHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;
  
  top.typerep = q.typerep.asDecoratedType;

  top.errors <- [errFromOrigin(top, s"Cannot access translation attribute ${q.attrDcl.fullName} from an undecorated type")];
}

abstract production unknownDclAccessHandler implements Access
top::Expr ::= @e::Expr @q::QNameAttrOccur
{
  top.unparse = e.unparse ++ "." ++ q.unparse;

  top.typerep = errorType();
}


concrete production decorateExprWithEmpty
top::Expr ::= 'decorate' e::Expr 'with' '{' '}'
{
  top.unparse = "decorate " ++ e.unparse ++ " with {}";

  forwards to decorateExprWith($1, @e, $3, $4, exprInhsEmpty(), $5);
}

concrete production decorateExprWith
top::Expr ::= 'decorate' e::Expr 'with' '{' inh::ExprInhs '}'
{
  top.unparse = "decorate " ++ e.unparse ++ " with {" ++ inh.unparse ++ "}";

  production eType::Type = performSubstitution(e.typerep, inh.downSubst);  -- Specialize e.typerep
  production ntType::Type = if eType.isDecorated then eType.decoratedType else @eType;

  -- TODO: This _could_ be uniqueDecoratedType, but we use decorate in a ton of places where we expect a decoratedType
  top.typerep = decoratedType(^ntType, inhSetType(sort(nub(inh.suppliedInhs ++ eType.inhSetMembers))));
  e.isRoot = false;
  
  inh.decoratingnt = ^ntType;
  inh.allSuppliedInhs = inh.suppliedInhs;
}

abstract production exprInhsEmpty
top::ExprInhs ::= 
{
  top.unparse = "";
  
  top.suppliedInhs = [];
}

concrete production exprInhsOne
top::ExprInhs ::= lhs::ExprInh
{
  top.unparse = lhs.unparse;
  
  top.suppliedInhs = lhs.suppliedInhs;
}

concrete production exprInhsCons
top::ExprInhs ::= lhs::ExprInh inh::ExprInhs
{
  top.unparse = lhs.unparse ++ " " ++ inh.unparse;
  
  top.suppliedInhs = lhs.suppliedInhs ++ inh.suppliedInhs;
}

concrete production exprInh
top::ExprInh ::= lhs::ExprLHSExpr '=' e::Expr ';'
{
  top.unparse = lhs.unparse ++ " = " ++ e.unparse ++ ";";
  
  top.suppliedInhs = lhs.suppliedInhs;

  e.isRoot = false;
}

-- TODO: permit supplying inhs on translation attributes
concrete production exprLhsExpr
top::ExprLHSExpr ::= q::QNameAttrOccur
{
  top.name = q.name;
  top.unparse = q.unparse;

  top.typerep = q.typerep;
  top.suppliedInhs = if q.attrFound then [q.attrDcl.fullName] else [];
  
  q.attrFor = top.decoratingnt;
}

concrete production decorationSiteExpr
top::Expr ::= '@' e::Expr
{
  top.unparse = s"@${e.unparse}";

  top.typerep = e.typerep.decoratedType;
  e.isRoot = false;
}

concrete production undecExpr
top::Expr ::= '^' e::Expr
{
  top.unparse = s"^${e.unparse}";

  forwards to Silver_Expr { silver:core:new($Expr{@e}) };
}

concrete production trueConst
top::Expr ::= 'true'
{
  top.unparse = "true";
  
  top.typerep = boolType();
}

concrete production falseConst
top::Expr ::= 'false'
{
  top.unparse = "false";
  
  top.typerep = boolType();
}

concrete production and
top::Expr ::= e1::AppExpr '&&' e2::AppExpr
{
  top.unparse = e1.unparse ++ " && " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:conj($AppExpr{@e1}, $AppExpr{@e2}) };
}

concrete production or
top::Expr ::= e1::Expr '||' e2::Expr
{
  top.unparse = e1.unparse ++ " || " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:disj($Expr{@e1}, $Expr{@e2}) };
}

concrete production notOp
top::Expr ::= '!' e::Expr
{
  top.unparse = "! " ++ e.unparse;

  forwards to Silver_Expr { silver:core:not($Expr{@e}) };
}

concrete production gtOp
top::Expr ::= e1::Expr op::'>' e2::Expr
{
  top.unparse = e1.unparse ++ " > " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:gt($Expr{@e1}, $Expr{@e2}) };
}

concrete production ltOp
top::Expr ::= e1::Expr op::'<' e2::Expr
{
  top.unparse = e1.unparse ++ " < " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:lt($Expr{@e1}, $Expr{@e2}) };
}

concrete production gteOp
top::Expr ::= e1::Expr op::'>=' e2::Expr
{
  top.unparse = e1.unparse ++ " >= " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:gte($Expr{@e1}, $Expr{@e2}) };
}

concrete production lteOp
top::Expr ::= e1::Expr op::'<=' e2::Expr
{
  top.unparse = e1.unparse ++ " <= " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:lte($Expr{@e1}, $Expr{@e2}) };
}

concrete production eqOp
top::Expr ::= e1::Expr op::'==' e2::Expr
{
  top.unparse = e1.unparse ++ " == " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:eq($Expr{@e1}, $Expr{@e2}) };
}

concrete production neqOp
top::Expr ::= e1::Expr op::'!=' e2::Expr
{
  top.unparse = e1.unparse ++ " != " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:neq($Expr{@e1}, $Expr{@e2}) };
}

concrete production ifThenElse
top::Expr ::= 'if' e1::Expr 'then' e2::Expr 'else' e3::Expr
precedence = 0
{
  top.unparse = "if " ++ e1.unparse ++ " then " ++ e2.unparse ++ " else " ++ e3.unparse;

  top.typerep = e2.typerep;

  e1.isRoot=false;
  e2.isRoot=false;
  e3.isRoot=false;
}

concrete production intConst
top::Expr ::= i::Int_t
{
  top.unparse = i.lexeme;

  top.typerep = intType();
}

concrete production floatConst
top::Expr ::= f::Float_t
{
  top.unparse = f.lexeme;

  top.typerep = floatType();
} 

concrete production plus
top::Expr ::= e1::Expr '+' e2::Expr
{
  top.unparse = e1.unparse ++ " + " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:add($Expr{@e1}, $Expr{@e2}) };
}

concrete production minus
top::Expr ::= e1::Expr '-' e2::Expr
{
  top.unparse = e1.unparse ++ " - " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:sub($Expr{@e1}, $Expr{@e2}) };
}

concrete production multiply
top::Expr ::= e1::Expr '*' e2::Expr
{
  top.unparse = e1.unparse ++ " * " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:mul($Expr{@e1}, $Expr{@e2}) };
}

concrete production divide
top::Expr ::= e1::Expr '/' e2::Expr
{
  top.unparse = e1.unparse ++ " / " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:div($Expr{@e1}, $Expr{@e2}) };
}

concrete production modulus
top::Expr ::= e1::Expr '%' e2::Expr
{
  top.unparse = e1.unparse ++ " % " ++ e2.unparse;

  top.errors <-
    case top.finalType of
    | floatType() -> [wrnFromOrigin(top, "Float modulo always returns zero")]
    | _ -> []
    end;

  forwards to Silver_Expr { silver:core:mod($Expr{@e1}, $Expr{@e2}) };
}

concrete production neg
top::Expr ::= '-' e::Expr
precedence = 13
{
  top.unparse = "- " ++ e.unparse;

  forwards to Silver_Expr { silver:core:negate($Expr{@e}) };
}

concrete production stringConst
top::Expr ::= s::String_t
{
  top.unparse = s.lexeme;

  top.typerep = stringType();
}

concrete production plusPlus
top::Expr ::= e1::Expr op::'++' e2::Expr
{
  top.unparse = e1.unparse ++ " ++ " ++ e2.unparse;

  forwards to Silver_Expr { silver:core:append($Expr{@e1}, $Expr{@e2}) };
}

concrete production terminalConstructor
top::Expr ::= 'terminal' '(' t::TypeExpr ',' es::Expr ',' el::Expr ')'
{
  top.unparse = "terminal(" ++ t.unparse ++ ", " ++ es.unparse ++ ", " ++ el.unparse ++ ")";

  top.typerep = t.typerep;

  es.isRoot = false;
  el.isRoot = false;
}

concrete production terminalFunction
top::Expr ::= 'terminal' '(' t::TypeExpr ',' e::Expr ')'
{
  nondecorated local locExpr::Expr =
    Silver_Expr {
      silver:core:fromMaybe(
        silver:core:bogusLoc(),
        silver:core:getParsedOriginLocation(silver:core:ambientOrigin()))
    };

  forwards to terminalConstructor($1, $2, @t, $4, @e, ',', locExpr, $6);
}

-- These sorta seem obsolete, but there are some important differences from AppExprs.
-- For one, AppExprs expects a fixed, imposed list of types. Here we're flexible!
-- This is used by both pattern matching and list literals.
abstract production exprsEmpty
top::Exprs ::=
{
  top.unparse = "";
  
  top.exprs := [];
  top.rawExprs := [];
}
concrete production exprsSingle
top::Exprs ::= e::Expr
{
  top.unparse = e.unparse;

  top.exprs := [e];
  top.rawExprs := [^e];

  e.isRoot = false;
}
concrete production exprsCons
top::Exprs ::= e1::Expr ',' e2::Exprs
{
  top.unparse = e1.unparse ++ ", " ++ e2.unparse;

  top.exprs := [e1] ++ e2.exprs;
  top.rawExprs := [^e1] ++ e2.rawExprs;

  e1.isRoot = false;
}


{--
 - Exprs with optional underscores omitting parameters. Used exclusively for
 - (partial) function application.
 -}
tracked nonterminal AppExprs with 
  config, grammarName, env, unparse, errors, freeVars, frame, compiledGrammars, exprs, rawExprs,
  isPartial, missingTypereps, appExprIndicies, appExprSize, appExprTypereps, appExprApplied, originRules;
flowtype AppExprs =
  decorate {
    config, grammarName, env, frame, compiledGrammars, appExprTypereps, appExprApplied, originRules,
    downSubst, finalSubst, flowEnv, appIndexOffset, dispatchFlowDeps
  },
  errors {
    config, grammarName, env, frame, compiledGrammars, appExprTypereps, appExprApplied,
    downSubst, finalSubst, flowEnv, decSiteVertexInfo, dispatchFlowDeps, appProd, appIndexOffset
  };

tracked nonterminal AppExpr with
  config, grammarName, env, unparse, errors, freeVars, frame, compiledGrammars, exprs, rawExprs,
  isPartial, missingTypereps, appExprIndicies, appExprIndex, appExprTyperep, appExprApplied, originRules;
flowtype AppExpr =
  decorate {
    config, grammarName, env, frame, compiledGrammars, appExprIndex, appExprTyperep, appExprApplied, originRules,
    downSubst, finalSubst, flowEnv, appIndexOffset, dispatchFlowDeps
  },
  errors {
    config, grammarName, env, frame, compiledGrammars, appExprIndex, appExprTyperep, appExprApplied,
    downSubst, finalSubst, flowEnv, decSiteVertexInfo, dispatchFlowDeps, appProd, appIndexOffset
  };

propagate config, grammarName, env, freeVars, frame, compiledGrammars, errors, originRules on AppExprs, AppExpr;
propagate appExprApplied, exprs, rawExprs on AppExprs;

synthesized attribute isPartial :: Boolean;
synthesized attribute missingTypereps :: [Type];
synthesized attribute appExprIndicies :: [Integer];
synthesized attribute appExprSize :: Integer;
inherited attribute appExprIndex :: Integer;
inherited attribute appExprTypereps :: [Type];
inherited attribute appExprTyperep :: Type;
inherited attribute appExprApplied :: String;

-- These are the "new" Exprs syntax. This allows missing (_) arguments, to indicate partial application.
concrete production missingAppExpr
top::AppExpr ::= '_'
{
  top.unparse = "_";
  
  top.isPartial = true;
  top.missingTypereps = [top.appExprTyperep];
  
  top.rawExprs := [];
  top.exprs := [];
  top.appExprIndicies = [];
}
concrete production presentAppExpr
top::AppExpr ::= e::Expr
{
  top.unparse = e.unparse;
  
  top.isPartial = false;
  top.missingTypereps = [];
  
  top.rawExprs := [^e];
  top.exprs := [e];
  top.appExprIndicies = [top.appExprIndex];

  e.isRoot = false;
}

concrete production snocAppExprs
top::AppExprs ::= es::AppExprs ',' e::AppExpr
{
  top.unparse = es.unparse ++ ", " ++ e.unparse;

  top.isPartial = es.isPartial || e.isPartial;
  top.missingTypereps = es.missingTypereps ++ e.missingTypereps;

  top.appExprIndicies = es.appExprIndicies ++ e.appExprIndicies;

  top.appExprSize = es.appExprSize + 1;

  e.appExprIndex = es.appExprSize;
  e.appExprTyperep =
    if null(top.appExprTypereps)
    then errorType()
    else head(top.appExprTypereps);
  
  es.appExprTypereps =
    if null(top.appExprTypereps) then [] else tail(top.appExprTypereps);
}
concrete production oneAppExprs
top::AppExprs ::= e::AppExpr
{
  top.unparse = e.unparse;

  top.isPartial = e.isPartial;
  top.missingTypereps = e.missingTypereps;

  top.appExprIndicies = e.appExprIndicies;
  
  top.appExprSize = 1;

  e.appExprIndex = 0;
  e.appExprTyperep =
    if null(top.appExprTypereps)
    then errorType()
    else head(top.appExprTypereps);
}
abstract production emptyAppExprs
top::AppExprs ::=
{
  top.unparse = "";

  top.isPartial = false;
  top.missingTypereps = [];

  top.appExprIndicies = [];
  top.appExprSize = 0;

  -- Assumption: We only get here when we're looking at ()
  -- i.e. we can't ever have 'too many' provided error
  top.errors <- if null(top.appExprTypereps) then []
                else [errFromOrigin(top, "Too few arguments provided to function '" ++ top.appExprApplied ++ "'")];
}


tracked nonterminal AnnoAppExprs with
  config, grammarName, env, unparse, errors, freeVars, frame, compiledGrammars,
  isPartial, appExprApplied, exprs, appExprSize,
  remainingFuncAnnotations, funcAnnotations,
  missingAnnotations, partialAnnoTypereps, annoIndexConverted, annoIndexSupplied, originRules;
tracked nonterminal AnnoExpr with
  config, grammarName, env, unparse, errors, freeVars, frame, compiledGrammars,
  isPartial, appExprApplied, exprs,
  remainingFuncAnnotations, funcAnnotations,
  missingAnnotations, partialAnnoTypereps, annoIndexConverted, annoIndexSupplied, originRules;
flowtype decorate {
    grammarName, env, flowEnv, downSubst, finalSubst, frame, originRules, compiledGrammars, config,
    appExprApplied, remainingFuncAnnotations, funcAnnotations
  } on AnnoAppExprs, AnnoExpr;
flowtype errors {
    grammarName, env, flowEnv, downSubst, finalSubst, frame, compiledGrammars, config,
    appExprApplied, remainingFuncAnnotations, funcAnnotations
  } on AnnoAppExprs, AnnoExpr;

propagate config, grammarName, env, errors, freeVars, frame, compiledGrammars, exprs, funcAnnotations, appExprApplied, originRules
  on AnnoAppExprs, AnnoExpr;

{--
 - Annotations that have not yet been supplied
 -}
inherited attribute remainingFuncAnnotations :: [(String, Type)];
{--
 - All annotations of this function
 -}
inherited attribute funcAnnotations :: [(String, Type)];
{--
 - Annotations that have not been supplied (by subtracting from remainingFuncAnnotations)
 -}
synthesized attribute missingAnnotations :: [(String, Type)];
{--
 - Typereps of those annotations that are partial (_)
 -}
synthesized attribute partialAnnoTypereps :: [Type];

synthesized attribute annoIndexConverted :: [Integer];
synthesized attribute annoIndexSupplied :: [Integer];

concrete production annoExpr
top::AnnoExpr ::= qn::QName '=' e::AppExpr
{
  top.unparse = qn.unparse ++ "=" ++ e.unparse;
  
  local fq :: (Maybe<(String, Type)>, [(String, Type)]) =
    extractNamedArg(qn.name, top.remainingFuncAnnotations);
    
  e.appExprIndex =
    findNamedArgType(qn.name, top.funcAnnotations, 0);
  e.appExprTyperep =
    if fq.fst.isJust then fq.fst.fromJust.snd else errorType();
    
  top.missingAnnotations = fq.snd; -- minus qn, if it was there
  top.partialAnnoTypereps = e.missingTypereps;
  
  top.errors <-
    if fq.fst.isJust then []
    else [errFromOrigin(qn, "Named parameter '" ++ qn.name ++ "' is not appropriate for '" ++ top.appExprApplied ++ "'")];
  top.isPartial = e.isPartial;
  top.annoIndexConverted =
    if e.isPartial then [e.appExprIndex] else [];
  top.annoIndexSupplied =
    if e.isPartial then [] else [e.appExprIndex];
}

concrete production snocAnnoAppExprs
top::AnnoAppExprs ::= es::AnnoAppExprs ',' e::AnnoExpr
{
  top.unparse = es.unparse ++ ", " ++ e.unparse;

  top.isPartial = es.isPartial || e.isPartial;
  top.appExprSize = 1 + es.appExprSize;

  e.remainingFuncAnnotations = top.remainingFuncAnnotations;
  es.remainingFuncAnnotations = e.missingAnnotations;
  top.missingAnnotations = es.missingAnnotations;
  
  top.partialAnnoTypereps = es.partialAnnoTypereps ++ e.partialAnnoTypereps;
  top.annoIndexConverted = es.annoIndexConverted ++ e.annoIndexConverted;
  top.annoIndexSupplied = es.annoIndexSupplied ++ e.annoIndexSupplied;
}

concrete production oneAnnoAppExprs
top::AnnoAppExprs ::= e::AnnoExpr
{
  top.unparse = e.unparse;

  top.isPartial = e.isPartial;
  top.appExprSize = 1;
  top.errors <-
    if null(top.missingAnnotations) then []
    else [errFromOrigin(top, "Missing named parameters for function '" ++ top.appExprApplied ++ "': "
      ++ implode(", ", map(fst, top.missingAnnotations)))];

  e.remainingFuncAnnotations = top.remainingFuncAnnotations;
  top.missingAnnotations = e.missingAnnotations;

  top.partialAnnoTypereps = e.partialAnnoTypereps;
  top.annoIndexConverted = e.annoIndexConverted;
  top.annoIndexSupplied = e.annoIndexSupplied;
}

abstract production emptyAnnoAppExprs
top::AnnoAppExprs ::=
{
  top.unparse = "";

  top.isPartial = false;
  top.appExprSize = 0;
  top.errors <-
    if null(top.missingAnnotations) then []
    else [errFromOrigin(top, "Missing named parameters for function '" ++ top.appExprApplied ++ "': "
      ++ implode(", ", map(fst, top.missingAnnotations)))];

  top.missingAnnotations = top.remainingFuncAnnotations;
  
  top.partialAnnoTypereps = [];
  top.annoIndexConverted = [];
  top.annoIndexSupplied = [];
}

fun reorderedAnnoAppExprs [Decorated Expr] ::= d::Decorated AnnoAppExprs =
  map(snd, sortBy(reorderedLte, zip(d.annoIndexSupplied, d.exprs)));
fun reorderedLte Boolean ::= l::(Integer, Decorated Expr)  r::(Integer, Decorated Expr) =
  l.fst <= r.fst;

function extractNamedArg
(Maybe<(String, Type)>, [(String, Type)]) ::= n::String  l::[(String, Type)]
{
  local recurse :: (Maybe<(String, Type)>, [(String, Type)]) =
    extractNamedArg(n, tail(l));

  return if null(l) then (nothing(), [])
  else if head(l).fst == n then (just(head(l)), tail(l))
  else (recurse.fst, head(l) :: recurse.snd);
}

fun findNamedArgType Integer ::= s::String l::[(String, Type)] z::Integer =
  if null(l) then -1
else if s == head(l).fst then z
else findNamedArgType(s, tail(l), z+1);


{--
 - Utility for other modules to create function invocations.
 - This makes no assumptions, use it any way you wish!
 -}
fun mkStrFunctionInvocation Expr ::= e::String  es::[Expr] =
  mkFullFunctionInvocation(baseExpr(qName(e)), es, []);
fun mkFunctionInvocation Expr ::= e::Expr  es::[Expr] = mkFullFunctionInvocation(e, es, []);
fun mkFullFunctionInvocation Expr ::= e::Expr  es::[Expr]  ans::[Pair<String Expr>] =
  application(e, '(',
    foldl(snocAppExprs(_, ',', _), emptyAppExprs(),
      map(presentAppExpr, es)),
    ',',
    foldl(snocAnnoAppExprs(_, ',', _), emptyAnnoAppExprs(),
      map(mkAnnoExpr, ans)),
    ')');
-- Internal helper function
fun mkAnnoExpr AnnoExpr ::= p::Pair<String Expr> =
  annoExpr(qName(p.fst), '=', presentAppExpr(p.snd));

{--
 - Note on the use of the 'decorated here' (@) operator with already-decorated expressions:
 - 
 - There is one MAJOR restriction on the use of this operator:
 -   The referenced expression MUST APPEAR in the same expression tree
 -   as it is referenced in.
 -
 - This is for type information reasons: the subtree referenced must have been
 - typechecked in the same 'typing context' as wherever this tree appears.
 -
 - This is trivially satisfied for the typical use case for this operator,
 - where you're typechecking your children, then forwarding to some tree with
 - references to those children.
 -}