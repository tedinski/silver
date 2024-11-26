grammar silver:compiler:extension:implicit_monads;


terminal Implicit_kwd    'implicit'     lexer classes {KEYWORD,RESERVED};
terminal Restricted_kwd    'restricted'     lexer classes {KEYWORD,RESERVED};
terminal Unrestricted_kwd    'unrestricted'     lexer classes {KEYWORD,RESERVED};



--Write an empty equation filled in by an appropriate fail
--We want to keep the 'implicit' keyword here so people don't accidentally write empty equations
concrete production emptyAttributeDef
top::ProductionStmt ::= 'implicit' dl::DefLHS '.' attr::QNameAttrOccur '=' ';'
{
  top.unparse = "\timplicit " ++ dl.unparse ++ "." ++ attr.unparse ++ " = ;";
  propagate grammarName, compiledGrammars, config, frame, env, flowEnv;

  top.productionAttributes := [];
  top.defs := [];
  top.forwardExpr := [];
  top.returnExpr := [];

  top.containsPluck = false;

  local merrors::[Message] =
    (if isMonadFail(attr.typerep, top.env)
     then []
     else [errFromOrigin(top, monadToString(attr.typerep) ++
               " is not an instance of MonadFail and cannot " ++
               "be used in an empty equation")]) ++
     ( if attr.found && dl.found
       then case attr.attrDcl of
            | implicitInhDcl(_, _, _) -> []
            | implicitSynDcl(_, _, _) -> []
            | _ -> [errFromOrigin(top, "Implicit equations can only be used for " ++
                                      "attributes declared to be implicit; " ++
                                      attr.unparse ++ " is not implicit")]
            end
       else dl.errors ++ attr.errors );

  dl.defLHSattr = attr;
  attr.attrFor = dl.typerep;

  forwards to
     if null(merrors)
     then attr.attrDcl.attrDefDispatcher(dl, attr, monadFail())
     else errorProductionStmt(merrors);
}


concrete production implicitAttributeDef
top::ProductionStmt ::= 'implicit' dl::DefLHS '.' attr::QNameAttrOccur '=' e::Expr ';'
{
  top.unparse = "\timplicit" ++ dl.unparse ++ "." ++ attr.unparse ++ " = ;";
  propagate grammarName, compiledGrammars, config, frame, env, flowEnv;

  top.productionAttributes := [];
  top.defs := [];
  top.forwardExpr := [];
  top.returnExpr := [];

  top.containsPluck = false;

  local merrors::[Message] =
       if attr.found && dl.found
       then case attr.attrDcl of
            | implicitSynDcl(_, _, _) -> []
            | implicitInhDcl(_, _, _) -> []
            | _ -> [errFromOrigin(top, "Implicit equations can only be used for " ++
                                      "attributes declared to be implicit; " ++
                                      attr.unparse ++ " is not implicit")]
            end
       else [];

  dl.defLHSattr = attr;
  attr.attrFor = dl.typerep;

  forwards to
          if null(merrors)
          then if attr.found
               then attr.attrDcl.attrDefDispatcher(dl, attr, @e)
                    --if not found, let the normal dispatcher handle it
               else attributeDef(^dl, '.', ^attr, '=', @e, ';')
          else errorAttributeDef(dl, attr, @e, merrors);
}




concrete production restrictedAttributeDef
top::ProductionStmt ::= 'restricted' dl::DefLHS '.' attr::QNameAttrOccur '=' e::Expr ';'
{
  e.downSubst = top.downSubst;
  top.unparse = "\trestricted" ++ dl.unparse ++ "." ++ attr.unparse ++ " = ;";
  propagate grammarName, compiledGrammars, config, frame, env, flowEnv;

  top.productionAttributes := [];
  top.defs := [];
  top.forwardExpr := [];
  top.returnExpr := [];

  top.containsPluck = false;

  local merrors::[Message] =
    if attr.found && dl.found
    then case attr.attrDcl of
         | restrictedSynDcl(_, _, _) -> []
         | restrictedInhDcl(_, _, _) -> []
         | _ -> [errFromOrigin(top, "Restricted equations can only be used for " ++
                                   "attributes declared to be restricted; " ++
                                   attr.unparse ++ " is not restricted")]
         end
    else [];

  dl.defLHSattr = attr;
  attr.attrFor = dl.typerep;

  forwards to
          if null(merrors)
          then if attr.found
               then attr.attrDcl.attrDefDispatcher(dl, attr, @e)
                    --if not found, let the normal dispatcher handle it
               else attributeDef(^dl, '.', ^attr, '=', @e, ';')
          else errorAttributeDef(dl, attr, @e, merrors);
}




concrete production unrestrictedAttributeDef
top::ProductionStmt ::= 'unrestricted' dl::DefLHS '.' attr::QNameAttrOccur '=' e::Expr ';'
{
  top.unparse = "\tunrestricted" ++ dl.unparse ++ "." ++ attr.unparse ++ " = ;";
  propagate grammarName, compiledGrammars, config, frame, env, flowEnv;

  top.productionAttributes := [];
  top.defs := [];
  top.forwardExpr := [];
  top.returnExpr := [];

  dl.defLHSattr = attr;
  attr.attrFor = dl.typerep;

  top.containsPluck = false;

  local restrictedErr::[Message] =
           [errFromOrigin(top,
                "Unrestricted equations can only be used for attributes " ++
                "not declared to be restricted or implicit; " ++ attr.unparse ++ " is restricted")];
  local implicitErr::[Message] =
           [errFromOrigin(top,
                "Unrestricted equations can only be used for attributes " ++
                "not declared to be restricted or implicit; " ++ attr.unparse ++ " is implicit")];
  forwards to
          if attr.found
          then case attr.attrDcl of
               | restrictedSynDcl(_, _, _) -> errorAttributeDef(dl, attr, @e, restrictedErr)
               | restrictedInhDcl(_, _, _) -> errorAttributeDef(dl, attr, @e, restrictedErr)
               | implicitSynDcl(_, _, _) -> errorAttributeDef(dl, attr, @e, implicitErr)
               | implicitInhDcl(_, _, _) -> errorAttributeDef(dl, attr, @e, implicitErr)
               | _ -> attributeDef(^dl, '.', ^attr, '=', @e, ';')
               end
          --if not found, let the normal dispatcher handle it
          else attributeDef(^dl, '.', ^attr, '=', @e, ';');
}






--take a list of unallowed attributes and generate error messages for them
fun buildExplicitAttrErrors [Message] ::= l::[Decorated QNameAttrOccur] =
  case l of
  | [] -> []
  | a::t ->
    errFromOrigin(a, "Attributes accessed in restricted equations must be restricted; " ++
              a.name ++ " is not")::buildExplicitAttrErrors(t)
  end;



--productions for error checking on restricted attributes
abstract production restrictedSynAttributeDef implements AttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  top.unparse = dl.unparse ++ "." ++ attr.unparse ++ " = " ++ e.unparse ++ ";";
  propagate grammarName, compiledGrammars, config, frame, env, flowEnv, finalSubst;

  e.downSubst = top.downSubst;
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
  e.isRoot = true;

  top.containsPluck = false;
  top.forwardExpr := [];
  top.returnExpr := [];

  local merrors::[Message] =
     --gives errors for implicit/unrestricted attributes used
     buildExplicitAttrErrors(e.notExplicitAttributes);

  forwards to
    if null(merrors)
    then synthesizedAttributeDef(dl, attr, @e)
    else errorAttributeDef(dl, attr, @e, merrors);
}


abstract production restrictedInhAttributeDef implements AttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  top.unparse = dl.unparse ++ "." ++ attr.unparse ++ " = " ++ e.unparse ++ ";";
  propagate grammarName, compiledGrammars, config, frame, env, flowEnv, finalSubst;

  e.downSubst = top.downSubst;
  e.decSiteVertexInfo = nothing();
  e.alwaysDecorated = false;
  e.appDecSiteVertexInfo = nothing();
  e.dispatchFlowDeps = [];
  e.isRoot = true;

  top.containsPluck = false;
  top.forwardExpr := [];
  top.returnExpr := [];

  local merrors::[Message] =
     --gives errors for implicit/unrestricted attributes used
     buildExplicitAttrErrors(e.notExplicitAttributes);

  forwards to
    if null(merrors)
    then inheritedAttributeDef(dl, attr, @e)
    else errorAttributeDef(dl, attr, @e, merrors);
}




--productions for error checking on implicit attributes
abstract production implicitSynAttributeDef implements AttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  top.unparse = dl.unparse ++ "." ++ attr.unparse ++ " = " ++ e.unparse ++ ";";

  local checkE::Expr = ^e;
  checkE.grammarName = top.grammarName;
  checkE.compiledGrammars = top.compiledGrammars;
  checkE.config = top.config;
  checkE.frame = top.frame;
  checkE.env = top.env;
  checkE.flowEnv = top.flowEnv;
  checkE.downSubst = top.downSubst;
  checkE.mDownSubst = top.downSubst;
  checkE.finalSubst = checkE.mUpSubst;
  checkE.decSiteVertexInfo = nothing();
  checkE.alwaysDecorated = false;
  checkE.appDecSiteVertexInfo = nothing();
  checkE.dispatchFlowDeps = [];
  checkE.isRoot = true;
  checkE.expectedMonad = attr.typerep;

  top.containsPluck = false;
  top.forwardExpr := [];
  top.returnExpr := [];

  local fwrdProd::AttributeDef = 
     if !null(checkE.merrors)
     then errorAttributeDef(checkE.merrors)
     else if  fst(monadsMatch(attr.typerep, checkE.mtyperep, checkE.mUpSubst))
     then transformExprAttributeDef(synthesizedAttributeDef, checkE.monadRewritten)
     else transformExprAttributeDef(synthesizedAttributeDef,
       Silver_Expr {
       $Expr {monadReturn()}
            ($Expr {checkE.monadRewritten})
       });

  forwards to fwrdProd(dl, attr, @e);
}


abstract production implicitInhAttributeDef implements AttributeDef
top::ProductionStmt ::= @dl::DefLHS @attr::QNameAttrOccur e::Expr
{
  top.unparse = dl.unparse ++ "." ++ attr.unparse ++ " = " ++ e.unparse ++ ";";

  local checkE::Expr = ^e;
  checkE.grammarName = top.grammarName;
  checkE.compiledGrammars = top.compiledGrammars;
  checkE.config = top.config;
  checkE.frame = top.frame;
  checkE.env = top.env;
  checkE.flowEnv = top.flowEnv;
  checkE.downSubst = top.downSubst;
  checkE.mDownSubst = top.downSubst;
  checkE.finalSubst = checkE.mUpSubst;
  checkE.decSiteVertexInfo = nothing();
  checkE.alwaysDecorated = false;
  checkE.appDecSiteVertexInfo = nothing();
  checkE.dispatchFlowDeps = [];
  checkE.isRoot = true;
  checkE.expectedMonad = attr.typerep;

  top.containsPluck = false;
  top.forwardExpr := [];
  top.returnExpr := [];

  local fwrdProd::AttributeDef = 
     if !null(checkE.merrors)
     then errorAttributeDef(checkE.merrors)
     else if  fst(monadsMatch(attr.typerep, checkE.mtyperep, checkE.mUpSubst))
     then transformExprAttributeDef(inheritedAttributeDef, checkE.monadRewritten)
     else transformExprAttributeDef(inheritedAttributeDef,
       Silver_Expr {
       $Expr {monadReturn()}
            ($Expr {checkE.monadRewritten})
       });

  forwards to fwrdProd(dl, attr, @e);
}

