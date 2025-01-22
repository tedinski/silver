grammar silver:compiler:extension:deriving;

import silver:compiler:extension:patternmatching only Arrow_kwd, Vbar_kwd;

terminal Derive_t 'derive' lexer classes {KEYWORD};

concrete production deriveTCsOnNTListDcl_c
top::AGDcl ::= 'derive' tcs::NameList 'on' nts::NameList ';'
{
  top.unparse = s"derive ${tcs.unparse} on ${nts.unparse};";
  
  forwards to deriveTCsOnNTListDcl(@tcs, @nts);
}

production deriveTCsOnNTListDcl
top::AGDcl ::= tcs::NameList nts::NameList
{
  top.unparse = s"derive ${tcs.unparse} on ${nts.unparse};";
  
  forwards to
    case nts of
    | nameListOne(n) -> deriveTCsOnOneNTDcl(@tcs, ^n)
    | nameListCons(n, _, rest) ->
      appendAGDcl(
        deriveTCsOnOneNTDcl(@tcs, ^n),
        deriveTCsOnNTListDcl(^tcs, ^rest))
    end;
}

production deriveTCsOnOneNTDcl
top::AGDcl ::= tcs::NameList nt::QName
{
  top.unparse = s"derive ${tcs.unparse} on ${nt.unparse};";
  
  forwards to
    case tcs of
    | nameListOne(tc) -> deriveDcl(^tc, @nt)
    | nameListCons(tc, _, rest) ->
      appendAGDcl(
        deriveDcl(^tc, @nt),
        deriveTCsOnOneNTDcl(^rest, ^nt))
    end;
}

production deriveDcl
top::AGDcl ::= tc::QName nt::QName
{
  top.unparse = s"derive ${tc.unparse} on ${nt.unparse};";
  top.moduleNames := [];
  propagate env;

  local localErrors::[Message] =
    tc.lookupType.errors ++ nt.lookupType.errors ++
    (if tc.lookupType.found && !tc.lookupType.dcl.isClass
     then [errFromOrigin(tc, s"${tc.lookupType.fullName} is not a type class")]
     else []) ++
    (if nt.lookupType.found && !(nt.lookupType.dcl.isType && nt.lookupType.typeScheme.isNonterminal)
     then [errFromOrigin(nt, s"${nt.lookupType.fullName} is not a nonterminal")]
     else []) ++
    (if nt.lookupType.found && nt.lookupType.dcl.isClosed
     then [errFromOrigin(nt, s"Cannot derive instances for ${nt.lookupType.fullName}, since that nonterminal is closed")]
     else []);
  top.errors := if null(localErrors) then forward.errors else localErrors;

  forwards to
    -- TODO: Yuck, can't forward based on env here since we need the defs from the forward.
    case if startsWith("silver:core:", tc.name) then tc.name else "silver:core:" ++ tc.name of  -- tc.lookupType.fullName
    | "silver:core:Eq" -> deriveEqDcl(nt)
    | "silver:core:Ord" -> deriveOrdDcl(nt)
    | fn -> errorAGDcl([errFromOrigin(tc, s"Cannot derive type class ${fn}")])
    end;
}

dispatch Derive = AGDcl ::= @nt::QName;

production deriveEqDcl implements Derive
top::AGDcl ::= @nt::QName
{
  top.unparse = s"derive silver:core:Eq on ${nt.unparse};";
  top.moduleNames := [];

  local tvs::[TyVar] = map(freshTyVar, nt.lookupType.dcl.kindrep.argKinds);
  nondecorated local ntty::Type = appTypes(nt.lookupType.typeScheme.monoType, map(skolemType, tvs));
  
  local includedProds::[ValueDclInfo] =
    filter(
      \ d::ValueDclInfo -> !d.hasForward,
      getKnownProds(nt.lookupType.fullName, top.env));
  forwards to Silver_AGDcl {
    instance $ConstraintList{
      foldr(
        consConstraint(_, ',', _),
        nilConstraint(),
        filterMap(
          \ tv::TyVar ->
            if tv.kind == starKind()
            then just(
              classConstraint(
                qName("silver:core:Eq").qNameType,
                typerepTypeExpr(skolemType(tv))))
            else nothing(),
          tvs))} => silver:core:Eq $TypeExpr{typerepTypeExpr(ntty)} {
        eq = \ x::$TypeExpr{typerepTypeExpr(ntty)} y::$TypeExpr{typerepTypeExpr(ntty)} -> $Expr{
          if null(includedProds) then Silver_Expr {true} else
          foldr(
            -- and(_, '&&', _), -- luke removal, replace with `_ && _` when jars build
            \e1::Expr e2::Expr -> Silver_Expr { silver:core:conj(e1, e2) }, -- luke addition for build
            matchPrimitive(
              Silver_Expr {x},
              Silver_TypeExpr {Boolean},
              foldPrimPatterns(
                map(
                  \ prod::ValueDclInfo ->
                    prodPattern(qName(prod.fullName), '(',
                    foldr(
                      consVarBinder(_, ',', _),
                      nilVarBinder(),
                      map(\ i::Integer ->
                        varVarBinder(name(s"a${toString(i)}")),
                        range(0, length(prod.namedSignature.inputElements)))), ')', '->',
                    matchPrimitive(
                      Silver_Expr {y},
                      Silver_TypeExpr {Boolean},
                      onePattern(
                        prodPattern(qName(prod.fullName), '(',
                          foldr(
                            consVarBinder(_, ',', _),
                            nilVarBinder(),
                            map(\ i::Integer ->
                              varVarBinder(name(s"b${toString(i)}")),
                              range(0, length(prod.namedSignature.inputElements)))), ')', '->',
                          foldr(
                            -- and(_, '&&', _), -- luke removal, replace with `_ && _` when jars build
                            \e1::Expr e2::Expr -> Silver_Expr { silver:core:conj(e1, e2) }, -- luke addition for build
                            Silver_Expr {true},
                            map(
                              \ ie::(Integer, NamedSignatureElement) ->
                                if isDecorable(ie.2.elementDclType, top.env)
                                then Silver_Expr { new($name{s"a${toString(ie.1)}"}) == new($name{s"b${toString(ie.1)}"}) }
                                else Silver_Expr { $name{s"a${toString(ie.1)}"} == $name{s"b${toString(ie.1)}"} },
                              enumerate(prod.namedSignature.inputElements))))),
                      Silver_Expr {false})),
                  includedProds)),
              Silver_Expr {silver:core:error("Unexpected production in derived Eq instance!")}),
            map(
              \ anno::NamedSignatureElement ->
                Silver_Expr { x.$name{anno.elementName} == y.$name{anno.elementName} },
              annotationsForNonterminal(ntty, top.env)))};
        neq = \ x::$TypeExpr{typerepTypeExpr(ntty)} y::$TypeExpr{typerepTypeExpr(ntty)} -> $Expr{
          if null(includedProds) then Silver_Expr {false} else
          foldr(
            or(_, '||', _),
            matchPrimitive(
              Silver_Expr {x},
              Silver_TypeExpr {Boolean},
              foldPrimPatterns(
                map(
                  \ prod::ValueDclInfo ->
                    prodPattern(qName(prod.fullName), '(',
                    foldr(
                      consVarBinder(_, ',', _),
                      nilVarBinder(),
                      map(\ i::Integer ->
                        varVarBinder(name(s"a${toString(i)}")),
                        range(0, length(prod.namedSignature.inputElements)))), ')', '->',
                    matchPrimitive(
                      Silver_Expr {y},
                      Silver_TypeExpr {Boolean},
                      onePattern(
                        prodPattern(qName(prod.fullName), '(',
                          foldr(
                            consVarBinder(_, ',', _),
                            nilVarBinder(),
                            map(\ i::Integer ->
                              varVarBinder(name(s"b${toString(i)}")),
                              range(0, length(prod.namedSignature.inputElements)))), ')', '->',
                          foldr(
                            or(_, '||', _),
                            Silver_Expr {false},
                            map(
                              \ ie::(Integer, NamedSignatureElement) ->
                                if isDecorable(ie.2.elementDclType, top.env)
                                then Silver_Expr { new($name{s"a${toString(ie.1)}"}) != new($name{s"b${toString(ie.1)}"}) }
                                else Silver_Expr { $name{s"a${toString(ie.1)}"} != $name{s"b${toString(ie.1)}"} },
                              enumerate(prod.namedSignature.inputElements))))),
                      Silver_Expr {true})),
                  includedProds)),
              Silver_Expr {silver:core:error("Unexpected production in derived Eq instance!")}),
            map(
              \ anno::NamedSignatureElement ->
                Silver_Expr { x.$name{anno.elementName} != y.$name{anno.elementName} },
              annotationsForNonterminal(ntty, top.env)))};
      }
  };
}

production deriveOrdDcl implements Derive
top::AGDcl ::= @nt::QName
{
  top.unparse = s"derive silver:core:Ord on ${nt.unparse};";
  top.moduleNames := [];

  local tvs::[TyVar] = map(freshTyVar, nt.lookupType.dcl.kindrep.argKinds);
  nondecorated local ntty::Type = appTypes(nt.lookupType.typeScheme.monoType, map(skolemType, tvs));
  
  local includedProds::[ValueDclInfo] =
    filter(
      \ d::ValueDclInfo -> !d.hasForward,
      getKnownProds(nt.lookupType.fullName, top.env));

  forwards to Silver_AGDcl {
    instance $ConstraintList{
      foldr(
        consConstraint(_, ',', _),
        nilConstraint(),
        filterMap(
          \ tv::TyVar ->
            if tv.kind == starKind()
            then just(
              classConstraint(
                qName("silver:core:Ord").qNameType,
                typerepTypeExpr(skolemType(tv))))
            else nothing(),
          tvs))} => silver:core:Ord $TypeExpr{typerepTypeExpr(ntty)} {
        compare = \ x::$TypeExpr{typerepTypeExpr(ntty)} y::$TypeExpr{typerepTypeExpr(ntty)} -> $Expr{
          if null(includedProds) then Silver_Expr { 0 } else
          foldr(
            \ e1::Expr e2::Expr ->
              Silver_Expr { let res::Integer = $Expr{e1} in if res == 0 then $Expr{e2} else res end },
            matchPrimitive(
              Silver_Expr {x},
              Silver_TypeExpr {Integer},
              foldPrimPatterns(
                map(
                  \ prod::ValueDclInfo ->
                    prodPattern(qName(prod.fullName), '(',
                    foldr(
                      consVarBinder(_, ',', _),
                      nilVarBinder(),
                      map(\ i::Integer ->
                        varVarBinder(name(s"a${toString(i)}")),
                        range(0, length(prod.namedSignature.inputElements)))), ')', '->',
                    matchPrimitive(
                      Silver_Expr {y},
                      Silver_TypeExpr {Integer},
                      foldPrimPatterns(
                        map(
                          \ prod2::ValueDclInfo ->
                            prodPattern(
                              qName(prod2.fullName), '(',
                              foldr(
                                consVarBinder(_, ',', _),
                                nilVarBinder(),
                                map(
                                  \ i::Integer ->
                                    if prod.fullName == prod2.fullName
                                    then varVarBinder(name(s"b${toString(i)}"))
                                    else ignoreVarBinder('_'),
                                  range(0, length(prod2.namedSignature.inputElements)))), ')', '->',
                              if prod.fullName < prod2.fullName
                              then Silver_Expr { -1 }
                              else if prod.fullName > prod2.fullName
                              then Silver_Expr { 1 }
                              else if null(prod2.namedSignature.inputElements)
                              then Silver_Expr { 0 }
                              else foldr1(
                                \ e1::Expr e2::Expr ->
                                  Silver_Expr { let res::Integer = $Expr{e1} in if res == 0 then $Expr{e2} else res end },
                                map(
                              \ ie::(Integer, NamedSignatureElement) ->
                                if isDecorable(ie.2.elementDclType, top.env)
                                then Silver_Expr { silver:core:compare(new($name{s"a${toString(ie.1)}"}), new($name{s"b${toString(ie.1)}"})) }
                                else Silver_Expr { silver:core:compare($name{s"a${toString(ie.1)}"}, $name{s"b${toString(ie.1)}"}) },
                              enumerate(prod.namedSignature.inputElements)))),
                          includedProds)),
                      Silver_Expr {silver:core:error("Unexpected production in derived Ord instance!")})),
                  includedProds)),
              Silver_Expr {silver:core:error("Unexpected production in derived Ord instance!")}),
            map(
              \ anno::NamedSignatureElement ->
                Silver_Expr { silver:core:compare(x.$name{anno.elementName}, y.$name{anno.elementName}) },
              annotationsForNonterminal(ntty, top.env)))};
      }
  };
}

fun foldPrimPatterns PrimPatterns ::= ps::[PrimPattern] =
  case ps of
  | [h] -> onePattern(h)
  | h :: t -> consPattern(h, '|', foldPrimPatterns(t))
  | [] -> error("empty patterns")
  end;
