grammar silver:compiler:translation:java:type;

import silver:compiler:definition:env;

-- Translation of *solved* contexts, not *constraint* contexts
synthesized attribute transContexts::[String] occurs on Contexts;
synthesized attribute transTypeableContexts::[String] occurs on Contexts; -- Hack to inject varTypeRep bindings
synthesized attribute transContextSuperAccessors::String occurs on Contexts;

aspect production consContext
top::Contexts ::= h::Context t::Contexts
{
  top.transContexts = h.transContext :: t.transContexts;
  top.transTypeableContexts = h.transTypeableContext :: t.transTypeableContexts;
  top.transContextSuperAccessors = h.transContextSuperAccessor ++ t.transContextSuperAccessors;
}
aspect production nilContext
top::Contexts ::=
{
  top.transContexts = [];
  top.transTypeableContexts = [];
  top.transContextSuperAccessors = "";
}

attribute transType occurs on Context;
synthesized attribute transContext::String occurs on Context;
synthesized attribute transTypeableContext::String occurs on Context;

synthesized attribute transContextMemberName::String occurs on Context;
synthesized attribute transContextSuperAccessorName::String occurs on Context;
synthesized attribute transContextSuperAccessor::String occurs on Context;

aspect default production
top::Context ::=
{
  top.transTypeableContext = top.transContext; -- Shouldn't be demanded?
}

aspect production instContext
top::Context ::= fn::String t::Type
{
  top.transType = makeClassName(fn);
  
  resolvedDcl.transContextDeps = requiredContexts.transContexts;
  top.transContext = resolvedDcl.transContext;
  
  top.transContextMemberName = makeConstraintDictName(fn, t, top.boundVariables);
  top.transContextSuperAccessorName = makeInstanceSuperAccessorName(fn);
  top.transContextSuperAccessor = s"""
	public final ${top.transType} ${top.transContextSuperAccessorName}() {
		return ${top.transContext};
	}
""";
}

aspect production inhOccursContext
top::Context ::= attr::String args::[Type] atty::Type ntty::Type
{
  top.transType = "int";
  
  resolvedDcl.transContextDeps = requiredContexts.transContexts;
  top.transContext = resolvedDcl.transContext;
  
  top.transContextMemberName = makeConstraintDictName(attr, ntty, top.boundVariables);
  top.transContextSuperAccessorName = makeInstanceSuperAccessorName(attr);
  top.transContextSuperAccessor = s"""
	public final ${top.transType} ${top.transContextSuperAccessorName}() {
		return ${top.transContext};
	}
""";
}

aspect production synOccursContext
top::Context ::= attr::String args::[Type] atty::Type inhs::Type ntty::Type
{
  top.transType = "int";
  
  resolvedDcl.transContextDeps = requiredContexts.transContexts;
  top.transContext = resolvedDcl.transContext;
  
  top.transContextMemberName = makeConstraintDictName(attr, ntty, top.boundVariables);
  top.transContextSuperAccessorName = makeInstanceSuperAccessorName(attr);
  top.transContextSuperAccessor = s"""
	public final ${top.transType} ${top.transContextSuperAccessorName}() {
		return ${top.transContext};
	}
""";
}

aspect production annoOccursContext
top::Context ::= attr::String args::[Type] atty::Type ntty::Type
{
  -- This doesn't actually encode any runtime information, for now...
  top.transType = "Object";
  top.transContext = "null";
  top.transContextMemberName = makeConstraintDictName(attr, ntty, top.boundVariables);
  top.transContextSuperAccessorName = makeInstanceSuperAccessorName(attr);
  top.transContextSuperAccessor = s"""
	public final ${top.transType} ${top.transContextSuperAccessorName}() {
		return ${top.transContext};
	}
""";
}

aspect production typeableContext
top::Context ::= t::Type
{
  top.transType = "common.TypeRep";
  
  t.skolemTypeReps = zipWith(pair, t.freeVariables, requiredContexts.transTypeableContexts);
  resolvedDcl.transContextDeps = requiredContexts.transTypeableContexts;
  top.transTypeableContext =
    case top.resolved, t of
    -- We might need translate this context even when resolution fails;
    -- in that case fall back to a rigid skolem constant.
    | [], skolemType(tv) -> s"new common.BaseTypeRep(\"b${toString(tv.extractTyVarRep)}\")"
    | [], _ -> t.transTypeRep
    | _, _ -> resolvedDcl.transContext
    end;
  top.transContext =
      if null(t.freeVariables) then top.transTypeableContext
      -- Workaround to inject variable bindings
      else s"""(new common.Typed() {
				public final common.TypeRep getType() {
${makeTyVarDecls(5, t.freeVariables)}
					return ${top.transTypeableContext};
				}
			}).getType()""";
  
  top.transContextMemberName = makeTypeableName(t, top.boundVariables);
  top.transContextSuperAccessorName = "getType";
  top.transContextSuperAccessor = s"""
	public final common.TypeRep getType() {
		return ${top.transTypeableContext};
	}
""";
}

aspect production inhSubsetContext
top::Context ::= i1::Type i2::Type
{
  -- This doesn't actually encode any runtime information, for now...
  top.transType = "Object";
  top.transContext = "null";
  top.transContextMemberName = makeInhSubsetName(i1, i2, top.boundVariables);
  top.transContextSuperAccessorName = "getInhSubset";
  top.transContextSuperAccessor = s"""
	public final Object getInhSubset() {
		return ${top.transContext};
	}
""";
}

aspect production typeErrorContext
top::Context ::= msg::String
{
  -- This should never get translated
  top.transType = error("Translation demanded for typeError context!");
  top.transContext = error("Translation demanded for typeError context!");
  top.transContextMemberName = error("Translation demanded for typeError context!");
  top.transContextSuperAccessorName = error("Translation demanded for typeError context!");
  top.transContextSuperAccessor = error("Translation demanded for typeError context!");
}

-- The translations of the narrowed forms of the instDcl's contexts are fed back as dcl.transContextDeps 
inherited attribute transContextDeps::[String] occurs on DclInfo;
attribute transContext occurs on DclInfo;

aspect default production
top::DclInfo ::=
{
  -- See TODO in the env DclInfo
  top.transContext = error("Internal compiler error: must be defined for all instance declarations");
}
aspect production instDcl
top::DclInfo ::= fn::String bound::[TyVar] contexts::[Context] ty::Type
{
  top.transContext = s"new ${makeInstanceName(top.sourceGrammar, fn, ty)}(${implode(", ", top.transContextDeps)})";
}
aspect production instConstraintDcl
top::DclInfo ::= fntc::String ty::Type tvs::[TyVar]
{
  top.transContext = makeConstraintDictName(fntc, ty, tvs);
}
aspect production sigConstraintDcl
top::DclInfo ::= fntc::String ty::Type ns::NamedSignature
{
  top.transContext = s"((${makeProdName(ns.fullName)})(context.undecorate())).${makeConstraintDictName(fntc, ty, ns.freeVariables)}";
}
aspect production currentInstDcl
top::DclInfo ::= fntc::String ty::Type
{
  top.transContext = s"currentInstance()";
}
aspect production instSuperDcl
top::DclInfo ::= fntc::String baseDcl::DclInfo
{
  baseDcl.transContextDeps = top.transContextDeps;
  top.transContext = baseDcl.transContext ++ s".${makeInstanceSuperAccessorName(fntc)}()";
}
aspect production occursDcl
top::DclInfo ::= fnnt::String fnat::String ntty::Type atty::Type
{
  top.transContext = top.attrOccursIndex;
}
aspect production occursInstConstraintDcl
top::DclInfo ::= fnat::String ntty::Type atty::Type tvs::[TyVar]
{
  top.transContext = makeConstraintDictName(fnat, ntty, tvs);
}
aspect production occursSigConstraintDcl
top::DclInfo ::= fnat::String ntty::Type atty::Type ns::NamedSignature
{
  top.transContext = s"((${makeProdName(ns.fullName)})(context.undecorate())).${makeConstraintDictName(fnat, ntty, ns.freeVariables)}";
}
aspect production occursSuperDcl
top::DclInfo ::= fnat::String atty::Type baseDcl::DclInfo
{
  baseDcl.transContextDeps = top.transContextDeps;
  top.transContext = baseDcl.transContext ++ s".${makeInstanceSuperAccessorName(fnat)}()";
}
aspect production annoInstanceDcl
top::DclInfo ::= fnnt::String fnat::String ntty::Type atty::Type
{
  top.transContext = "null";
}
aspect production annoInstConstraintDcl
top::DclInfo ::= fnat::String ntty::Type atty::Type tvs::[TyVar]
{
  top.transContext = "null";
}
aspect production annoSigConstraintDcl
top::DclInfo ::= fnat::String ntty::Type atty::Type ns::NamedSignature
{
  top.transContext = "null";
}
aspect production annoSuperDcl
top::DclInfo ::= fnat::String atty::Type baseDcl::DclInfo
{
  top.transContext = "null";
}
aspect production typeableInstConstraintDcl
top::DclInfo ::= ty::Type tvs::[TyVar]
{
  top.transContext = makeTypeableName(ty, tvs);
}
aspect production typeableSigConstraintDcl
top::DclInfo ::= ty::Type ns::NamedSignature
{
  top.transContext = s"((${makeProdName(ns.fullName)})(context.undecorate())).${makeTypeableName(ty, ns.freeVariables)}"; 
}
aspect production typeableSuperDcl
top::DclInfo ::= baseDcl::DclInfo
{
  baseDcl.transContextDeps = top.transContextDeps;
  top.transContext = baseDcl.transContext ++ ".getType()";
}
aspect production inhSubsetInstConstraintDcl
top::DclInfo ::= i1::Type i2::Type tvs::[TyVar]
{
  top.transContext = "null";
}
aspect production inhSubsetSigConstraintDcl
top::DclInfo ::= i1::Type i2::Type fnsig::NamedSignature
{
  top.transContext = "null";
}

function makeConstraintDictName
String ::= s::String t::Type tvs::[TyVar]
{
  t.boundVariables = tvs;
  return "d_" ++ substitute(":", "_", s) ++ "_" ++ t.transTypeName;
}

function makeTypeableName
String ::= t::Type tvs::[TyVar]
{
  t.boundVariables = tvs;
  return "typeRep_" ++ t.transTypeName;
}

function makeInhSubsetName
String ::= i1::Type i2::Type tvs::[TyVar]
{
  i1.boundVariables = tvs;
  i2.boundVariables = tvs;
  return s"inhSubset_${i1.transTypeName}_${i2.transTypeName}";
}

function makeInstanceSuperAccessorName
String ::= s::String
{
  return "getSuper_" ++ substitute(":", "_", s);
}
