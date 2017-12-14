
package silver.definition.core;

// top::AppExprs ::= es::AppExprs ',' e::AppExpr 
public final class PsnocAppExprs extends silver.definition.core.NAppExprs {

	public static final int i_es = 0;
	public static final int i__G_1 = 1;
	public static final int i_e = 2;


	public static final Class<?> childTypes[] = {silver.definition.core.NAppExprs.class,silver.definition.core.TComma_t.class,silver.definition.core.NAppExpr.class};

	public static final int num_local_attrs = Init.count_local__ON__silver_definition_core_snocAppExprs;
	public static final String[] occurs_local = new String[num_local_attrs];

	public static final common.Lazy[] forwardInheritedAttributes = new common.Lazy[silver.definition.core.NAppExprs.num_inh_attrs];

	public static final common.Lazy[] synthesizedAttributes = new common.Lazy[silver.definition.core.NAppExprs.num_syn_attrs];
	public static final common.Lazy[][] childInheritedAttributes = new common.Lazy[3][];

	public static final common.Lazy[] localAttributes = new common.Lazy[num_local_attrs];
	public static final common.Lazy[][] localInheritedAttributes = new common.Lazy[num_local_attrs][];

	static {
	childInheritedAttributes[i_es] = new common.Lazy[silver.definition.core.NAppExprs.num_inh_attrs];
	childInheritedAttributes[i_e] = new common.Lazy[silver.definition.core.NAppExpr.num_inh_attrs];

	}

	public PsnocAppExprs(final Object c_es, final Object c__G_1, final Object c_e, final Object a_core_location) {
		super(a_core_location);
		this.child_es = c_es;
		this.child__G_1 = c__G_1;
		this.child_e = c_e;

	}

	private Object child_es;
	public final silver.definition.core.NAppExprs getChild_es() {
		return (silver.definition.core.NAppExprs) (child_es = common.Util.demand(child_es));
	}

	private Object child__G_1;
	public final silver.definition.core.TComma_t getChild__G_1() {
		return (silver.definition.core.TComma_t) (child__G_1 = common.Util.demand(child__G_1));
	}

	private Object child_e;
	public final silver.definition.core.NAppExpr getChild_e() {
		return (silver.definition.core.NAppExpr) (child_e = common.Util.demand(child_e));
	}



	@Override
	public Object getChild(final int index) {
		switch(index) {
			case i_es: return getChild_es();
			case i__G_1: return getChild__G_1();
			case i_e: return getChild_e();

			default: return null;
		}
	}

	@Override
	public Object getChildLazy(final int index) {
		switch(index) {
			case i_es: return child_es;
			case i__G_1: return child__G_1;
			case i_e: return child_e;

			default: return null;
		}
	}

	@Override
	public final int getNumberOfChildren() {
		return 3;
	}

	@Override
	public common.Lazy getSynthesized(final int index) {
		return synthesizedAttributes[index];
	}

	@Override
	public common.Lazy[] getLocalInheritedAttributes(final int key) {
		return localInheritedAttributes[key];
	}

	@Override
	public common.Lazy[] getChildInheritedAttributes(final int key) {
		return childInheritedAttributes[key];
	}

	@Override
	public boolean hasForward() {
		return false;
	}

	@Override
	public common.Node evalForward(final common.DecoratedNode context) {
		throw new common.exceptions.SilverInternalError("Production silver:definition:core:snocAppExprs erroneously claimed to forward");
	}

	@Override
	public common.Lazy getForwardInheritedAttributes(final int index) {
		return forwardInheritedAttributes[index];
	}

	@Override
	public common.Lazy getLocal(final int key) {
		return localAttributes[key];
	}

	@Override
	public final int getNumberOfLocalAttrs() {
		return num_local_attrs;
	}

	@Override
	public final String getNameOfLocalAttr(final int index) {
		return occurs_local[index];
	}

	@Override
	public String getName() {
		return "silver:definition:core:snocAppExprs";
	}

	static void initProductionAttributeDefinitions() {
		// top.pp = es.pp ++ ", " ++ e.pp
		silver.definition.core.PsnocAppExprs.synthesizedAttributes[silver.definition.core.Init.silver_definition_env_pp__ON__silver_definition_core_AppExprs] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return new common.StringCatter((common.StringCatter)((common.StringCatter)context.childDecorated(silver.definition.core.PsnocAppExprs.i_es).synthesized(silver.definition.core.Init.silver_definition_env_pp__ON__silver_definition_core_AppExprs)), (common.StringCatter)new common.StringCatter((common.StringCatter)(new common.StringCatter(", ")), (common.StringCatter)((common.StringCatter)context.childDecorated(silver.definition.core.PsnocAppExprs.i_e).synthesized(silver.definition.core.Init.silver_definition_env_pp__ON__silver_definition_core_AppExpr)))); } };
		// top.isPartial = es.isPartial || e.isPartial
		silver.definition.core.PsnocAppExprs.synthesizedAttributes[silver.definition.core.Init.silver_definition_core_isPartial__ON__silver_definition_core_AppExprs] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return (((Boolean)context.childDecorated(silver.definition.core.PsnocAppExprs.i_es).synthesized(silver.definition.core.Init.silver_definition_core_isPartial__ON__silver_definition_core_AppExprs)) || ((Boolean)context.childDecorated(silver.definition.core.PsnocAppExprs.i_e).synthesized(silver.definition.core.Init.silver_definition_core_isPartial__ON__silver_definition_core_AppExpr))); } };
		// top.missingTypereps = es.missingTypereps ++ e.missingTypereps
		silver.definition.core.PsnocAppExprs.synthesizedAttributes[silver.definition.core.Init.silver_definition_core_missingTypereps__ON__silver_definition_core_AppExprs] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)core.Pappend.invoke(context.childDecoratedSynthesizedLazy(silver.definition.core.PsnocAppExprs.i_es, silver.definition.core.Init.silver_definition_core_missingTypereps__ON__silver_definition_core_AppExprs), context.childDecoratedSynthesizedLazy(silver.definition.core.PsnocAppExprs.i_e, silver.definition.core.Init.silver_definition_core_missingTypereps__ON__silver_definition_core_AppExpr))); } };
		// top.rawExprs = es.rawExprs ++ e.rawExprs
		silver.definition.core.PsnocAppExprs.synthesizedAttributes[silver.definition.core.Init.silver_definition_core_rawExprs__ON__silver_definition_core_AppExprs] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)core.Pappend.invoke(context.childDecoratedSynthesizedLazy(silver.definition.core.PsnocAppExprs.i_es, silver.definition.core.Init.silver_definition_core_rawExprs__ON__silver_definition_core_AppExprs), context.childDecoratedSynthesizedLazy(silver.definition.core.PsnocAppExprs.i_e, silver.definition.core.Init.silver_definition_core_rawExprs__ON__silver_definition_core_AppExpr))); } };
		// top.exprs = es.exprs ++ e.exprs
		silver.definition.core.PsnocAppExprs.synthesizedAttributes[silver.definition.core.Init.silver_definition_core_exprs__ON__silver_definition_core_AppExprs] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)core.Pappend.invoke(context.childDecoratedSynthesizedLazy(silver.definition.core.PsnocAppExprs.i_es, silver.definition.core.Init.silver_definition_core_exprs__ON__silver_definition_core_AppExprs), context.childDecoratedSynthesizedLazy(silver.definition.core.PsnocAppExprs.i_e, silver.definition.core.Init.silver_definition_core_exprs__ON__silver_definition_core_AppExpr))); } };
		// top.appExprIndicies = es.appExprIndicies ++ e.appExprIndicies
		silver.definition.core.PsnocAppExprs.synthesizedAttributes[silver.definition.core.Init.silver_definition_core_appExprIndicies__ON__silver_definition_core_AppExprs] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)core.Pappend.invoke(context.childDecoratedSynthesizedLazy(silver.definition.core.PsnocAppExprs.i_es, silver.definition.core.Init.silver_definition_core_appExprIndicies__ON__silver_definition_core_AppExprs), context.childDecoratedSynthesizedLazy(silver.definition.core.PsnocAppExprs.i_e, silver.definition.core.Init.silver_definition_core_appExprIndicies__ON__silver_definition_core_AppExpr))); } };
		// top.errors := es.errors ++ e.errors
		if(silver.definition.core.PsnocAppExprs.synthesizedAttributes[silver.definition.core.Init.silver_definition_core_errors__ON__silver_definition_core_AppExprs] == null)
			silver.definition.core.PsnocAppExprs.synthesizedAttributes[silver.definition.core.Init.silver_definition_core_errors__ON__silver_definition_core_AppExprs] = new silver.definition.core.CAerrors(silver.definition.core.Init.silver_definition_core_errors__ON__silver_definition_core_AppExprs);
		((common.CollectionAttribute)silver.definition.core.PsnocAppExprs.synthesizedAttributes[silver.definition.core.Init.silver_definition_core_errors__ON__silver_definition_core_AppExprs]).setBase(new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)core.Pappend.invoke(context.childDecoratedSynthesizedLazy(silver.definition.core.PsnocAppExprs.i_es, silver.definition.core.Init.silver_definition_core_errors__ON__silver_definition_core_AppExprs), context.childDecoratedSynthesizedLazy(silver.definition.core.PsnocAppExprs.i_e, silver.definition.core.Init.silver_definition_core_errors__ON__silver_definition_core_AppExpr))); } });
		// top.appExprSize = es.appExprSize + 1
		silver.definition.core.PsnocAppExprs.synthesizedAttributes[silver.definition.core.Init.silver_definition_core_appExprSize__ON__silver_definition_core_AppExprs] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return Integer.valueOf(((Integer)context.childDecorated(silver.definition.core.PsnocAppExprs.i_es).synthesized(silver.definition.core.Init.silver_definition_core_appExprSize__ON__silver_definition_core_AppExprs)) + Integer.valueOf((int)1)); } };
		// e.appExprIndex = es.appExprSize
		silver.definition.core.PsnocAppExprs.childInheritedAttributes[silver.definition.core.PsnocAppExprs.i_e][silver.definition.core.Init.silver_definition_core_appExprIndex__ON__silver_definition_core_AppExpr] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((Integer)context.childDecorated(silver.definition.core.PsnocAppExprs.i_es).synthesized(silver.definition.core.Init.silver_definition_core_appExprSize__ON__silver_definition_core_AppExprs)); } };
		// e.appExprTyperep = if null(top.appExprTypereps) then errorType() else head(top.appExprTypereps)
		silver.definition.core.PsnocAppExprs.childInheritedAttributes[silver.definition.core.PsnocAppExprs.i_e][silver.definition.core.Init.silver_definition_core_appExprTyperep__ON__silver_definition_core_AppExpr] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return (((Boolean)core.Pnull.invoke(context.contextInheritedLazy(silver.definition.core.Init.silver_definition_core_appExprTypereps__ON__silver_definition_core_AppExprs))) ? ((silver.definition.type.NType)silver.definition.type.PerrorType.invoke()) : ((silver.definition.type.NType)core.Phead.invoke(context.contextInheritedLazy(silver.definition.core.Init.silver_definition_core_appExprTypereps__ON__silver_definition_core_AppExprs)))); } };
		// es.appExprTypereps = if null(top.appExprTypereps) then [] else tail(top.appExprTypereps)
		silver.definition.core.PsnocAppExprs.childInheritedAttributes[silver.definition.core.PsnocAppExprs.i_es][silver.definition.core.Init.silver_definition_core_appExprTypereps__ON__silver_definition_core_AppExprs] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return (((Boolean)core.Pnull.invoke(context.contextInheritedLazy(silver.definition.core.Init.silver_definition_core_appExprTypereps__ON__silver_definition_core_AppExprs))) ? ((common.ConsCell)core.Pnil.invoke()) : ((common.ConsCell)core.Ptail.invoke(context.contextInheritedLazy(silver.definition.core.Init.silver_definition_core_appExprTypereps__ON__silver_definition_core_AppExprs)))); } };

	}

	public static final common.NodeFactory<PsnocAppExprs> factory = new Factory();

	public static final class Factory extends common.NodeFactory<PsnocAppExprs> {

		@Override
		public PsnocAppExprs invoke(final Object[] children, final Object[] annotations) {
			return new PsnocAppExprs(children[0], children[1], children[2], annotations[0]);
		}
	};

}
