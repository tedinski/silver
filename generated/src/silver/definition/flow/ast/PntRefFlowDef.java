
package silver.definition.flow.ast;

// top::FlowDef ::= nt::String inhs::[String] 
public final class PntRefFlowDef extends silver.definition.flow.ast.NFlowDef {

	public static final int i_nt = 0;
	public static final int i_inhs = 1;


	public static final Class<?> childTypes[] = {common.StringCatter.class,common.DecoratedNode.class};

	public static final int num_local_attrs = Init.count_local__ON__silver_definition_flow_ast_ntRefFlowDef;
	public static final String[] occurs_local = new String[num_local_attrs];

	public static final common.Lazy[] forwardInheritedAttributes = new common.Lazy[silver.definition.flow.ast.NFlowDef.num_inh_attrs];

	public static final common.Lazy[] synthesizedAttributes = new common.Lazy[silver.definition.flow.ast.NFlowDef.num_syn_attrs];
	public static final common.Lazy[][] childInheritedAttributes = new common.Lazy[2][];

	public static final common.Lazy[] localAttributes = new common.Lazy[num_local_attrs];
	public static final common.Lazy[][] localInheritedAttributes = new common.Lazy[num_local_attrs][];

	static {

	}

	public PntRefFlowDef(final Object c_nt, final Object c_inhs) {
		super();
		this.child_nt = c_nt;
		this.child_inhs = c_inhs;

	}

	private Object child_nt;
	public final common.StringCatter getChild_nt() {
		return (common.StringCatter) (child_nt = common.Util.demand(child_nt));
	}

	private Object child_inhs;
	public final common.ConsCell getChild_inhs() {
		return (common.ConsCell) (child_inhs = common.Util.demand(child_inhs));
	}



	@Override
	public Object getChild(final int index) {
		switch(index) {
			case i_nt: return getChild_nt();
			case i_inhs: return getChild_inhs();

			default: return null;
		}
	}

	@Override
	public Object getChildLazy(final int index) {
		switch(index) {
			case i_nt: return child_nt;
			case i_inhs: return child_inhs;

			default: return null;
		}
	}

	@Override
	public final int getNumberOfChildren() {
		return 2;
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
		throw new common.exceptions.SilverInternalError("Production silver:definition:flow:ast:ntRefFlowDef erroneously claimed to forward");
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
		return "silver:definition:flow:ast:ntRefFlowDef";
	}

	static void initProductionAttributeDefinitions() {
		// top.refTreeContribs = [ pair(nt, top) ]
		silver.definition.flow.ast.PntRefFlowDef.synthesizedAttributes[silver.definition.flow.ast.Init.silver_definition_flow_ast_refTreeContribs__ON__silver_definition_flow_ast_FlowDef] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)core.Pcons.invoke(new common.Thunk<Object>(context) { public final Object doEval(final common.DecoratedNode context) { return ((core.NPair)new core.Ppair(context.childAsIsLazy(silver.definition.flow.ast.PntRefFlowDef.i_nt), context.undecorate())); } }, new common.Thunk<Object>(context) { public final Object doEval(final common.DecoratedNode context) { return ((common.ConsCell)core.Pnil.invoke()); } })); } };
		// top.prodGraphContribs = []
		silver.definition.flow.ast.PntRefFlowDef.synthesizedAttributes[silver.definition.flow.ast.Init.silver_definition_flow_ast_prodGraphContribs__ON__silver_definition_flow_ast_FlowDef] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)core.Pnil.invoke()); } };
		// top.flowEdges = error("Internal compiler error: this sort of def should not be in a context where edges are requested.")
		silver.definition.flow.ast.PntRefFlowDef.synthesizedAttributes[silver.definition.flow.ast.Init.silver_definition_flow_ast_flowEdges__ON__silver_definition_flow_ast_FlowDef] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)core.Perror.invoke((new common.StringCatter("Internal compiler error: this sort of def should not be in a context where edges are requested.")))); } };
		// top.unparses = [ "ntRefFlowDef(" ++ quoteString(nt) ++ ", " ++ unparseStrings(inhs) ++ ")" ]
		silver.definition.flow.ast.PntRefFlowDef.synthesizedAttributes[silver.definition.flow.ast.Init.silver_definition_flow_ast_unparses__ON__silver_definition_flow_ast_FlowDef] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)core.Pcons.invoke(new common.Thunk<Object>(context) { public final Object doEval(final common.DecoratedNode context) { return new common.StringCatter((common.StringCatter)(new common.StringCatter("ntRefFlowDef(")), (common.StringCatter)new common.StringCatter((common.StringCatter)((common.StringCatter)silver.definition.env.PquoteString.invoke(context.childAsIsLazy(silver.definition.flow.ast.PntRefFlowDef.i_nt))), (common.StringCatter)new common.StringCatter((common.StringCatter)(new common.StringCatter(", ")), (common.StringCatter)new common.StringCatter((common.StringCatter)((common.StringCatter)silver.definition.env.PunparseStrings.invoke(context.childAsIsLazy(silver.definition.flow.ast.PntRefFlowDef.i_inhs))), (common.StringCatter)(new common.StringCatter(")")))))); } }, new common.Thunk<Object>(context) { public final Object doEval(final common.DecoratedNode context) { return ((common.ConsCell)core.Pnil.invoke()); } })); } };

	}

	public static final common.NodeFactory<PntRefFlowDef> factory = new Factory();

	public static final class Factory extends common.NodeFactory<PntRefFlowDef> {

		@Override
		public PntRefFlowDef invoke(final Object[] children, final Object[] annotations) {
			return new PntRefFlowDef(children[0], children[1]);
		}
	};

}
