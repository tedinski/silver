
package silver.modification.impide;

// top::IdeStmts ::= '{' stmtList::IdeStmtList '}' 
public final class PlistIdeStmts extends silver.modification.impide.NIdeStmts {

	public static final int i__G_2 = 0;
	public static final int i_stmtList = 1;
	public static final int i__G_0 = 2;


	public static final Class<?> childTypes[] = {silver.definition.core.TLCurly_t.class,silver.modification.impide.NIdeStmtList.class,silver.definition.core.TRCurly_t.class};

	public static final int num_local_attrs = Init.count_local__ON__silver_modification_impide_listIdeStmts;
	public static final String[] occurs_local = new String[num_local_attrs];

	public static final common.Lazy[] forwardInheritedAttributes = new common.Lazy[silver.modification.impide.NIdeStmts.num_inh_attrs];

	public static final common.Lazy[] synthesizedAttributes = new common.Lazy[silver.modification.impide.NIdeStmts.num_syn_attrs];
	public static final common.Lazy[][] childInheritedAttributes = new common.Lazy[3][];

	public static final common.Lazy[] localAttributes = new common.Lazy[num_local_attrs];
	public static final common.Lazy[][] localInheritedAttributes = new common.Lazy[num_local_attrs][];

	static {
	childInheritedAttributes[i_stmtList] = new common.Lazy[silver.modification.impide.NIdeStmtList.num_inh_attrs];

	}

	public PlistIdeStmts(final Object c__G_2, final Object c_stmtList, final Object c__G_0, final Object a_core_location) {
		super(a_core_location);
		this.child__G_2 = c__G_2;
		this.child_stmtList = c_stmtList;
		this.child__G_0 = c__G_0;

	}

	private Object child__G_2;
	public final silver.definition.core.TLCurly_t getChild__G_2() {
		return (silver.definition.core.TLCurly_t) (child__G_2 = common.Util.demand(child__G_2));
	}

	private Object child_stmtList;
	public final silver.modification.impide.NIdeStmtList getChild_stmtList() {
		return (silver.modification.impide.NIdeStmtList) (child_stmtList = common.Util.demand(child_stmtList));
	}

	private Object child__G_0;
	public final silver.definition.core.TRCurly_t getChild__G_0() {
		return (silver.definition.core.TRCurly_t) (child__G_0 = common.Util.demand(child__G_0));
	}



	@Override
	public Object getChild(final int index) {
		switch(index) {
			case i__G_2: return getChild__G_2();
			case i_stmtList: return getChild_stmtList();
			case i__G_0: return getChild__G_0();

			default: return null;
		}
	}

	@Override
	public Object getChildLazy(final int index) {
		switch(index) {
			case i__G_2: return child__G_2;
			case i_stmtList: return child_stmtList;
			case i__G_0: return child__G_0;

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
		throw new common.exceptions.SilverInternalError("Production silver:modification:impide:listIdeStmts erroneously claimed to forward");
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
		return "silver:modification:impide:listIdeStmts";
	}

	static void initProductionAttributeDefinitions() {
		// top.errors := stmtList.errors
		if(silver.modification.impide.PlistIdeStmts.synthesizedAttributes[silver.modification.impide.Init.silver_definition_core_errors__ON__silver_modification_impide_IdeStmts] == null)
			silver.modification.impide.PlistIdeStmts.synthesizedAttributes[silver.modification.impide.Init.silver_definition_core_errors__ON__silver_modification_impide_IdeStmts] = new silver.definition.core.CAerrors(silver.modification.impide.Init.silver_definition_core_errors__ON__silver_modification_impide_IdeStmts);
		((common.CollectionAttribute)silver.modification.impide.PlistIdeStmts.synthesizedAttributes[silver.modification.impide.Init.silver_definition_core_errors__ON__silver_modification_impide_IdeStmts]).setBase(new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)context.childDecorated(silver.modification.impide.PlistIdeStmts.i_stmtList).synthesized(silver.modification.impide.Init.silver_definition_core_errors__ON__silver_modification_impide_IdeStmtList)); } });
		// top.ideFunctions = stmtList.ideFunctions
		silver.modification.impide.PlistIdeStmts.synthesizedAttributes[silver.modification.impide.Init.silver_modification_impide_ideFunctions__ON__silver_modification_impide_IdeStmts] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)context.childDecorated(silver.modification.impide.PlistIdeStmts.i_stmtList).synthesized(silver.modification.impide.Init.silver_modification_impide_ideFunctions__ON__silver_modification_impide_IdeStmtList)); } };
		// top.propDcls = stmtList.propDcls
		silver.modification.impide.PlistIdeStmts.synthesizedAttributes[silver.modification.impide.Init.silver_modification_impide_propDcls__ON__silver_modification_impide_IdeStmts] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)context.childDecorated(silver.modification.impide.PlistIdeStmts.i_stmtList).synthesized(silver.modification.impide.Init.silver_modification_impide_propDcls__ON__silver_modification_impide_IdeStmtList)); } };
		// top.wizards = stmtList.wizards
		silver.modification.impide.PlistIdeStmts.synthesizedAttributes[silver.modification.impide.Init.silver_modification_impide_wizards__ON__silver_modification_impide_IdeStmts] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)context.childDecorated(silver.modification.impide.PlistIdeStmts.i_stmtList).synthesized(silver.modification.impide.Init.silver_modification_impide_wizards__ON__silver_modification_impide_IdeStmtList)); } };
		// top.ideNames = stmtList.ideNames
		silver.modification.impide.PlistIdeStmts.synthesizedAttributes[silver.modification.impide.Init.silver_modification_impide_ideNames__ON__silver_modification_impide_IdeStmts] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)context.childDecorated(silver.modification.impide.PlistIdeStmts.i_stmtList).synthesized(silver.modification.impide.Init.silver_modification_impide_ideNames__ON__silver_modification_impide_IdeStmtList)); } };
		// top.ideVersions = stmtList.ideVersions
		silver.modification.impide.PlistIdeStmts.synthesizedAttributes[silver.modification.impide.Init.silver_modification_impide_ideVersions__ON__silver_modification_impide_IdeStmts] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)context.childDecorated(silver.modification.impide.PlistIdeStmts.i_stmtList).synthesized(silver.modification.impide.Init.silver_modification_impide_ideVersions__ON__silver_modification_impide_IdeStmtList)); } };
		// top.ideResources = stmtList.ideResources
		silver.modification.impide.PlistIdeStmts.synthesizedAttributes[silver.modification.impide.Init.silver_modification_impide_spec_ideResources__ON__silver_modification_impide_IdeStmts] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)context.childDecorated(silver.modification.impide.PlistIdeStmts.i_stmtList).synthesized(silver.modification.impide.Init.silver_modification_impide_spec_ideResources__ON__silver_modification_impide_IdeStmtList)); } };

	}

	public static final common.NodeFactory<PlistIdeStmts> factory = new Factory();

	public static final class Factory extends common.NodeFactory<PlistIdeStmts> {

		@Override
		public PlistIdeStmts invoke(final Object[] children, final Object[] annotations) {
			return new PlistIdeStmts(children[0], children[1], children[2], annotations[0]);
		}
	};

}
