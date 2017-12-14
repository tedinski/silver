
package silver.extension.doc.core;

// top::AGDcl ::= '{@config' items::DocConfigs '@}' 
public final class Pconfig extends silver.definition.core.NAGDcl {

	public static final int i__G_2 = 0;
	public static final int i_items = 1;
	public static final int i__G_0 = 2;


	public static final Class<?> childTypes[] = {silver.extension.doc.core.TConfigOpen_t.class,silver.extension.doc.core.NDocConfigs.class,silver.extension.doc.core.TClose_t.class};

	public static final int num_local_attrs = Init.count_local__ON__silver_extension_doc_core_config;
	public static final String[] occurs_local = new String[num_local_attrs];

	public static final common.Lazy[] forwardInheritedAttributes = new common.Lazy[silver.definition.core.NAGDcl.num_inh_attrs];

	public static final common.Lazy[] synthesizedAttributes = new common.Lazy[silver.definition.core.NAGDcl.num_syn_attrs];
	public static final common.Lazy[][] childInheritedAttributes = new common.Lazy[3][];

	public static final common.Lazy[] localAttributes = new common.Lazy[num_local_attrs];
	public static final common.Lazy[][] localInheritedAttributes = new common.Lazy[num_local_attrs][];

	static {
	childInheritedAttributes[i_items] = new common.Lazy[silver.extension.doc.core.NDocConfigs.num_inh_attrs];

	}

	public Pconfig(final Object c__G_2, final Object c_items, final Object c__G_0, final Object a_core_location) {
		super(a_core_location);
		this.child__G_2 = c__G_2;
		this.child_items = c_items;
		this.child__G_0 = c__G_0;

	}

	private Object child__G_2;
	public final silver.extension.doc.core.TConfigOpen_t getChild__G_2() {
		return (silver.extension.doc.core.TConfigOpen_t) (child__G_2 = common.Util.demand(child__G_2));
	}

	private Object child_items;
	public final silver.extension.doc.core.NDocConfigs getChild_items() {
		return (silver.extension.doc.core.NDocConfigs) (child_items = common.Util.demand(child_items));
	}

	private Object child__G_0;
	public final silver.extension.doc.core.TClose_t getChild__G_0() {
		return (silver.extension.doc.core.TClose_t) (child__G_0 = common.Util.demand(child__G_0));
	}



	@Override
	public Object getChild(final int index) {
		switch(index) {
			case i__G_2: return getChild__G_2();
			case i_items: return getChild_items();
			case i__G_0: return getChild__G_0();

			default: return null;
		}
	}

	@Override
	public Object getChildLazy(final int index) {
		switch(index) {
			case i__G_2: return child__G_2;
			case i_items: return child_items;
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
		return true;
	}

	@Override
	public common.Node evalForward(final common.DecoratedNode context) {
		return ((silver.definition.core.NAGDcl)new silver.definition.core.PemptyAGDcl(new common.Thunk<Object>(context) { public final Object doEval(final common.DecoratedNode context) { return ((core.NLocation)((silver.definition.core.NAGDcl)context.undecorate()).getAnno_core_location()); } }));
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
		return "silver:extension:doc:core:config";
	}

	static void initProductionAttributeDefinitions() {
		// top.docs := []
		if(silver.extension.doc.core.Pconfig.synthesizedAttributes[silver.extension.doc.core.Init.silver_extension_doc_core_docs__ON__silver_definition_core_AGDcl] == null)
			silver.extension.doc.core.Pconfig.synthesizedAttributes[silver.extension.doc.core.Init.silver_extension_doc_core_docs__ON__silver_definition_core_AGDcl] = new silver.extension.doc.core.CAdocs(silver.extension.doc.core.Init.silver_extension_doc_core_docs__ON__silver_definition_core_AGDcl);
		((common.CollectionAttribute)silver.extension.doc.core.Pconfig.synthesizedAttributes[silver.extension.doc.core.Init.silver_extension_doc_core_docs__ON__silver_definition_core_AGDcl]).setBase(new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.ConsCell)core.Pnil.invoke()); } });
		// top.docsHeader = items.header
		silver.extension.doc.core.Pconfig.synthesizedAttributes[silver.extension.doc.core.Init.silver_extension_doc_core_docsHeader__ON__silver_definition_core_AGDcl] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.StringCatter)context.childDecorated(silver.extension.doc.core.Pconfig.i_items).synthesized(silver.extension.doc.core.Init.silver_extension_doc_core_header__ON__silver_extension_doc_core_DocConfigs)); } };
		// top.docsSplit = items.splitFiles
		silver.extension.doc.core.Pconfig.synthesizedAttributes[silver.extension.doc.core.Init.silver_extension_doc_core_docsSplit__ON__silver_definition_core_AGDcl] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((common.StringCatter)context.childDecorated(silver.extension.doc.core.Pconfig.i_items).synthesized(silver.extension.doc.core.Init.silver_extension_doc_core_splitFiles__ON__silver_extension_doc_core_DocConfigs)); } };
		// top.docsNoDoc = items.noDoc
		silver.extension.doc.core.Pconfig.synthesizedAttributes[silver.extension.doc.core.Init.silver_extension_doc_core_docsNoDoc__ON__silver_definition_core_AGDcl] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return ((Boolean)context.childDecorated(silver.extension.doc.core.Pconfig.i_items).synthesized(silver.extension.doc.core.Init.silver_extension_doc_core_noDoc__ON__silver_extension_doc_core_DocConfigs)); } };

	}

	public static final common.NodeFactory<Pconfig> factory = new Factory();

	public static final class Factory extends common.NodeFactory<Pconfig> {

		@Override
		public Pconfig invoke(final Object[] children, final Object[] annotations) {
			return new Pconfig(children[0], children[1], children[2], annotations[0]);
		}
	};

}
