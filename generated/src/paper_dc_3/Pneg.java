
package paper_dc_3;

// p::Expr_a ::= ne::Expr_a 
public final class Pneg extends paper_dc_3.NExpr_a {

	public static final int i_ne = 0;


	public static final Class<?> childTypes[] = {paper_dc_3.NExpr_a.class};

	public static final int num_local_attrs = Init.count_local__ON__paper_dc_3_neg;
	public static final String[] occurs_local = new String[num_local_attrs];

	public static final common.Lazy[] forwardInheritedAttributes = new common.Lazy[paper_dc_3.NExpr_a.num_inh_attrs];

	public static final common.Lazy[] synthesizedAttributes = new common.Lazy[paper_dc_3.NExpr_a.num_syn_attrs];
	public static final common.Lazy[][] childInheritedAttributes = new common.Lazy[1][];

	public static final common.Lazy[] localAttributes = new common.Lazy[num_local_attrs];
	public static final common.Lazy[][] localInheritedAttributes = new common.Lazy[num_local_attrs][];

	static {
	childInheritedAttributes[i_ne] = new common.Lazy[paper_dc_3.NExpr_a.num_inh_attrs];

	}

	public Pneg(final Object c_ne, final Object a_silver_extension_bidirtransform_labels, final Object a_silver_extension_bidirtransform_origin, final Object a_silver_extension_bidirtransform_redex) {
		super(a_silver_extension_bidirtransform_labels, a_silver_extension_bidirtransform_origin, a_silver_extension_bidirtransform_redex);
		this.child_ne = c_ne;

	}

	private Object child_ne;
	public final paper_dc_3.NExpr_a getChild_ne() {
		return (paper_dc_3.NExpr_a) (child_ne = common.Util.demand(child_ne));
	}



	@Override
	public Object getChild(final int index) {
		switch(index) {
			case i_ne: return getChild_ne();

			default: return null;
		}
	}

	@Override
	public Object getChildLazy(final int index) {
		switch(index) {
			case i_ne: return child_ne;

			default: return null;
		}
	}

	@Override
	public final int getNumberOfChildren() {
		return 1;
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
		throw new common.exceptions.SilverInternalError("Production paper_dc_3:neg erroneously claimed to forward");
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
		return "paper_dc_3:neg";
	}

	static void initProductionAttributeDefinitions() {
		// p.value = - ne.value
		paper_dc_3.Pneg.synthesizedAttributes[paper_dc_3.Init.paper_dc_3_value__ON__paper_dc_3_Expr_a] = new common.Lazy() { public final Object eval(final common.DecoratedNode context) { return Integer.valueOf(-((Integer)context.childDecorated(paper_dc_3.Pneg.i_ne).synthesized(paper_dc_3.Init.paper_dc_3_value__ON__paper_dc_3_Expr_a))); } };

	}

	public static final common.NodeFactory<Pneg> factory = new Factory();

	public static final class Factory extends common.NodeFactory<Pneg> {

		@Override
		public Pneg invoke(final Object[] children, final Object[] annotations) {
			return new Pneg(children[0], annotations[0], annotations[1], annotations[2]);
		}
	};

}
