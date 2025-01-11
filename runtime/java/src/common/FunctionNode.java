package common;

import common.exceptions.SilverInternalError;

/**
 * FunctionNode is a Node, but with a few methods "removed".
 * 
 * We do things ever so slightly backwards. Instead of making production a subtype of function,
 * we make function a subtype of production.  Thus, here we wall off a few production-only things
 * that don't apply to functions (and throw exceptions if they are requested.)
 * 
 * The reason for this is simply so that DecoratedNode doesn't have to also deal with multiple
 * types of Node.
 * 
 * @author tedinski
 * @see Node
 */
public abstract class FunctionNode extends Node {
	public FunctionNode() {
		super(false);
	}

	@Override
	public final Node updateAnnos(Object[] annos) {
		// Functions should never even have this consulted. Ever.
		throw new SilverInternalError("Functions do not have annotations!");
	}

	// Used only when needing origins info on lazily evaluated locals in functions :/
	public DecoratedNode decorate(OriginContext originCtx) {
		DecoratedNode tmp = decorate();
		tmp.originCtx = originCtx;
		return tmp;
	}

	@Override
	public final Node evalUndecorate(final DecoratedNode context) {
		// Functions should never even have this consulted. Ever.
		throw new SilverInternalError("Functions do not undecorate!");
	}

	@Override
	public final boolean getLocalIsForward(final int index) {
		return false;
	}

	@Override
	public final boolean hasForward() {
		// Functions should never even have this consulted. Ever.
		throw new SilverInternalError("Functions do not forward!");
	}

	@Override
	public final Node evalForward(final DecoratedNode context) {
		throw new SilverInternalError("Functions do not forward!");
	}

	@Override
	public final Lazy[] getForwardInheritedAttributes() {
		throw new SilverInternalError("Functions do not forward!");
	}

	@Override
	public final Lazy getSynthesized(final int index) {
		throw new SilverInternalError("Functions do not possess synthesized attributes! (Requested index " + index + ")");
	}

	@Override
	public final Lazy getDefaultSynthesized(int index) {
		throw new SilverInternalError("Functions do not possess synthesized attributes! (Requested default for index " + index + ")");
	}
	
	@Override
	public final int getNumberOfInhAttrs() {
		return 0;
	}

	@Override
	public final int getNumberOfSynAttrs() {
		return 0;
	}

	@Override
	public final String getNameOfInhAttr(final int index) {
		throw new SilverInternalError("Functions do not possess inherited attributes! (Requested name of index " + index + ")");
	}

	@Override
	public final String getNameOfSynAttr(final int index) {
		throw new SilverInternalError("Functions do not possess synthesized attributes! (Requested name of index " + index + ")");
	}

	@Override
	public final String[] getAnnoNames() {
		throw new SilverInternalError("Functions do not possess annotations!");
	}
	
	@Override
	public final Object getAnno(final String name) {
		throw new SilverInternalError("Functions do not possess annotations! (Requested name " + name + ")");
	}
	
	@Override
	public final common.BaseTypeRep getType() {
		throw new SilverInternalError("Function nodes do not have a type!");
	}

	public RTTIManager.Prodleton<? extends Node> getProdleton() {
		throw new SilverInternalError("Function nodes do not have prodletons!");
	}
}
