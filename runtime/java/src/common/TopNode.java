package common;

import common.exceptions.SilverInternalError;

/**
 * TopNode is a DecoratedNode that is empty. It is used largely to give better error
 * messages than "null pointer exception" if there is a compiler bug.
 * 
 * <p>It's used as the parent of the very first thing, as the context for evaluating
 * global values, and is the parent of all function nodes.
 * 
 * @author tedinski, bodin
 * @see DecoratedNode
 */
public class TopNode extends DecoratedNode{ // TODO: this should become a Node!

	public static final TopNode singleton = new TopNode();
	
	private TopNode() {
		super(0,0,0,0,null,null,null,null,false,null);
		this.originCtx = OriginContext.GLOBAL_CONTEXT;
	}

	@Override
	public final DecoratedNode decorate(final DecoratedNode parent, final Lazy[] inhs, final Lazy decSite) {
		throw new SilverInternalError("TopNode cannot be decorated.");
	}

	@Override
	public final DecoratedNode decorate(final DecoratedNode parent, final Lazy[] inhs, final DecoratedNode fwdParent, final boolean prodFwrd) {
		throw new SilverInternalError("TopNode cannot be decorated.");
	}

	@Override
	public <T> T inherited(final int attribute) {
		throw new SilverInternalError("No inherited attributes given to TopNode.");
	}

	@Override
	public <T> T synthesized(final int attribute) {
		throw new SilverInternalError("No synthesized attributes defined on TopNode.");
	}
	
	@Override
	public <T> T childAsIs(final int s) {
		throw new SilverInternalError("No Children defined on TopNode.");
	}

	@Override
	public DecoratedNode childDecorated(final int s) {
		throw new SilverInternalError("No Children defined on TopNode.");
	}

	@Override
	public <T> T localAsIs(final int attribute) {
		throw new SilverInternalError("No local attributes defined on TopNode.");
	}

	@Override
	public DecoratedNode localDecorated(final int attribute) {
		throw new SilverInternalError("No local attributes defined on TopNode.");
	}

	@Override
	public DecoratedNode forward() {
		throw new SilverInternalError("TopNode does not forward.");
	}
	
}
