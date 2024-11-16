package common;

import java.util.Arrays;

import common.exceptions.MissingDefinitionException;
import common.exceptions.SilverException;
import common.exceptions.SilverInternalError;
import common.exceptions.TraceException;
import silver.core.NLocation;
import silver.core.NMaybe;

/**
 * This is the <strike>Stack</strike>Heap Frame and primary data structure of Silver.
 * 
 * <p>Here be dragons, unfortunately. Don't modify at all without running it past me.
 * 
 * @author tedinski, krame505
 * @see Node
 */
public class DecoratedNode implements Decorable, Typed {
	// TODO list:
	// - Delete parent / forwardParent. Or coalesce them (only NEED for debugging purposes, if inh become thunks!)
	// - Delete forwardValue (make it a local/production attribute)
	// - merge inheritedAttributes into inheritedValues
	
	// Please note: the methods in this file have been refined to be quite small
	// because the JVM makes inlining decisions on a per-method basis (of course!)
	// So we try to keep the "slow paths" in a separate method, so the hot paths
	// can be inlined. (Things are designed around 35 bytes of bytecode as the limit.)

	// Error reporting note: we don't attempt to identify and report errors for
	// mis-generated code.  e.g. asking for synthesized attributes that
	// don't exist (syn#15 when there's only 10)
	// We only try to nicely report errors that are the fault of the user writing
	// broken code. (e.g. "no equation for syn")

	public OriginContext originCtx; //OriginContext of the "invocation" this is
	
	/**
	 * The "undecorated" form of this DecoratedNode. (Never null)
	 * 
	 * @see #undecorate()
	 */
	protected final Node self;
	/**
	 * The node that forwards to this one. (May be null)
	 * Not final, because we may set this when forwarding to a decorated tree via sharing.
	 */
	protected DecoratedNode forwardParent;
	/**
	 * The DecoratedNode creating this one. (Never null except for TopNode)
	 * This is only used for debugging and origins.
	 * 
	 * <p> May be actual parent. Or production this is a local in. Or just a production that
	 * called 'decorate' to create this one.
	 * 
	 * @see TopNode
	 */
	protected final DecoratedNode parent;
	/**
	 * Is this the forward for the production of forwardParent?
	 * This is true for normal forwarding, where there will be syn copy equations,
	 * but false for forward production attributes, which only forward inhs.
	 * Thus this determines whether translation attributes on this node
	 * default to having the same decoration sites as forwardParent.
	 */
	protected boolean isProdForward;
	/**
	 * The cache of children (e.g. the DecoratedNodes)
	 * 
	 * @see #child(int)
	 */
	protected final Object[] childrenValues;
	/**
	 * The cache of the forward node.
	 * 
	 * @see #forward()
	 */
	protected DecoratedNode forwardValue;
	/**
	 * The cache of the inherited attribute supplied to this node.
	 * 
	 * @see #inherited(int)
	 * @see #inheritedAttributes
	 */
	protected final Object[] inheritedValues;
	/**
	 * The cache of the synthesized attributes on this node.
	 * 
	 * @see #synthesized(int)
	 * @see #local(String)
	 */
	protected final Object[] synthesizedValues;

	/**
	 * The inherited attributes supplied to this DecoratedNode, to be evaluated with context 'parent'.
	 * Not final, because we make a copy of the array if this DecoratedNode is extra-decorated.
	 * 
	 * @see #inherited(int)
	 * @see #inheritedValues
	 */
	protected Lazy[] inheritedAttributes;

	/**
	 * A place where this tree will be decorated with additional inherited attributes.
	 * Decoration can be forced by evaluating this with context 'parent'.
	 */
	protected Lazy decorationSite;

	/**
	 * A cache of the values of local attributes on this node. (incl. locals and prod)
	 */
	protected final Object[] localValues;

	/**
	 * Construct a decorated form of a Node. Called only via Node.
	 * 
	 * <p> 'self' and 'parent' are not null (except for TopNode)
	 * 
	 * @param cc  Child count
	 * @param ic  Inherited attribute count
	 * @param sc  Synthesized attribute count
	 * @param lc  Local/prod attribute count
	 * @param self  The Node to decorate.
	 * @param parent  The DecoratedNode creating this one, to evaluate inhs in.
	 * @param inhs  The inherited attributes to decorate this node with.
	 * @param forwardParent  The node to request inherited attributes from if not supplied in 'inhs'.
	 * @param isProdForward  Is this the forward for forwardParent's prod?  False for forward prod attributes.
	 * 
	 * @see Node#decorate(DecoratedNode, Lazy[])
	 * @see Node#decorate(DecoratedNode, Lazy[], DecoratedNode, boolean)
	 */
	DecoratedNode(
			final int cc, final int ic, final int sc, final int lc,
			final Node self, final DecoratedNode parent,
			final Lazy[] inhs,
			final DecoratedNode forwardParent, final boolean isProdForward,
			final Lazy decorationSite) {
		this.self = self;
		this.parent = parent;
		this.originCtx = parent!=null?parent.originCtx:null;
		this.forwardParent = forwardParent;
		this.isProdForward = isProdForward;
		this.decorationSite = decorationSite;

		if(inhs != null && inhs.length < ic) {
			// TODO: Due to the implementation of inherited occurs-on constraints, we might
			// get passed a shorter array when decorating a polymorphic type.
			// This seems like it should be avoidable?
			this.inheritedAttributes = Arrays.copyOf(inhs, ic);
		} else {
			this.inheritedAttributes = inhs;
		}
		
		// create caches
		this.childrenValues =    (cc > 0) ? new Object[cc] : null;
		this.inheritedValues =   (ic > 0) ? new Object[ic] : null;
		this.synthesizedValues = (sc > 0) ? new Object[sc] : null;
		this.localValues =       (lc > 0) ? new Object[lc] : null;
		
		// STATS: Uncomment to enable statistics
		//Statistics.dnSpawn(self!=null?self.getClass():TopNode.class);
		// System.err.println("TRACE: " + (parent == null? "null" : parent.getDebugID()) + " creating decorated " + getDebugID());
	}
	/**
	 * Initialize a DecorateNode created by a FunctionNode.
	 * 
	 * @param cc number of children
	 * @param lc number of locals
	 * @param self The FunctionNode
	 * @see {@link FunctionNode#decorate()}
	 */
	DecoratedNode(final int cc, final int lc, final FunctionNode self) {
		// TODO: I added this constructor largely because I wanted to
		// see if I could make all this fit under the 35 byte inline limit.
		// This doesn't. :(  Leaving it, because it certainly doesn't hurt.
		this.self = self;
		this.parent = TopNode.singleton;
		this.inheritedAttributes = null;
		this.forwardParent = null;
		this.isProdForward = false;
		
		this.childrenValues = new Object[cc];
		this.inheritedValues = null;
		this.synthesizedValues = null;
		this.localValues = (lc > 0) ? new Object[lc] : null;
	}
	
	// STATS: Uncomment to enable statistics
	//@Override
	//protected void finalize() throws Throwable {
	//	Statistics.dnFinal(self!=null?self.getClass():TopNode.class);
	//}

	/**
	 * @return Turn this DecoratedNode back into an undecorated {@link Node}.
	 */
	public final Node undecorate() {
		if (self.isUnique) {
			// System.err.println("TRACE: undecorating " + getDebugID());
			return self.undecorate(this);
		} else {
			return self;
		}
	}

	/**
	 * Decorate this (decorated) node with additional inherited attributes.
	 * This has no effect if the node already has a forward parent.
	 * 
	 * @param parent The DecoratedNode extra-decorating this one. (Whether this is a child or a local (or other) of that node.)
	 * @param inhs Overrides for inherited attributes that should not be computed via forwarding.
	 *   These Lazys will be supplied with 'parent' as their context for evaluation.
	 * @param decSite An accessor for where this DecoratedNode will be supplied with additional inherited attributes.
	 * @return A DecoratedNode with the additional attributes supplied, referencing this DecoratedNode as 'base'.
	 */
	@Override
	public DecoratedNode decorate(final DecoratedNode parent, final Lazy[] inhs, final Lazy decSite) {
		// System.err.println("TRACE: " + parent.getDebugID() + " extra-decorating " + getDebugID());
		if (forwardParent == null) {
			if (inhs != null) {
				if (inheritedAttributes == null) {
					inheritedAttributes = new Lazy[self.getNumberOfInhAttrs()];
				} else {
					inheritedAttributes = inheritedAttributes.clone();  // Avoid modifying the static inh array from the original parent Node
				}
				copyInhOverrides(parent, inheritedAttributes, inhs);
			}
			// It's okay if we override the old decorationSite here if it wasn't null,
			// that just means something else is directly demanding what would have been
			// forced by the current decorationSite, first.
			decorationSite = decSite != null? decSite.withContext(parent) : null;
		}
		return this;
	}

	private void copyInhOverrides(final DecoratedNode parent, final Lazy[] inhs, final Lazy[] newInhs) {
		// Arrays can differ in length if a tree is shared in a polymorphic decoration site.
		// The new inh array should never be larger than the original one.
		assert inhs.length >= newInhs.length;
		for(int i = 0; i < newInhs.length; i++) {
			if(newInhs[i] != null) {
				Lazy newInh = newInhs[i].withContext(parent);
				if(inhs[i] == null) {
					inhs[i] = newInh;
				} else if (inhs[i] instanceof TransInhs) {
					assert newInhs[i] instanceof TransInhs;
					copyInhOverrides(parent, ((TransInhs)inhs[i]).inhs, ((TransInhs)newInh).inhs);
				}
			}
		}
	}

	/**
	 * Decorate this node with a forward parent.
	 * This has no effect if the node already has a forward parent.
	 * 
	 * @param parent The "true parent" of this node (same as the fwdParent's parent) 
	 * @param inhs A map from attribute indexes to Lazys that define them.  These Lazys will be supplied with 'parent' as their context for evaluation.
	 * @param fwdParent The DecoratedNode that forwards to the one we are about to create. We will pass inherited attribute access requests to this node.
	 * @param prodFwrd  Is this the forward for fwdParent's prod?  False for forward prod attributes.
	 * @return A DecoratedNode with the attributes supplied.
	 */
	@Override
	public DecoratedNode decorate(final DecoratedNode parent, final Lazy[] inhs, final DecoratedNode fwdParent, final boolean prodFwrd) {
		if (forwardParent == null) {
			decorate(parent, inhs, null);
			forwardParent = fwdParent;
			isProdForward = prodFwrd;
		}
		return this;
	}

	/**
	 * Accessor function to access the originally-decorated Node.
	 * The Node returned by this function must never be decorated - 
	 * e.g. for use by origin tracking or for debugging purposes.
	 * One should typically use {@link undecorate} instead to avoid duplicating any shared children.
	 * 
	 * @return The {@link Node} this decorates.
	 */
	public final Node getNode() {
		return self;
	}

	/**
	 * Accessor function to access the tree that forwarded to this one.
	 * This is currently only used in undecorating productions with shared children.
	 * 
	 * @return The parent of this DecoratedNode.
	 */
	public final DecoratedNode getForwardParent() {
		if (forwardParent == null) {
			throw new SilverInternalError("Attempted to access forwardParent of " + getDebugID() + ", which is not a forward tree.");
		}
		return forwardParent;
	}

	/**
	 * Returns the child of this DecoratedNode, decorating it if needed.
	 * 
	 * This may be useful for debugging/reflection but is not used in the translation;
	 * prefer calling childAsIs/childDecorated directly for performance.
	 * 
	 * @param child The number of the child to obtain.
	 * @return The value of the child.
	 */
	public Object child(final int child) {
		if(self.isChildDecorable(child)) {
			return childDecorated(child);
		} else {
			return childAsIs(child);
		}
	}

	/**
	 * Returns the child of this DecoratedNode, without potentially decorating it.
	 * 
	 * <p>Warning: do not mix {@link #childAsIs} and {@link #childDecorated} on the same child!
	 * 
	 * @param child The number of the child to obtain.
	 * @return The unmodified value of the child.
	 */
	@SuppressWarnings("unchecked")
	public <T> T childAsIs(final int child) {
		return (T) self.getChild(child);
	}
	
	/**
	 * Returns the child of this DecoratedNode, decorating it with whatever inherited attributes
	 * this production has for it.
	 * 
	 * <p>Warning: do not mix {@link #childAsIs} and {@link #childDecorated} on the same child!
	 * 
	 * @param child The number of the child to obtain.
	 * @return The decorated value of the child.
	 */
	public DecoratedNode childDecorated(final int child) {
		Object o = this.childrenValues[child]; 
		if(o == null) {
			o = createDecoratedChild(child);
			
			assert(o != null);

			// CACHE : probably should not comment out child caching?
			this.childrenValues[child] = o;
		}
		return (DecoratedNode)o;
	}

	/**
	 * Create the DecoratedNode for a child.
	 * Invariant: should never be called more than once for a child!
	 * 
	 * @param child The number of the child to create.
	 * @return The decorated value of the child.
	 */
	private final DecoratedNode createDecoratedChild(final int child) {
		assert self.isChildDecorable(child);
		return ((Decorable)self.getChild(child)).decorate(
			this, self.getChildInheritedAttributes(child), self.getChildDecSite(child));
	}

	/**
	 * Returns the value of a local, decorating it if needed.
	 * 
	 * This may be useful for debugging/reflection but is not used in the translation;
	 * prefer calling localAsIs/localDecorated directly for performance.
	 * 
	 * @param attribute The index of the local to obtain.
	 * @return The value of the local.
	 */
	public Object local(final int attribute) {
		if(self.isLocalDecorable(attribute)) {
			return localDecorated(attribute);
		} else {
			return localAsIs(attribute);
		}
	}

	/**
	 * Get the value of a local, caching it for re-use.
	 * 
	 * <p>Warning: do not mix {@link #localAsIs} and {@link #localDecorated} on the same local attribute!
	 * 
	 * @param attribute The index of the local to obtain.
	 * @return The value of the local.
	 */
	@SuppressWarnings("unchecked")
	public <T> T localAsIs(final int attribute) {
		Object o = this.localValues[attribute];
		if(o == null) {
			o = evalLocalAsIs(attribute);
			
			assert(o != null);

			// CACHE : comment out to disable caching for local attributes
			// not recommended due to IO objects (IOString, etc)
			this.localValues[attribute] = o;
		}
		return (T) o;
	}
	
	/**
	 * Slow path to eval a local, kept separate for inlining reasons.
	 */
	private final Object evalLocalAsIs(final int attribute) {
		try {
			return self.getLocal(attribute).eval(this);
		} catch(Throwable t) {
			throw handleLocalError(attribute, t);
		}
	}
	
	/**
	 * Error generation code for local attribute evaluation.
	 * Kept separate so as not to impact inlining decisions.
	 */
	private final SilverException handleLocalError(final int attribute, final Throwable t) {
		// Rather than checking in the fast path, we try to reconstruct what went wrong in the slow path.
		if(self.getLocal(attribute) == null) {
			return new MissingDefinitionException("Local '" + self.getNameOfLocalAttr(attribute) + "' not defined in " + getDebugID());
		}
		return new TraceException("While evaling local '" + self.getNameOfLocalAttr(attribute) + "' in " + getDebugID(), t);
	}

	/**
	 * Get the value of a local, caching it for re-use.
	 * 
	 * <p>Warning: do not mix {@link #localAsIs} and {@link #localDecorated} on the same local attribute!
	 * 
	 * @param attribute The index of the local to obtain.
	 * @return The value of the local.
	 */
	public DecoratedNode localDecorated(final int attribute) {
		Object o = this.localValues[attribute];
		if(o == null) {
			o = evalLocalDecorated(attribute);
			
			assert(o != null);

			// CACHE : comment out to disable caching for local attributes
			// not recommended due to IO objects (IOString, etc)
			this.localValues[attribute] = o;
		}
		return (DecoratedNode)o;
	}

	/**
	 * Evaluate a local and decorate it.
	 * Invariant: should never be called more than once for a local!
	 * 
	 * @param attribute The index of the local to obtain.
	 * @return The decorated value of the local.
	 */
	private final DecoratedNode evalLocalDecorated(final int attribute) {
		assert self.isLocalDecorable(attribute);
		Decorable localAsIs = (Decorable)evalLocalAsIs(attribute);
		Lazy[] inhs = self.getLocalInheritedAttributes(attribute);
		if(self.getLocalIsForward(attribute)) {
			return localAsIs.decorate(this, inhs, this, false);
		} else {
			return localAsIs.decorate(this, inhs, self.getLocalDecSite(attribute));
		}
	}

	/**
	 * Obtain a synthesized attribute from this DecoratedNode. First, look for definitions on this node,
	 * and if that fails, request it from whatever we forward to, if anything.
	 * 
	 * @param attribute The index of the attribute.
	 * @return The value of the attribute.
	 */
	@SuppressWarnings("unchecked")
	public <T> T synthesized(final int attribute) {
		// common.Util.stackProbe();
		// System.err.println("TRACE: " + getDebugID() + " demanding syn attribute: " + self.getNameOfSynAttr(attribute));
		
		Object o = this.synthesizedValues[attribute];
		if(o == null) {
			o = evalSyn(attribute);
			
			assert(o != null);

			// CACHE : comment out to disable caching for synthesized attributes
			this.synthesizedValues[attribute] = o;
		}
		return (T) o;
	}
	
	private final Object evalSyn(final int attribute) {
		// TODO: Try to break this up into < 35 byte methods?
		Lazy l = self.getSynthesized(attribute);
		if(l != null) {
			try {
				if(l instanceof CollectionAttribute) {
					// This is necessary to ensure collection
					// attribute equations in aspect default
					// productions work; see
					// https://github.com/melt-umn/silver/issues/290
					CollectionAttribute prodAttr = (CollectionAttribute)l;
					if(!prodAttr.appliedNTFix) {
						prodAttr.appliedNTFix = true;
						CollectionAttribute ntAttr = (CollectionAttribute)self.getDefaultSynthesized(attribute);
						if(ntAttr != null)
							prodAttr.getPieces().addAll(ntAttr.getPieces());
					}
				}
				return l.eval(this);
			} catch(Throwable t) {
				throw new TraceException("While evaling syn '" + self.getNameOfSynAttr(attribute) + "' in " + getDebugID(), t);
			}
		} else if(self.hasForward()) {
			try {
				return forward().synthesized(attribute);
			} catch(Throwable t) {
				throw new TraceException("While evaling syn '" + self.getNameOfSynAttr(attribute) + "' via forward in " + getDebugID(), t);
			}
		} else {
			l = self.getDefaultSynthesized(attribute);
			if(l != null) {
				try {
					return l.eval(this);
				} catch(Throwable t) {
					throw new TraceException("While evaling default for syn '" + self.getNameOfSynAttr(attribute) + "' in " + getDebugID(), t);
				}
			} else {
				throw new MissingDefinitionException("Synthesized attribute '" + self.getNameOfSynAttr(attribute) + "' not defined in " + getDebugID());
			}
		}
	}

	/**
	 * Obtain a translation attribute from this DecoratedNode.
	 * Evaluate it as a synthesized attribute, then decorate it.
	 * 
	 * @param attribute The index of the attribute.
	 * @param inhsAttribute The index of the TransInhs supplying the attribute's inherited attributes
	 * @param decSiteAttribute The index of the attribute's decoration site attribute
	 * @return The value of the attribute.
	 */
	public DecoratedNode translation(final int attribute, final int inhsAttribute, final int decSiteAttribute) {
		// common.Util.stackProbe();
		// System.err.println("TRACE: " + getDebugID() + " demanding trans attribute: " + self.getNameOfSynAttr(attribute));
		
		DecoratedNode o = (DecoratedNode)this.synthesizedValues[attribute];
		if(o == null) {
			o = evalTrans(attribute, inhsAttribute, decSiteAttribute);
			
			assert(o != null);

			// CACHE : comment out to disable caching for translation attributes
			this.synthesizedValues[attribute] = o;
		}
		return o;
	}

	/**
	 * Evaluate a translation attribute and decorate it.
	 * Invariant: should never be called more than once for an attribute!
	 * 
	 * @param attribute The index of the translation attribute to obtain.
	 * @param inhsAttribute The index of the TransInhs supplying the attribute's inherited attributes
	 * @param decSiteAttribute The index of the attribute's decoration site attribute
	 * @return The decorated value of the translation attribute.
	 */
	private final DecoratedNode evalTrans(final int attribute, final int inhsAttribute, final int decSiteAttribute) {
		Lazy l = self.getSynthesized(attribute);
		Decorable d;
		if(l != null) {
			try {
				d = (Decorable)l.eval(this);
			} catch(Throwable t) {
				throw new TraceException("While evaling trans '" + self.getNameOfSynAttr(attribute) + "' in " + getDebugID(), t);
			}
		} else if(self.hasForward()) {
			try {
				d = forward().translation(attribute, inhsAttribute, decSiteAttribute);
			} catch(Throwable t) {
				throw new TraceException("While evaling trans '" + self.getNameOfSynAttr(attribute) + "' via forward in " + getDebugID(), t);
			}
		} else {
			l = self.getDefaultSynthesized(attribute);
			if(l != null) {
				try {
					d = (Decorable)l.eval(this);
				} catch(Throwable t) {
					throw new TraceException("While evaling default for trans '" + self.getNameOfSynAttr(attribute) + "' in " + getDebugID(), t);
				}
			} else {
				throw new MissingDefinitionException("Translation attribute '" + self.getNameOfSynAttr(attribute) + "' not defined in " + getDebugID());
			}
		}
		Lazy[] inhs = null;
		if (inheritedAttributes != null && inheritedAttributes[inhsAttribute] != null) {
			if (inheritedAttributes[inhsAttribute] instanceof TransInhs) {
				inhs = ((TransInhs)inheritedAttributes[inhsAttribute]).inhs;
			} else {
				throw new SilverInternalError("Supplied trans inhs attribute not TransInhs!");
			}
		}
		Lazy decSite = inheritedAttributes == null? null : inheritedAttributes[decSiteAttribute];
		if(decSite == null && forwardParent != null && isProdForward && forwardParent.synthesizedValues[attribute] == null) {
			decSite = (context) -> forwardParent.translation(attribute, inhsAttribute, decSiteAttribute);
		}
		return d.decorate(parent, inhs, decSite);
	}

	/**
	 * Get the forwarded-to DecoratedNode.  Cached.  There is no need for an "AsIs" vs "Decorated"
	 * variant of this function, since we always know it's a Node.
	 * 
	 * @return The DecoratedNode this one forwards to. (Crash if non-forwarding!)
	 */
	public DecoratedNode forward() {
		if(this.forwardValue == null) {
			// CACHE : should not comment out forward caching !
			this.forwardValue = evalForward();

			assert(this.forwardValue != null);
		}
		return this.forwardValue;
	}

	/**
	 * @return Either forward() or this.
	 */
	public DecoratedNode forwardOrThis() {
		return self.hasForward() ? forward() : this;
	}
	
	/**
	 * Also to keep the fast path small and inlineable.
	 */
	private final DecoratedNode evalForward() {
		try {
			return self.evalForward(this).decorate(
				parent, getForwardInheritedAttributes(), this, true);
		} catch(Throwable t) {
			throw handleFwdError(t);
		}
	}

	private final Lazy[] getForwardInheritedAttributes() {
		Lazy[] forwardInhs = self.getForwardInheritedAttributes();
		if(forwardInhs == null) return null;
		Lazy[] result = new Lazy[self.getNumberOfInhAttrs()];
		for(int i = 0; i < result.length; i++) {
			Lazy l = forwardInhs[i];
			if (l != null) {
				// The Lazys in self.getForwardInheritedAttributes expect this (forwarding) DecoratedNode as context,
				// but will be passed the parent of this node instead.
				result[i] = l.withContext(this);
			}
		}
		return result;
	}
	
	private final RuntimeException handleFwdError(Throwable t) {
		return new TraceException("While evaling forward equation in " + getDebugID(), t);
	}

	/**
	 * Get the value of an inherited attribute on this DN.  First, try the inherited attributes we were given.
	 * If that fails, ask our {@link #forwardParent}, if any, for whatever they may give us.
	 * 
	 * @param attribute The index of the attribute.
	 * @return The value of the attribute.
	 */
	@SuppressWarnings("unchecked")
	public <T> T inherited(final int attribute) {
		// common.Util.stackProbe();
		// System.err.println("TRACE: " + getDebugID() + " demanding inh attribute: " + self.getNameOfInhAttr(attribute));
		
		Object o = this.inheritedValues[attribute];
		if(o == null) {
			o = evalInhSomehow(attribute);
			
			assert(o != null);

			// CACHE : comment out to disable caching of inherited attributes
			// not recommended because it leads to a combinatoric explosion for environments
			// due to thunks keeping around references to previously computed environments that
			// we're recomputing
			this.inheritedValues[attribute] = o;
		}
		return (T) o;
	}
	
	private final Object evalInhSomehow(final int attribute) {
		// We specifically have to check here for inheritedAttributes == null, because
		// that's what happens when we don't supply any inherited attributes...
		// That is, unlike the unconditional access earlier for inheritedValues[attribute]
		// (which could be null if *no inherited attributes occur at all* on this
		// node), this could be the result of correctly compiled, but wrongly written user
		// code.
		if(inheritedAttributes != null && inheritedAttributes[attribute] != null)
			return evalInhHere(attribute);
		else
			return evalInhViaDecSiteOrFwrd(attribute);
	}
	private final Object evalInhViaDecSiteOrFwrd(final int attribute) {
		if(this.decorationSite != null) {
			return evalInhViaDecSite(attribute);
		} else {
			return evalInhViaFwdP(attribute);
		}
	}
	private final Object evalInhViaDecSite(final int attribute) {
		Lazy decSite = this.decorationSite;
		this.decorationSite = null;
		Object decSiteTree;
		try {
			decSiteTree = decSite.eval(parent);
		} catch (Throwable t) {
			throw new TraceException("While evaling inh '" + self.getNameOfInhAttr(attribute) + "' via decoration site of " + getDebugID() + " in " + parent.getDebugID(), t);
		}
		if(this != decSiteTree) {
			throw new SilverInternalError("Decoration site for " + getDebugID() + " returned a different tree: " + decSiteTree.toString());
		}
		return evalInhSomehow(attribute);
	}
	private final Object evalInhViaFwdP(final int attribute) {
		try {
			return forwardParent.inherited(attribute);
		} catch(Throwable t) {
			throw handleInhFwdPError(attribute, t); 
		}
	}
	private final SilverException handleInhFwdPError(final int attribute, Throwable t) {
		if(forwardParent == null) {
			return new MissingDefinitionException("Inherited attribute '" + self.getNameOfInhAttr(attribute) + "' not provided to " + getDebugID() + " by " + parent.getDebugID());
		}
		return new TraceException("While evaling inh '" + self.getNameOfInhAttr(attribute) + "' via forward in " + getDebugID(), t);
	}
	private final Object evalInhHere(final int attribute) {
		try {
			return inheritedAttributes[attribute].eval(parent);
		} catch(Throwable t) {
			throw handleInhHereError(attribute, t);
		}
	}
	private final SilverException handleInhHereError(final int attribute, Throwable t) {
		// This seems impossible since we're checking if it has an equation earlier up there!
		// if(inheritedAttributes == null || inheritedAttributes[attribute] == null) {
		// 	return new MissingDefinitionException("Inherited attribute '" + self.getNameOfInhAttr(attribute) + "' not provided to " + getDebugID() + " by " + parent.getDebugID());
		// }
		return new TraceException("While evaling inh '" + self.getNameOfInhAttr(attribute) + "' in " + getDebugID(), t);
	}

	// The following are very common types of thunks.
	// We put them here in the runtime to reduce generated jar sizes,
	// as many class files can start eating space like crazy.
	// Was something like 30% reduction, just from these...
	
	public final Object childDecoratedLazy(final int child) {
		if(childrenValues[child] != null)
			return childrenValues[child];
		
		return new Thunk<Object>(() -> this.childDecorated(child));
	}
	public final Object childUndecoratedLazy(final int child) {
		return new Thunk<Object>(() -> this.childDecorated(child).undecorate());
	}
	public final Object childAsIsLazy(final int child) {
		// childAsIs does not store in the childrenValues array, so...
		// Straight up use whatever thunk (or not!) is in the node.
		return self.getChildLazy(child);
	}
	public final Object localLazy(final int index) {
		if(localValues[index] != null)
			return localValues[index];
		
		return new Thunk<Object>(() -> this.local(index));
	
	}
	public final Object localDecoratedLazy(final int index) {
		if(localValues[index] != null)
			return localValues[index];
		
		return new Thunk<Object>(() -> this.localDecorated(index));
	}
	public final Object localAsIsLazy(final int index) {
		if(localValues[index] != null)
			return localValues[index];

		return new Thunk<Object>(() -> this.localAsIs(index));
	}
	public final Object childDecoratedSynthesizedLazy(final int child, final int index) {
		Object v = childrenValues[child];
		if(v != null) {
			return ((DecoratedNode)v).contextSynthesizedLazy(index);
		}

		return new Thunk<Object>(() -> this.childDecorated(child).synthesized(index));
	}
	public final Object childAsIsSynthesizedLazy(final int child, final int index) {
		// For as-is children, we do not store in childrenValues
		Object v = self.getChildLazy(child);
		if(!(v instanceof Thunk)) {
			return ((DecoratedNode)v).contextSynthesizedLazy(index);
		}

		return new Thunk<Object>(() -> ((DecoratedNode)this.childAsIs(child)).synthesized(index));
	}
	public final Object contextSynthesizedLazy(final int index) {
		if(synthesizedValues[index] != null) {
			return synthesizedValues[index];
		}
		
		return new Thunk<Object>(() -> this.synthesized(index));
	}
	public final Object contextInheritedLazy(final int index) {
		if(inheritedValues[index] != null)
			return inheritedValues[index];
		
		return new Thunk<Object>(() -> this.inherited(index));
	}
	
	@Override
	public final DecoratedTypeRep getType() {
		return new DecoratedTypeRep(self.getType());
	}
	
	/**
	 * Debug ID. e.g. "node 'some:prod' (f32ca8, ParseFile.c:328:8)"
	 * 
	 * @return an identification string for this node.
	 */
	public final String getDebugID() {
		if(self == null) {
			return "<top>";
		}
		NLocation loc = null;
		String notes = "";
		if(self instanceof silver.core.Alocation) {
			loc = ((silver.core.Alocation)self).getAnno_silver_core_location();
		} else if(self instanceof Tracked) {
			NMaybe maybeLoc = silver.core.PgetParsedOriginLocation.invoke(OriginContext.FFI_CONTEXT, self);
			if(maybeLoc instanceof silver.core.Pjust) {
				loc = (silver.core.NLocation)maybeLoc.getChild(0);
			}
			notes = silver.core.PgetOriginNotesString.invoke(OriginContext.FFI_CONTEXT, self).toString();
		}
		String qualifier = Integer.toHexString(System.identityHashCode(this));
		if(loc != null) {
			String file = loc.synthesized(silver.core.Init.silver_core_filename__ON__silver_core_Location).toString();
			int line = (Integer)loc.synthesized(silver.core.Init.silver_core_line__ON__silver_core_Location);
			int col = (Integer)loc.synthesized(silver.core.Init.silver_core_column__ON__silver_core_Location);
			qualifier += ", " + file + ":" + Integer.toString(line) + ":" + Integer.toString(col);
		}
		if(!notes.isEmpty()) {
			qualifier += ", " + notes;
		}
		return "'" + self.getName() + "' (" + qualifier + ")";
	}
	
	public final String toString() {
		return getDebugID();
	}
}
