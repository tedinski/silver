package common;

import java.util.*;


/**
 * A function resulting from a partially applied annotation update.
 * e.g. x(anno1=4, anno2=_) where x is a nonterminal with annotations anno1 and anno2.
 * 
 * @param <T>
 * @author krame505
 */
public class AnnoUpdateNodeFactory<T extends Node> extends NodeFactory<T> {

	final T node;
    final int[] iConvertedToOrdered;
    final int[] iSuppliedHere;
    final Object[] annosHere;

	/**
	 * @param node  The Node we're updating annotations on
	 * @param iConvertedToOrdered  An unordered int list, specifying the indices of annotations that
	 * 		will be supplied as function parameters.
	 * @param iSuppliedHere  The ORDERED int list of indices of annotations we're updating in now.
	 * @param args  The annotations being supplied, in order
	 */
	public AnnoUpdateNodeFactory(final T node,
			                     final int[] iConvertedToOrdered,
			                     final int[] iSuppliedHere,
			                     final Object[] annosHere) {
		this.node = node;
		this.iConvertedToOrdered = (iConvertedToOrdered == null) ? new int[0] : iConvertedToOrdered;
		this.iSuppliedHere = (iSuppliedHere == null) ? new int[0] : iSuppliedHere;
		this.annosHere = annosHere;
	}
	
	@Override
	@SuppressWarnings("unchecked")
	public T invoke(final common.OriginContext originCtx, final Object[] args, final Object[] namedArgs) {
		assert iConvertedToOrdered.length == 0 && args == null || args.length == iConvertedToOrdered.length;
		// This should never be called with named arguments
		assert namedArgs == null || namedArgs.length == 0;

		final Object[] annos = new Object[node.getAnnoNames().length];

		for(int i = 0; i < iSuppliedHere.length; i++) {
			annos[iSuppliedHere[i]] = annosHere[i];
		}

		for(int i = 0; i < iConvertedToOrdered.length; i++) {
			annos[iConvertedToOrdered[i]] = args[i];
		}

		return (T)node.updateAnnos(annos);
	}
	
	@Override
	public final TypeRep getType() {
		// TODO: need to track the types of the annotations on the node, somehow.
		throw new UnsupportedOperationException("Not implemented yet");
	}
	
	@Override
	public final String toString() {
		return "partially applied annotation update of " + node.toString();
	}

}
