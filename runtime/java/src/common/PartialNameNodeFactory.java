package common;

import java.util.*;


/**
 * Here we are concerning ONLY with partially applying named arguments.
 * 
 * e.g.
 * foo(_, a=y, b=z) -> foo {} {0,1} {y,z}
 * foo(_, a=_, b=_) -> foo {0,1} {} {}
 * foo(_, b=_, a=_) -> foo {1,0} {} {}
 * foo(_, a=y, b=_) -> foo {1} {0} {y}
 * foo(_, b=_, a=y) -> foo {1} {0} {y}
 * foo(_, a=_, b=y) -> foo {0} {1} {y}
 * foo(_, a=_, b??) -> foo {0} {} {}
 * 
 * @param <T>
 * @see PartialNodeFactory  for applying unnamed arguments.
 * @author tedinski
 */
public class PartialNameNodeFactory<T> extends NodeFactory<T> {

	final NodeFactory<? extends T> ref;
    final int[] iConvertedToOrdered;
    final int[] iSuppliedHere;
    final Object[] args;

	/**
	 * We have three concerns:
	 * 1. Supplying the values of some named parameters.
	 * 2. Converting some named parameters to ordered parameters (in some specified order)
	 * 3. Leaving some named parameters alone.
	 * 
	 * @param ref  The NodeFactory we're transforming
	 * @param iConvertedToOrdered  An unordered int list, specifying the indices of named parameters
	 *          that should be tacked onto the end of the ordered parameter list.
	 * @param iSuppliedHere  The ORDERED int list of indicies of named paramters we're filling in now.
	 * @param args  The parameters being supplied, in order
	 */
	public PartialNameNodeFactory(final NodeFactory<? extends T> ref,
			                      final int[] iConvertedToOrdered,
			                      final int[] iSuppliedHere,
			                      final Object[] args) {
		this.ref = ref;
		this.iConvertedToOrdered = (iConvertedToOrdered == null) ? new int[0] : iConvertedToOrdered;
		this.iSuppliedHere = (iSuppliedHere == null) ? new int[0] : iSuppliedHere;
		this.args = args;
	}
	
	@Override
	public T invoke(final common.OriginContext originCtx, final Object[] restargs, final Object[] namedArgs) {
		// STEP 1 : cut 'args' down to the true args we'll be supplying to 'ref'
		final int numConverted = iConvertedToOrdered.length;
		final int newArgsLength = restargs.length - numConverted;
		
		// Here's what we should give ref, as the first parameter:
		final Object[] finalArgs = 
				(restargs.length == newArgsLength) ? restargs : Arrays.copyOf(restargs, newArgsLength);
		
		// STEP 2 : construct the appropriate new namedArgs parameter to pass to the underlying ref
		final int namedArgsLen = (namedArgs == null) ? 0 : namedArgs.length;
		final int argsLen = (args == null) ? 0 : args.length;
		final int fullNamedArgsSize = numConverted + namedArgsLen + argsLen;
		
		// We're filling this in:
		final Object[] fullNamedArgs = new Object[fullNamedArgsSize];
		
		// Step 2.1: Get out of 'restargs' those values that were converted to ordered parameters
		for(int i = newArgsLength; i < restargs.length; i++) {
			fullNamedArgs[iConvertedToOrdered[i-newArgsLength]] = restargs[i];
		}
		
		// Step 2.2: Do the same for 'args' which were supplied at this partial application site.
		for(int i = 0; i < argsLen; i++) {
			fullNamedArgs[iSuppliedHere[i]] = args[i];
		}

		// Step 2.3: Now, we just fill in the empty spaces with the values we're being given
		for(int i = 0, namedArgsIndex = 0; i < fullNamedArgsSize && namedArgsIndex < namedArgsLen; i++) {
			if(fullNamedArgs[i] == null) {
				fullNamedArgs[i] = namedArgs[namedArgsIndex++];
			}
		}
		
		return ref.invoke(originCtx, finalArgs, fullNamedArgs);
	}
	
	@Override
	public final TypeRep getType() {
		// Unpack the function type
		List<TypeRep> typeArgs = new LinkedList<>();
		TypeRep a = ref.getType();
		for (; a instanceof AppTypeRep; a = ((AppTypeRep)a).cons) {
			typeArgs.add(0, ((AppTypeRep)a).arg);
		}
		FunctionTypeRep fnType = (FunctionTypeRep)a;
		List<TypeRep> params = typeArgs.subList(0, fnType.params);
		List<TypeRep> namedParamTypes = typeArgs.subList(fnType.params, fnType.params + fnType.namedParams.length);
		TypeRep resultType = typeArgs.get(fnType.params + fnType.namedParams.length);
		
		// Take existing params and append named parameters converted to ordered params
		List<TypeRep> newArgs = new LinkedList<>();
		newArgs.addAll(params);
		for (int i = 0; i < iConvertedToOrdered.length; i++) {
			newArgs.add(namedParamTypes.get(iConvertedToOrdered[i]));
		}

		// Build a set of converted parameter indices
	    final Set<Integer> iConvertedToOrderedSet = new HashSet<Integer>(iConvertedToOrdered.length);
	    for (int i : iConvertedToOrdered) {
	    	iConvertedToOrderedSet.add(i);
	    }
	    // Construct new named parameter arrays by copying items not supplied or converted
		final String[] newNamedParams = new String[fnType.namedParams.length - (iConvertedToOrdered.length + iSuppliedHere.length)];
		final List<TypeRep> newNamedParamTypes = new ArrayList<>(newNamedParams.length);
		int i = 0, j = 0, k = 0;
		while (k < newNamedParams.length) {
			if (i < iSuppliedHere.length && i + j + k == iSuppliedHere[i]) {
				i++;
			} else if (iConvertedToOrderedSet.contains(j)) {
				j++;
			} else {
				newNamedParams[k] = fnType.namedParams[i + j + k];
				newNamedParamTypes.set(k, namedParamTypes.get(i + j + k));
				k++;
			}
		}
		
		// Add the remaining named params and result to the type arg list
		newArgs.addAll(newNamedParamTypes);
		newArgs.add(resultType);
		
		// Re-pack the function type
		TypeRep result = new FunctionTypeRep(fnType.params + iConvertedToOrdered.length, newNamedParams);
		for (TypeRep arg : newArgs) {
			result = new AppTypeRep(result, arg);
		}
		return result;
	}
	
	@Override
	public final String toString() {
		return "partial named application of " + ref.toString();
	}

}
