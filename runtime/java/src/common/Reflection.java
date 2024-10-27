package common;

import java.util.*;

import common.exceptions.*;
import silver.core.*;
import java.io.*;

/**
 * Implementation of the Silver reflection library
 * 
 * @author krame505
 */
public final class Reflection {
	/**
	 * Extract a runtime type representation of any object.
	 * 
	 * @param o The object to extract the type. 
	 * @return The type of the object.
	 */
	public static TypeRep getType(final Object o) {
		if(o instanceof Integer) {
			return new BaseTypeRep("Integer");
		} else if(o instanceof Float) {
			return new BaseTypeRep("Float");
		} else if(o instanceof Boolean) {
			return new BaseTypeRep("Boolean");
		} else if(o instanceof Typed){
			return ((Typed)o).getType();
		} else if(o instanceof Thunk) {
			throw new SilverInternalError("Runtime type of an unevaluated Thunk should never be demanded.");
		} else {
			// Not an internal error, since foreign types not implementing Typed will trigger this,
			// but should only be possible with applyAST.
			throw new SilverError("Runtime type checking of object requires class " + o.getClass().getName() + " to implement Typed.");
		}
	}
	
	/**
	 * Create a Silver Maybe<String> object containing an extracted string representation of the
	 * runtime type of an object, if available.
	 * 
	 * @param o The object to extract the type. 
	 * @return just the extracted type representation, if the object is typed, or else nothing().
	 */
	public static NMaybe reflectTypeName(final Object o) {
		String result;
		if(o instanceof Integer) {
			result = "Integer";
		} else if(o instanceof Float) {
			result = "Float";
		} else if(o instanceof Boolean) {
			result = "Boolean";
		} else if(o instanceof Typed){
			result = ((Typed)o).getType().toString();
		} else if(o instanceof Thunk) {
			throw new SilverInternalError("Runtime type of an unevaluated Thunk should never be demanded.");
		} else {
			return new Pnothing();
		}
		return new Pjust(new StringCatter(result));
	}
	
	/**
	 * Implementation of the reflect operation for an arbitrary type.
	 * 
	 * @param rules origins context of the invocation
	 * @param o The object to reflect.
	 * @return The reflected AST.
	 */
	public static NAST reflect(final ConsCell rules, Object o) {
		silver.core.NOriginInfo origin = (rules!=null)?new silver.core.PoriginOriginInfo(o, true, rules, OriginsUtil.SET_FROM_REFLECTION_OIT):null;
		if(o instanceof Node) {
			Node n = (Node)o;
			NASTs children = new PnilAST(origin);
			for (int i = n.getNumberOfChildren() - 1; i >= 0; i--) {
				Object value = reflect(rules, n.getChild(i));
				children = new PconsAST(origin, value, children);
			}
			String[] annotationNames = n.getAnnoNames();
			NNamedASTs annotations = new PnilNamedAST(origin);
			for (int i = annotationNames.length - 1; i >= 0; i--) {
				String name = annotationNames[i];
				Object value = reflect(rules, n.getAnno(name));
				annotations = new PconsNamedAST(origin, new PnamedAST(origin, new StringCatter(name), value), annotations);
			}
			return new PnonterminalAST(origin, new StringCatter(n.getName()), children, annotations);
		} else if(o instanceof Terminal) {
			Terminal t = (Terminal)o;
			return new PterminalAST(origin, new StringCatter(t.getName()), t.lexeme, t.location);
		} else if(o instanceof ConsCell) {
			return new PlistAST(origin, reflectList(rules, origin, (ConsCell)o));
		} else if(o instanceof StringCatter) {
			return new PstringAST(origin, (StringCatter)o);
		} else if(o instanceof Integer) {
			return new PintegerAST(origin, (Integer)o);
		} else if(o instanceof Float) {
			return new PfloatAST(origin, (Float)o);
		} else if(o instanceof Boolean) {
			return new PbooleanAST(origin, (Boolean)o);
		} else {
			return new PanyAST(origin, o);
		}
	}
	private static NASTs reflectList(ConsCell rules, silver.core.NOriginInfo origin, final ConsCell l) {
		if (!l.nil()) {
			return new PconsAST(origin, reflect(rules, l.head()), reflectList(rules, origin, l.tail()));
		} else {
			return new PnilAST(origin);
		}
	}
	
	/**
	 * Implementation of reification with error checking.
	 * 
	 * @param resultType The type of tree to be constructed.
	 * @param ast The AST to reify.
	 * @return An Either<String a> object containing either an error message or a constructed object. 
	 */
	public static NEither reifyChecked(final ConsCell rules, final TypeRep resultType, final NAST ast) {
		try {
			return new Pright(reify(rules, resultType, ast));
		} catch (SilverException e) {
			Throwable rootCause = SilverException.getRootCause(e);
			if (rootCause instanceof SilverError) {
				return new Pleft(new StringCatter("Reification error at " + ReifyTraceException.getASTRepr(e) + ":\n" + rootCause.getMessage()));
			} else {
				throw e;
			}
		}
	}
	
	/**
	 * Implementation of the reify operation for an arbitrary type.
	 * 
	 * @param rules origins context of the invocation of reify
	 * @param resultType The type of tree to be constructed.
	 * @param ast The AST to reify.
	 * @return The constructed object.
	 */
	public static Object reify(final ConsCell rules, final TypeRep resultType, final NAST ast) {
		if (ast instanceof PnonterminalAST) {
			// Unpack production name
			final String prodName = ((StringCatter)ast.getChild(0)).toString();
			
			// Unpack children
			final List<NAST> childASTList = new ArrayList<>(5);
			for (NASTs current = (NASTs)ast.getChild(1); !(current instanceof PnilAST); current = (NASTs)current.getChild(1)) {
				childASTList.add((NAST)current.getChild(0));
			}
			final NAST[] childASTs = childASTList.toArray(new NAST[childASTList.size()]);
			
			// Unpack annotations
			class AnnotationEntry implements Comparable<AnnotationEntry> {
			    public final String name;
			    public final NAST ast;

			    public AnnotationEntry(String name, NAST ast) {
			        this.name = name;
			        this.ast = ast;
			    }

			    public int compareTo(AnnotationEntry other) {
			        return name.compareTo(other.name);
			    }
			}

			final List<AnnotationEntry> annotationASTList = new ArrayList<>();
			for (NNamedASTs current = (NNamedASTs)ast.getChild(2); !(current instanceof PnilNamedAST); current = (NNamedASTs)current.getChild(1)) {
				NNamedAST item = (NNamedAST)current.getChild(0);
				annotationASTList.add(new AnnotationEntry(item.getChild(0).toString(), (NAST)item.getChild(1)));
			}
			Collections.sort(annotationASTList);
			final String[] annotationNames = new String[annotationASTList.size()];
			final NAST[] annotationASTs = new NAST[annotationASTList.size()];
			for (int i = 0; i < annotationASTList.size(); i++) {
				annotationNames[i] = annotationASTList.get(i).name;
				annotationASTs[i] = annotationASTList.get(i).ast;
			}

			RTTIManager.Prodleton<?> pton = RTTIManager.getProdleton(prodName);
			if (pton==null) {
				throw new SilverError("Undefined production " + prodName);
			}

			return pton.reify(ast, rules, resultType, childASTs, annotationNames, annotationASTs);

		} else if (ast instanceof PterminalAST) {
			// Unpack components
			final String terminalName = ((StringCatter)ast.getChild(0)).toString();
			final StringCatter lexeme = (StringCatter)ast.getChild(1);
			final NLocation location = (NLocation)ast.getChild(2);
			
			// Perform unification with the expected type
			if (!TypeRep.unify(resultType, new BaseTypeRep(terminalName))) {
				throw new SilverError("reify is constructing " + resultType.toString() + ", but found terminal " + terminalName + " AST.");
			}

			RTTIManager.Terminalton<?> tton = RTTIManager.getTerminalton(terminalName);
			if (tton==null) {
				throw new SilverError("Undefined terminal " + terminalName);
			}

			return tton.construct(lexeme, location);

		} else if (ast instanceof PlistAST) {
			final TypeRep paramType = new VarTypeRep();
			if (!TypeRep.unify(resultType, new AppTypeRep(new BaseTypeRep("[]"), paramType))) {
				throw new SilverError("reify is constructing " + resultType.toString() + ", but found list AST.");
			}
			return reifyList(rules, paramType, (NASTs)ast.getChild(0));
		} else {
			Object givenObject = ast.getChild(0);
			
			// Construct the TypeRep correpsonding to the given object
			TypeRep givenType;
			if (ast instanceof PstringAST) {
				givenType = new BaseTypeRep("String");
			} else if (ast instanceof PintegerAST) {
				givenType = new BaseTypeRep("Integer");
			} else if (ast instanceof PfloatAST) {
				givenType = new BaseTypeRep("Float");
			} else if (ast instanceof PbooleanAST) {
				givenType = new BaseTypeRep("Boolean");
			} else if (ast instanceof PanyAST) {
				givenType = getType(givenObject);
			} else {
				throw new SilverInternalError("Unexpected AST production " + ast.getName());
			}
			// Perform unification with the expected type
			if (!TypeRep.unify(resultType, givenType)) {
				throw new SilverError("reify is constructing " + resultType.toString() + ", but found " + givenType.toString() + " AST.");
			}
			return givenObject;
		}
	}
	// Recursive helper to walk the ASTs tree and build a list
	private static ConsCell reifyList(final ConsCell rules, final TypeRep resultParamType, final NASTs asts) {
		if (asts instanceof PconsAST) {
			Object head;
			try {
				head = reify(rules, resultParamType, (NAST)asts.getChild(0));
			} catch (SilverException e) {
				throw new ConsReifyTraceException(true, e);
			}
			ConsCell tail;
			try {
				tail = reifyList(rules, resultParamType, (NASTs)asts.getChild(1));
			} catch (SilverException e) {
				throw new ConsReifyTraceException(false, e);
			}
			return new ConsCell(head, tail);
		} else if (asts instanceof PnilAST) {
			return ConsCell.nil;
		} else {
			throw new SilverInternalError("Unexpected ASTs production " + asts.getName());
		}
	}
	
	/**
	 * Apply a function wrapped in AST to AST arguments.
	 * 
	 * @param fn An AnyAST containing the argument.
	 * @param args A list of Maybe<AST> arguments or holes for partial application.
	 * @param namedArgs A list of Pair<String Maybe<AST>> named arguments or holes for partial application.
	 * @return An Either<String a> object containing either an error message or the reflected result of calling the function.
	 */
	public static NEither applyAST(final OriginContext ctx, final NAST fn, final ConsCell args, final ConsCell namedArgs) {
		// Unpack function
		if (!(fn instanceof PanyAST) || !(fn.getChild(0) instanceof NodeFactory)) {
			return new Pleft(new StringCatter("Expected a function AST"));
		}
		NodeFactory<?> givenFn = (NodeFactory<?>)(fn.getChild(0));
		
		// Unpack the function type
		List<TypeRep> typeArgs = new LinkedList<>();
		TypeRep a = givenFn.getType();
		for (; a instanceof AppTypeRep; a = ((AppTypeRep)a).cons) {
			typeArgs.add(0, ((AppTypeRep)a).arg);
		}
		FunctionTypeRep fnType = (FunctionTypeRep)a;
		List<TypeRep> params = typeArgs.subList(0, fnType.params);
		List<TypeRep> namedParamTypes = typeArgs.subList(fnType.params, fnType.params + fnType.namedParams.length);
		//TypeRep resultType = typeArgs.get(fnType.params + fnType.namedParams.length);

		final ConsCell rules = ctx.rulesAsSilverList();
		
		// Unpack args
		final List<Integer> argIndexList = new ArrayList<>(5);
		final List<Object> argList = new ArrayList<>(5);
		int i = 0;
		for (ConsCell current = args; !current.nil(); current = current.tail()) {
			if (i >= fnType.params) {
				return new Pleft(new StringCatter("Expected only " + fnType.params + " arguments, but got " + args.length()));
			}
			final NMaybe item = (NMaybe)current.head();
			if (item instanceof Pjust) {
				argIndexList.add(i);
				try {
					argList.add(reify(rules, params.get(i), (NAST)item.getChild(0)));
				} catch (SilverException e) {
					Throwable rootCause = SilverException.getRootCause(e);
					if (rootCause instanceof SilverError) {
						return new Pleft(new StringCatter("Reification error in argument " + i + " at " + ReifyTraceException.getASTRepr(e) + ":\n" + rootCause.getMessage()));
					} else {
						throw e;
					}
				}
			}
			i++;
		}
		if (i < fnType.params) {
			return new Pleft(new StringCatter("Expected " + fnType.params + " arguments, but got only " + i));
		}
		
		// Unpack named args
		final List<Integer> convertedIndexList = new ArrayList<>();
		final List<Integer> suppliedIndexList = new ArrayList<>();
		final List<Object> namedArgList = new ArrayList<>();
		final Object[] reorderedNamedArgs = new Object[fnType.namedParams.length];
		for (ConsCell current = namedArgs; !current.nil(); current = current.tail()) {
			final NPair entry = (NPair)current.head();
			final String name = entry.getAnno_silver_core_fst().toString();
			int index = Arrays.asList(fnType.namedParams).indexOf(name);
			if (index == -1) {
				return new Pleft(new StringCatter("Unexpected named argument " + name));
			}
			final NMaybe item = (NMaybe)entry.getAnno_silver_core_snd();
			if (item instanceof Pjust) {
				Object o;
				try {
					o = reify(rules, namedParamTypes.get(index), (NAST)item.getChild(0));
				} catch (SilverException e) {
					Throwable rootCause = SilverException.getRootCause(e);
					if (rootCause instanceof SilverError) {
						return new Pleft(new StringCatter("Reification error in named argument " + name + " at " + ReifyTraceException.getASTRepr(e) + ":\n" + rootCause.getMessage()));
					} else {
						throw e;
					}
				}
				suppliedIndexList.add(index);
				namedArgList.add(o);
				reorderedNamedArgs[index] = o;
			} else {
				convertedIndexList.add(index);
			}
			i++;
		}
		
		Object result;
		if (argList.size() < fnType.params || namedArgList.size() < fnType.namedParams.length) {
			// Apply partial
			result = givenFn
					.invokePartial(argIndexList.stream().mapToInt(n -> n).toArray(), argList.toArray())
					.invokeNamedPartial(
							convertedIndexList.stream().mapToInt(n -> n).toArray(),
							suppliedIndexList.stream().mapToInt(n -> n).toArray(),
							namedArgList.toArray());
		} else {
			// Apply regular
			result = givenFn.invoke(ctx, argList.toArray(), reorderedNamedArgs);
		}
		return new Pright(reflect(rules, result));
	}

	
	////////////////////////////////////////////////////////////////////////////////////////////////
	// This is the machinery for nativeSerialize/nativeDeserialize. It is a bespoke binary
	//  format written/read via java's DataOutputStream/DataInputStream machinery.
	//  
	//  This is an OPAQUE serialization format, and must not be modified. Type-safety
	//  of nativeDeserialize (silver type-safety) depends on the stored value being
	//  well-formed (i.e., produced by nativeSerialize from a well-typed silver value.)
	//
	//  We use the writeUTF/readUTF helpers from java to write and read strings. This internally
	//  is length+data, and allows us to treat strings as units.
	//
	//  Files start with a header to make sure we don't try to interpret garbage. Then there
	//  is a lookup table of production names, which are indexed into by serialized production
	//  values. This means that names are only looked up as strings once in the prodleton dictionary.
	//  This table also contains opaque string representations of the types of the productions, which are
	//  compared to the string type reps of productions in the deserializing silver (stored on
	//  prodletons.) This prevents type confusion if the definition of a serialized nonterminal is
	//  changed.
	//
	//  Serialized values start with a one-byte type tag, then some body. Primitives are stored
	//  directly. Lists have a special-case serialization (length+items). Terminals are stored
	//  with their full name, looked up at deserialization. [If we started serializing lots of CSTs
	//  we could do the same lookup table thing we do with productions to speed this up. We could also
	//  make that faster by special-casing storing the Location value (currently it is stored as a
	//  'normal' nonterminal value.) But we don't really ever serialize terminals so it dosen't matter 
	//  much.] Productions store the index of the entry in the production table, and then the children
	//  and annotations. Deserialization machinery must interrogate the prodleton to know how many
	//  children and annos to read (we are guaranteed it has not changed by the type rep check when
	//  loading the prod table.) Nonterminals are then constructed via constructDirect with NO
	//  typechecking on erased values (so it is important that this is an opaque format, since then
	//  the type-safety is guaranteed by it's having been produced from a valid silver value.)
	//  Annotations are in whatever arbitrary order they are in in the translation, and the opaque
	//  type identifier prevents this from violating type safety. If we ever use more than `location`,
	//  revisit this.
	//
	//  One final reify is invoked to make sure that the types match for polymorphic serialized types.
	//  No typedata is stored, so this is reifying the expected type with the getType of the deserialized
	//  type.
	//
	//  Decorated nodes are not supported. Foreign types are not supported.
	//
	//  This is a more fragile format w/r/t changes in the silver program saving/loading it than the
	//   textual one (e.g. reordering annotations, changing children names, will cause a deserialization
	//   failure) and should only be used for caching. But it is MUCH faster and about 50% more
	//   space-efficient than the textual one.
	//
    // File: SVB\0<\n><1b version (0)><index array><item>
    // item: <0><string>                                - String
    //       <1><4b integer>                            - Integer
    //       <2>                                        - false
    //       <3>                                        - true
    //       <4><4b float>                              - float
    //       <5><name string><children><annos>          - production (children, annos = items)
    //       <6><name string><lexeme><location (item)>  - terminal (location = item)
    //       <7><2b length><data>                       - list (data = items)
    //       <8><4b length><data>                       - long list for dawn :) -- separate for backwards compat because it was easy
    //
    // index array: <2b nt count><that many ntrecs...>
    // ntrec: <name string><type string>
    // 
    // strings, ints, etc are writeUTF/writeInt/writeShort format (so integers are big-endian), see
    //  https://docs.oracle.com/javase/7/docs/api/java/io/DataOutputStream.html#writeUTF(java.lang.String)
    //  for details on writeUTF (basically a 2b length then UTF-8).
    //
    // @author louisg

    private static class NativeSerializationException extends IOException {
    	public NativeSerializationException(String x) { super(x); }
    }

    // Serialize x into a bytearray
    // x::a -> Either<String ByteArrray>
	public static NEither nativeSerialize(Object x) {
		try{
			ByteArrayOutputStream arr = new ByteArrayOutputStream(10_000_000);
			DataOutputStream o = new DataOutputStream(arr);

			o.writeBytes("SVB\0\n\0"); // Header

			ArrayList<RTTIManager.Prodleton<?>> prodset = new ArrayList<RTTIManager.Prodleton<?>>();

			nSerGetProdSet(prodset, x); // Compute set of productions

			if (prodset.size() > 1<<15) throw new NativeSerializationException("Too many productions for native serialize");
			o.writeShort(prodset.size()); // Write lookup table size

			for (RTTIManager.Prodleton<?> p : prodset) { // Write lookup table. For each prod:
				o.writeUTF(p.getName());              //  fully qualified silver prod name 
				o.writeUTF(p.getTypeUnparse());       //  opaque typerep
			}

			nSerItem(o, prodset, x); // Serialize the value

			return new Pright(arr.toByteArray());
		} catch (NativeSerializationException e) {
			return new Pleft(new StringCatter("Native serialize failed: " + e.getMessage()));
		} catch (Exception e) {
			String m = "Native serialize failed: Unknown error: " + e.toString();
			System.err.println(m);
			return new Pleft(new StringCatter(m));
		}
	}

	// Recursively compute the set of productions used in the object, adding their prodletons once to `s`.
	//  This forms the production lookup table.
	public static void nSerGetProdSet(ArrayList<RTTIManager.Prodleton<?>> s, Object x) {
		if(x instanceof Node) {
			Node n = (Node)x;
			if (s.indexOf(n.getProdleton()) == -1) s.add(n.getProdleton());

			for (int i = 0; i < n.getNumberOfChildren(); i++) {
				nSerGetProdSet(s, n.getChild(i));
			}

			String[] annotationNames = n.getAnnoNames();
			
			for (int i = 0; i < annotationNames.length; i++) {
				String name = annotationNames[i];
				nSerGetProdSet(s, n.getAnno(name));
			}
		} else if (x instanceof Terminal) {
			nSerGetProdSet(s, ((Terminal)x).location);
		} else if (x instanceof ConsCell) {
			ConsCell c = (ConsCell) x;
			while (c != ConsCell.nil) {
				nSerGetProdSet(s, c.head());
				c = c.tail();
			}
		}
	}


	// Serialize a single value `x` into `o`, using `s` as production lookup table
	public static void nSerItem(DataOutputStream o, ArrayList<RTTIManager.Prodleton<?>> s, Object x) throws IOException {
		if(x instanceof Node) {
			Node n = (Node)x;

			o.writeByte(5); // type tag
			o.writeShort(s.indexOf(n.getProdleton())); // index of this production in prod lookup table

			String[] annotationNames = n.getAnnoNames();

			for (int i = 0; i < n.getNumberOfChildren(); i++) {
				nSerItem(o, s, n.getChild(i)); // serialize all children
			}
			
			for (int i = 0; i < annotationNames.length; i++) {
				String name = annotationNames[i];
				nSerItem(o, s, n.getAnno(name)); // serialize all annos
			}
		} else if(x instanceof Terminal) {
			Terminal t = (Terminal)x;
			
			o.writeByte(6); // type tag
			o.writeUTF(t.getTerminalton().getName()); // store name of terminal
			o.writeUTF(t.lexeme.toString()); // store lexeme
			nSerItem(o, s, t.location); // store location (which is a NT, so recurse to store it as an item)

		} else if(x instanceof ConsCell) {
			ConsCell c = (ConsCell)x;

			int listLen = c.length();

			if (listLen > 1<<30 || listLen < 0) throw new NativeSerializationException("List too long for native serialize");

			if (listLen > 1<<15) {
				o.writeByte(8); // type tag for 32-bit-count list
				o.writeInt(listLen); // store length of list
			} else {
				o.writeByte(7); // type tag for 16-bit-count (original) list
				o.writeShort(listLen); // store length of list
			}

			while (c!=ConsCell.nil) {
				nSerItem(o, s, c.head()); // store items of list ("forward")
				c = (ConsCell)c.tail();
			}
		} else if(x instanceof StringCatter) {
			o.writeByte(0); // type tag
			o.writeUTF(((StringCatter)x).toString()); // string value
		} else if(x instanceof Integer) {
			o.writeByte(1); // type tag
			o.writeInt((int)x); // integer value
		} else if(x instanceof Float) {
			o.writeByte(4); // type tag
			o.writeFloat((float)x); // float value
		} else if(x instanceof Boolean) {
			if ((boolean)x) o.writeByte(3); // type tag/value for true
			else o.writeByte(2); // type tag/value for false
		} else if(x instanceof DecoratedNode) {
			throw new NativeSerializationException("Cannot serialize DecoratedNodes (prod " + x.toString() + ")");
		} else {
			throw new NativeSerializationException("Unserializable type encountered: " + x.toString());
		}
	}

	// Deserialize `arr` into a silver object
	// RuntimeTypable x => ByteArray -> Either<String x>
	public static NEither nativeDeserialize(final TypeRep expected, final byte[] arr) {
		try{
			ByteArrayInputStream ins = new ByteArrayInputStream(arr);
			DataInputStream i = new DataInputStream(ins);

			byte header[] = "SVB\0\n\0".getBytes("ASCII");
			byte[] buf = new byte[6];
			i.readFully(buf, 0, 6); // Read header

			if (!Arrays.equals(header, buf)) throw new NativeSerializationException("Not a SVB serialization");

			int prodCount = i.readShort(); // length of prod lookup table

			ArrayList<RTTIManager.Prodleton<?>> lookup = new ArrayList<RTTIManager.Prodleton<?>>(prodCount);
			for (int c = 0; c < prodCount; c++) {
				String name = i.readUTF(); // Read name of prod
				String opaqueTypeIdentifier = i.readUTF(); // Read opaque type identifier

				RTTIManager.Prodleton<?> pton = RTTIManager.getProdleton(name);
				if (pton == null) throw new NativeSerializationException("Unknown production: " + name);
				if (!pton.getTypeUnparse().equals(opaqueTypeIdentifier))
					throw new NativeSerializationException("Production " + name + " changed type since serialization (from `" + opaqueTypeIdentifier + "` to `" + pton.getTypeUnparse() + "`)");
				
				lookup.add(pton);
			}

			Object v = nDeserItem(lookup, i); // Deserialize the stored item

			if (!TypeRep.unify(expected, getType(v))) { // Run a unification check to ensure silver type-safety
				return new Pleft(new StringCatter("Native deserialize is constructing " + expected.toString() + ", but found " + getType(v).toString()));
			}

			return new Pright(v);
		} catch (NativeSerializationException e) {
			return new Pleft(new StringCatter("Native deserialize failed: " + e.getMessage()));
		} catch (IOException e) {
			String m = "Native deserialize failed: Unknown Error: " + e.toString();
			System.err.println(m);
			return new Pleft(new StringCatter(m));
		}
	}

	// Deserialize a single item from stream `i` using prod lookup table `s`
	public static Object nDeserItem(ArrayList<RTTIManager.Prodleton<?>> s, DataInputStream i) throws IOException {
		int typeId = i.readByte(); // read type-tag

		if (typeId == 5) { // production

			int orderedIndex = i.readShort(); // read index and retrieve prodleton from lookup
			RTTIManager.Prodleton<?> pton = s.get(orderedIndex);

			int childCount = pton.getChildCount(); // get number of children to load
			Object children[] = new Object[childCount];

			for (int n = 0; n < childCount; n++) {
				children[n] = nDeserItem(s, i); // ...and load them
			}

			int annoCount = pton.getAnnoCount(); // get number of annos to load
			Object annos[] = new Object[annoCount];

			for (int n = 0; n < annoCount; n++) {
				annos[n] = nDeserItem(s, i); // ...and load them
			}

			return pton.constructDirect(children, annos); // construct value
		} else if (typeId == 6) { // terminal
			String name = i.readUTF(); // read the terminal name
			RTTIManager.Terminalton<?> tton = RTTIManager.getTerminalton(name);

			if (tton == null)
				throw new NativeSerializationException("Can't find terminal " + name);

			String lexeme = i.readUTF();
			Object location = nDeserItem(s, i); // deserialize the location as an item

			return tton.construct(new StringCatter(lexeme), (NLocation)location);
		} else if (typeId == 7 || typeId == 8) { // list
			int length;

			if (typeId == 7) length = i.readShort(); // 16-bit-count (original) list
			else             length = i.readInt();   // 32-bit-count list

			Object values[] = new Object[length];

			for (int c=0; c<length; c++) {
				values[c] = nDeserItem(s, i); // stored in "forwards" order
			}

			ConsCell l = ConsCell.nil;

			for (int c=length-1; c>=0; c--) {
				l = new ConsCell(values[c], l); // traverse "backwards" to construct cons-list
			}

			return l;
		} else if (typeId == 0) { // string primitive
			return new StringCatter(i.readUTF());
		} else if (typeId == 1) { // int primitive
			return i.readInt();
		} else if (typeId == 4) { // float primitive
			return i.readFloat();
		} else if (typeId == 3) { // bool primitive
			return true;
		} else if (typeId == 2) { // bool primitive
			return false;
		} else {
			throw new NativeSerializationException("Unknown type id (" + Integer.toString(typeId) + ")");
		}
	}

	/**
	 * Try to access an inherited attribute from a DecoratedNode, by name.
	 * @param node  A DecoratedNode on which to compute the attribute.
	 * @param attr  The name of the inherited attribute to access. 
	 * @return An Either<String a> object containing either an error message or the reflected result of evaluating the attribute.
	 */
	public static NEither getInherited(final TypeRep expected, final DecoratedNode d, final String attr) {
		RTTIManager.Nonterminalton<?> nt = d.getNode().getProdleton().getNonterminalton();
		if (!nt.hasInh(attr)) {
			return new Pleft(new StringCatter("Inherited attribute " + attr + " does not occur on " + nt.getName()));
		}
		int i = nt.getInhOccursIndex(attr);
		Object res;
		try {
			res = d.inherited(i);
			traverseTerm(res);
		} catch (Throwable t) {
			return new Pleft(new StringCatter(SilverException.getRootCause(t).getMessage()));
		}
		if (!TypeRep.unify(expected, getType(res))) {
			return new Pleft(new StringCatter("getInherited expected " + expected.toString() + ", but " + attr + " on " + nt.getName() + " gave type " + getType(res).toString()));
		}
		return new Pright(res);
	}

	/**
	 * Try to access a synthesized attribute from a node, by name.
	 * @param node  A Node or DecoratedNode on which to compute the attribute.
	 * @param attr  The name of the synthesized attribute to access. 
	 * @return An Either<String a> object containing either an error message or the reflected result of evaluating the attribute.
	 */
	public static NEither getSynthesized(final TypeRep expected, final Object o, final String attr) {
		if (!(o instanceof Decorable)) {
			return new Pleft(new StringCatter(getType(o).toString() + " does not have attributes"));
		}
		DecoratedNode d = ((Decorable)o).decorate();
		RTTIManager.Nonterminalton<?> nt = d.getNode().getProdleton().getNonterminalton();
		if (!nt.hasSyn(attr)) {
			return new Pleft(new StringCatter("Synthesized attribute " + attr + " does not occur on " + nt.getName()));
		}
		int i = nt.getSynOccursIndex(attr);
		Object res;
		try {
			res = d.synthesized(i);
			traverseTerm(res);
		} catch (Throwable t) {
			return new Pleft(new StringCatter(SilverException.getRootCause(t).getMessage()));
		}
		if (!TypeRep.unify(expected, getType(res))) {
			return new Pleft(new StringCatter("getSynthesized expected " + expected.toString() + ", but " + attr + " on " + nt.getName() + " gave type " + getType(res).toString()));
		}
		return new Pright(res);
	}

	/**
	 * Recursively force the evaluation of a term, catching any errors.
	 * @param o  A Thunk or Node to force
	 * @return An Either<String a> containing either an error message or the forced input.
	 */
	public static NEither tryForceTerm(Object o) {
		try {
			traverseTerm(o);
		} catch (Throwable t) {
			return new Pleft(new StringCatter(SilverException.getRootCause(t).getMessage()));
		}
		return new Pright(o);
	}
	private static void traverseTerm(Object o) {
		if (o instanceof Thunk) {
			o = Util.demand(o);
		}
		if (o instanceof Node) {
			Node n = (Node)o;
			for (int i = n.getNumberOfChildren() - 1; i >= 0; i--) {
				traverseTerm(n.getChild(i));
			}
			String[] annotationNames = n.getAnnoNames();
			for (int i = annotationNames.length - 1; i >= 0; i--) {
				String name = annotationNames[i];
				traverseTerm(n.getAnno(name));
			}
		}
	}
}
