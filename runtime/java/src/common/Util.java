package common;

import java.io.*;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;
import java.util.stream.Collectors;
import java.net.URI;
import java.util.jar.JarInputStream;
import java.util.jar.Attributes.Name;

import common.exceptions.*;
import common.javainterop.ConsCellCollection;
import silver.core.NLocation;
import silver.core.NParseError;
import silver.core.NParseResult;
import silver.core.NTerminalDescriptor;
import silver.core.Ploc;
import silver.core.PparseFailed;
import silver.core.PsyntaxError;
import silver.core.PterminalDescriptor;
import silver.core.PunknownParseError;
import edu.umn.cs.melt.copper.runtime.engines.CopperParser;
import edu.umn.cs.melt.copper.runtime.logging.CopperParserException;
import edu.umn.cs.melt.copper.runtime.logging.CopperSyntaxError;

/**
 * Many places in Silver's translation are bits of code that need factoring out, somehow.
 * 
 * <p>The most common justification is the need to do several statements, while being in the middle
 * of an expression.
 * 
 * @author tedinski, bodin, krame505
 */
public final class Util {
	private static String forceInit;
	private static ArrayList<Integer> freeThisToPrintErrors;

	public static void init() {
		// forceInit = "foo" + "bar" + "baz";
		// freeThisToPrintErrors = new ArrayList<Integer>();
		// for (int i=0; i<1_000_000; i++) {
		// 	freeThisToPrintErrors.add(i);
		// }
	}

	public static void stackProbe(int count) {
		long a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z;
		long aa, bb, cc, dd, ee, ff, gg, hh, ii, jj, kk, ll, mm, nn, oo, pp, qq, rr, ss, tt, uu, vv, ww, xx, yy, zz;
		if (count!=0) stackProbe(count-1);
	}

	public static void stackProbe() {
		// stackProbe(1_000);
	}


	/**
	 * There are some places in the translation where we need to perform unchecked casts,
	 * known to be safe via Silver's static type system.
	 * Java doesn't have a nice way of suppressing warnings on individual subexpressions,
	 * so this function exists as a proxy.
	 *
	 * @param o An object
	 * @return o
	 */
	@SuppressWarnings("unchecked")
	public static <T> T uncheckedCast(final Object o) {
		return (T) o;
	}

	/**
	 * Ensures that a (potential) thunk is evaluated.
	 *
	 * Use by writing  (v = Util.demand(v)), never just invoke it!
	 *
	 * @param c  Either a value, or a Thunk
	 * @return The value, either directly, or evaluating the Thunk
	 */
	@SuppressWarnings("unchecked")
	public static <T> T demand(final Object c) {
		if(c instanceof Thunk)
			return ((Thunk<T>)c).eval();
		return (T)c;
	}

	/**
	 * Demand a (potential) thunk in an array of thunks, caching the resulting value.
	 * This is factored out for the translation of demanding lambda arguments, to avoid unchecked casts.
	 *
	 * @param cs  An array that are either values or Thunks
	 * @param i An index in the array
	 * @return The value, either directly, or evaluating the Thunk at the index
	 */
	public static <T> T demandIndex(final Object[] cs, final int i) {
		T result = demand(cs[i]);
		cs[i] = result;
		return result;
	}

	/**
	 * Turns a list of names and values into a map.
	 *
	 * <p>Used by the 'decorate ... with { THIS PART }' syntax.
	 */
	public static Lazy[] populateInh(final int size, final int[] idx, final Lazy[] val) {
		final Lazy[] result = new Lazy[size];
		for(int i = 0; i < idx.length; i++) {
			result[idx[i]] = val[i];
		}
		return result;
	}

	/**
	 * Used by the 'error("wat")' syntax in Silver.
	 *
	 * @param o the "wat"
	 * @return Does not return.
	 */
	public static Object error(Object o) {
		System.err.print(o);
		throw new SilverError(o.toString());
	}

	public static silver.core.NMaybe safetoInt(String s) {
		try {
			return new silver.core.Pjust(Integer.valueOf(s) );
		} catch(NumberFormatException e) {
			return new silver.core.Pnothing();
		}
	}

	public static boolean isAlpha(String sb) {
		boolean result = true;
		for (int i = 0; result && i < sb.length(); i++) {
			result = Character.isLetter(sb.charAt(i));
		}
		return result;
	}

	public static boolean isDigit(String sb) {
		boolean result = true;
		for (int i = 0; result && i < sb.length(); i++) {
			result = Character.isDigit(sb.charAt(i));
		}
		return result;
	}

	public static boolean isSpace(String sb) {
		boolean result = true;
		for (int i = 0; result && i < sb.length(); i++) {
			result = Character.isWhitespace(sb.charAt(i));
		}
		return result;
	}

	public static boolean isUpper(String sb) {
		boolean result = true;
		for (int i = 0; result && i < sb.length(); i++) {
			result = Character.isUpperCase(sb.charAt(i));
		}
		return result;
	}

	public static boolean isLower(String sb) {
		boolean result = true;
		for (int i = 0; result && i < sb.length(); i++) {
			result = Character.isLowerCase(sb.charAt(i));
		}
		return result;
	}

	/**
	 * This exists only because some things like {@link Util#writeFile} don't take an IO object, so
	 * we use this to demand the io object, then call writeFile.
	 *
	 * <p>In other cases, we're actually returning something, like system, and the call to the IOInteger
	 * nonterminal constructor takes care of demanding the old IO object.
	 *
	 * @param i First thing to do
	 * @param o Second thing to do
	 * @return o, the second thing given, which is intended to be the
	 * IO token.
	 */
	public static Object io(Object i, Object o) {
		return o;
	}

	private static int i = 0;
	public static int genInt() {
		return i++;
	}

	public static void printStackCauses(Throwable e) {
		freeThisToPrintErrors = null;

		System.err.println("\nAn error occurred.  Silver stack trace follows. (To see full traces including java elements, SILVERTRACE=1)\n");

		if(! "1".equals(System.getenv("SILVERTRACE"))) {
			Throwable t = e;
			while(t != null) {
				StackTraceElement st[] = t.getStackTrace();

				String msg = t.getLocalizedMessage();
				if(msg == null) // Some exceptions have no message... apparently.
					msg = t.toString();

				if(t instanceof CycleTraceException) {
					System.err.println("\tCycle begins here:");
				} else if(st.length == 0) {
					// Some exceptions don't seem to occur anywhere... somehow.
					System.err.println("(??): " + msg);
				} else if(st[0].getClassName().startsWith("common.")) {
					// This will give error messages like (DN.146) corresponding to DecoratedNode.java:146
					System.err.println("(" + st[0].getFileName().replaceAll("[a-z]", "") + st[0].getLineNumber() + "): " + msg);
				} else {
					// Be more explicit about where when it's not one of ours
					System.err.println("(" + st[0].getClassName() + " in " + st[0].getFileName() + ":" + st[0].getLineNumber() + "): " + msg);
					if(t instanceof NullPointerException && st.length > 1) {
						System.err.println("\t1 up: " + st[1].getClassName() + " in " + st[1].getFileName() + ":" + st[1].getLineNumber());
						if(st.length > 2)
							System.err.println("\t2 up: " + st[2].getClassName() + " in " + st[2].getFileName() + ":" + st[2].getLineNumber());
					}
				}

				String lastCause = t.getLocalizedMessage();
				int repeats = 0;
				t = t.getCause();
				while(t != null && lastCause.equals(t.getLocalizedMessage())) {
					repeats++;
					t = t.getCause();
				}
				if(repeats > 0) {
					System.err.println("\t(last line repeats " + repeats + " more times)");
				}
			}

			System.exit(-2);
		} else {
			// Displaying it by rethrowing it.
			throw new RuntimeException(e);
		}
	}

	public static String namesToString(final String[] names, final String none) {
		String result = names.length > 0? names[0] : none;
		for (int i = 1; i < names.length; i++) {
			result += ", " + names[i];
		}
		return result;
	}

	public static StringCatter escapeString(final StringCatter s) {
		return new StringCatter(escapeString(s.toString()));
	}
	public static String escapeString(final String s) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < s.length(); i++) {
			char c = s.charAt(i);
			switch (c) {
			case '\t':
				sb.append("\\t");
				break;
			case '\b':
				sb.append("\\b");
				break;
			case '\n':
				sb.append("\\n");
				break;
			case '\r':
				sb.append("\\r");
				break;
			case '\f':
				sb.append("\\f");
				break;
			case '\"':
				sb.append("\\\"");
				break;
			case '\\':
				sb.append("\\\\");
				break;
			default:
				sb.append(c);
			}
		}
		return sb.toString();
	}

	public static StringCatter unescapeString(final StringCatter s) {
		return new StringCatter(unescapeString(s.toString()));
	}
	public static String unescapeString(final String s) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < s.length(); i++) {
			char c = s.charAt(i);
			if (c == '\\') {
				i++;
				if (i < s.length()) {
					char c1 = s.charAt(i);
					switch (c1) {
					case 't':
						sb.append("\t");
						break;
					case 'b':
						sb.append("\b");
						break;
					case 'n':
						sb.append("\n");
						break;
					case 'r':
						sb.append("\r");
						break;
					case 'f':
						sb.append("\f");
						break;
					case '\"':
						sb.append("\"");
						break;
					case '\\':
						sb.append("\\");
						break;
					default:
						sb.append(c1);
					}
				}
			} else {
				sb.append(c);
			}
		}
		return sb.toString();
	}

	// These are written un-ideally so that they're all confined in one place.
	public static StringCatter hackyhackyUnparse(Object o) {
		StringBuilder sb = new StringBuilder();

		hackyhackyUnparseObject(o, sb);

		return new StringCatter(sb.toString());
	}

	private static void hackyhackyUnparseObject(Object o, StringBuilder sb) {
		if(o instanceof Node) {
			hackyhackyUnparseNode((Node)o, sb);
		} else if(o instanceof DecoratedNode) {
			// For the time being, just grab the underlying Node (don't copy-undecorate!)
			hackyhackyUnparseNode(((DecoratedNode)o).getNode(), sb);
		} else if(o instanceof Terminal) {
			Terminal t = (Terminal) o;
			sb.append("'" + t.lexeme + "'");
		} else if(o instanceof StringCatter) {
			sb.append("\"" + o.toString() + "\"");
		} else if(o instanceof Integer ||
			  o instanceof Float ||
 			  o instanceof Boolean) {
			sb.append(o.toString());
		} else if(o instanceof ConsCell) {
			hackyhackyUnparseList((ConsCell)o, sb);
		} else {
			sb.append("<OBJ " + o.toString() + ">");
		}
	}
	private static void hackyhackyUnparseNode(Node n, StringBuilder sb) {
		sb.append(n.getName() + "(");
		int nc = n.getNumberOfChildren();
		for(int i = 0; i < nc; i++) {
			if(i != 0) {
				sb.append(", ");
			}
			hackyhackyUnparseObject(n.getChild(i), sb);
			//System.out.println(sb.toString());
		}
		String[] annos = n.getAnnoNames();
		for(int i = 0; i < annos.length; i++) {
			if(!annos[i].equals("silver:core:location")) {
				if(nc != 0 || i != 0) {
					sb.append(", ");
				}
				sb.append(annos[i] + "=");
				hackyhackyUnparseObject(n.getAnno(annos[i]), sb);
				//System.out.println(sb.toString());
			}
		}
		sb.append(")");
	}
	private static void hackyhackyUnparseList(ConsCell c, StringBuilder sb) {
		sb.append("[");
		ConsCell i = c;
		while(!i.nil()) {
			if(i != c) {
				sb.append(", ");
			}
			hackyhackyUnparseObject(i.head(), sb);
			i = i.tail();
		}
		sb.append("]");
	}

	/**
	 * Attempt to use the improved genericPP from silver:langutil:reflect if that library is available;
	 * else fall back to hackUnparse.
	 * Note that we can't actually let the runtime/silver:core depend on that library,
	 * thus we attempt to call it via reflection.
	 * 
	 * @param o  The object to show
	 * @return A string representation.
	 */
	public static StringCatter genericShow(Object o) {
		try {
			Method genericPP = Class.forName("silver.langutil.reflect.PgenericPP")
				.getMethod("invoke", OriginContext.class, Object.class);
			Method showDoc = Class.forName("silver.langutil.pp.PshowDoc")
				.getMethod("invoke", OriginContext.class, Object.class, Object.class);
			Object pp = genericPP.invoke(null, OriginContext.FFI_CONTEXT, o);
			return (StringCatter)showDoc.invoke(null, OriginContext.FFI_CONTEXT, 80, pp);
		} catch(ClassNotFoundException | NoSuchMethodException | SecurityException |
		        IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
			return hackyhackyUnparse(o);
		}
	}

	/**
	 * Calls a Copper parser, and returns a ParseResult<ROOT> object.
	 *
	 * @param parser The Copper parser to call
	 * @param string The string to parse.
	 * @param file The filename to report to the parser (filling in location information)
	 * @return A silver ParseResult<ROOT> node.
	 */
	public static <ROOT> NParseResult callCopperParser(SilverCopperParser<ROOT> parser, Object string, Object file) {
		String javaString = ((StringCatter)demand(string)).toString();
		String javaFile = ((StringCatter)demand(file)).toString();
		try {
			ROOT tree = parser.parse(new StringReader(javaString), javaFile);
			Object terminals = getTerminals(parser);
			return new silver.core.PparseSucceeded(tree, terminals);
		} catch(CopperSyntaxError e) {
			// To create a space, we increment the ending columns and indexes by 1.
			NLocation loc = new Ploc(new StringCatter(e.getVirtualFileName()),
				e.getVirtualLine(),
				e.getVirtualColumn(),
				e.getVirtualLine(),
				e.getVirtualColumn() + 1,
				(int)(e.getRealCharIndex()),
				(int)(e.getRealCharIndex()) + 1);
			NParseError err = new PsyntaxError(new common.StringCatter(e.getMessage()),
					loc,
					convertStrings(e.getExpectedTerminalsDisplay().iterator()),
					convertStrings(e.getMatchedTerminalsDisplay().iterator()));
			Object terminals = getTerminals(parser);
			return new PparseFailed(err, terminals);
		} catch(CopperParserException e) {
			// Currently this is dead code, but perhaps in the future we'll see IOException wrapped in here.
			NParseError err = new PunknownParseError(new StringCatter(e.getMessage()), file);
			return new PparseFailed(err, null);
		} catch(Throwable t) {
			throw new TraceException("An error occurred while parsing", t);
		}
	}

	/**
	 * Returns the terminals from a parser.
	 */
	private static Object getTerminals(SilverCopperParser<?> parser) {
		List<Terminal> tokens = (List<Terminal>) parser.getTokens();
		return new Thunk<ConsCell>(() -> {
			List<NTerminalDescriptor> tds = tokens
				.stream()
				.map(Util::terminalToTerminalDescriptor)
				.collect(Collectors.toList());
			return ConsCellCollection.fromList(tds);
		});
	}

	/**
	 * Converts a common.Terminal to a Silver silver:core:TerminalDescriptor.
	 */
	private static NTerminalDescriptor terminalToTerminalDescriptor(Terminal t) {
        return new PterminalDescriptor(t.lexeme,
            convertStrings(Arrays.stream(t.getLexerClasses()).iterator()),
            Terminal.extractLocation(t),
            new StringCatter(t.getName()));
	}

	/**
	 * Like javainterop.ConsCellCollection.fromIterator, but also converts String to StringCatter.
	 */
	private static ConsCell convertStrings(Iterator<String> i) {
		if(!i.hasNext())
			return ConsCell.nil;
		return new ConsCell(new StringCatter(i.next()), convertStrings(i));
	}

	/**
	 * This is a "private" method for the Silver compiler to use to determine
	 * where it is installed. We can figure out how to generalize this later.
	 */
	public static StringCatter determineSilverHomePath(Class<?> clazz) {
		URI jarLocation;
		try {
			jarLocation = clazz.getProtectionDomain().getCodeSource().getLocation().toURI();
		} catch(Throwable t) {
			throw new RuntimeException("Failed to find install location of Silver runtime.", t);
		}
		// HOME/jars/file.jar to HOME
		File home = new File(jarLocation).getParentFile().getParentFile();
		return new StringCatter(home.getPath());
	}

	public static StringCatter getSilverVersion() {
		String path = determineSilverHomePath(Util.class).toString()+"/jars/silver.compiler.composed.Default.jar";
        try {
            JarInputStream file = new JarInputStream(new FileInputStream(path));
            return new StringCatter(file.getManifest().getMainAttributes().getValue(Name.IMPLEMENTATION_VERSION));
        } catch (Throwable t) {
            throw new RuntimeException("Failed to get Silver version.", t);
        }
    }
	
	public static ConsCell bitSetToList(BitSet b) {
		ConsCell result = ConsCell.nil;
		for (int i = b.nextSetBit(0); i >= 0; i = b.nextSetBit(i+1)) {
			result = new ConsCell(i, result);
		}
		return result;
	}
}
