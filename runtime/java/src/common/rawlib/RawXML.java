package common.rawlib;

import java.io.File;
import java.io.IOException;
import java.io.StringWriter;
import java.util.Iterator;
import java.util.Map;
import java.util.TreeMap;

import javax.xml.XMLConstants;
import javax.xml.namespace.NamespaceContext;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpression;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;

import silver.xml.ast.NXMLAttribute;
import silver.xml.ast.NXMLDocumentType;
import silver.xml.ast.NXMLNode;
import silver.xml.ast.NXMLNodeList;

import org.w3c.dom.Document;
import org.w3c.dom.DocumentType;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.w3c.dom.Text;
import org.xml.sax.SAXException;

import common.ConsCell;
import common.StringCatter;
import common.exceptions.SilverError;
import common.exceptions.SilverInternalError;
import common.exceptions.TraceException;
import common.javainterop.ConsCellCollection;
import silver.core.NPair;

public final class RawXML {

	private static DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
	private static DocumentBuilder parser;
	
	/**
	 * Ensure we've properly instantiated a parser object.
	 */
	private static final void ensureParserSetup() {
		// Create the parser, if we haven't already. Why do they create these things so complicated?
		if(parser == null) {
			try {
				dbFactory.setCoalescing(true); // Eliminate CDATA into text nodes...
				dbFactory.setIgnoringComments(true); // Eliminate comment nodes...
				//dbFactory.setIgnoringElementContentWhitespace(true); //REQUIRES VALIDATION MODE?
				dbFactory.setValidating(false); // Make sure we're not validating...
				dbFactory.setNamespaceAware(true); // But, apparently, we'd like to know about namespaces?
				
				// BRAIN DAMAGE OF THE HIGHEST ORDER
				dbFactory.setFeature("http://apache.org/xml/features/nonvalidating/load-external-dtd", false);
				
				parser = dbFactory.newDocumentBuilder();
			} catch(ParserConfigurationException pce) {
				throw new SilverInternalError("Unexpected error initializing XML parser", pce);
			}
		}
	}

	/**
	 * @param fn The filename of an XML file to convert to a Silver AST (Silver type String)
	 * @return The Silver AST of the XML file, wrapped in a ParseResult structure.
	 *   (Silver type silver:core:ParseResult&lt;silver:xml:ast:XMLDocument&gt;)
	 */
	public static final silver.core.NParseResult parseXMLFileN(final common.StringCatter fn) {
		
		ensureParserSetup();
		
		Document d;
		try {
			d = parser.parse(new File(fn.toString()));
		} catch (IOException e) {
			throw new TraceException("IO error while parsing xml file " + fn.toString(), e);
		} catch (SAXException e) {
			// Return the failure data structure, with the parse error.
			return new silver.core.PparseFailed(new common.StringCatter(e.toString()), null);
		}
		
		return new silver.core.PparseSucceeded(documentF2N(d), null);
		//  fmap documentF2n . parseXMLFileF  -- OH WAIT
	}
	
	/**
	 * @param fn The filename of an XML file (Silver type String)
	 * @return A parse result containing a direct reference to a Document.
	 *   (Silver type silver:core:ParseResult&lt;silver:xml:foreigntypes:XML_Document&gt;)
	 */
	public static final silver.core.NParseResult parseXMLFileF(final common.StringCatter fn) {

		ensureParserSetup();
		
		Document d;
		try {
			d = parser.parse(new File(fn.toString()));
		} catch (IOException e) {
			throw new TraceException("IO error while parsing xml file " + fn.toString(), e);
		} catch (SAXException e) {
			// Return the failure data structure, with the parse error.
			return new silver.core.PparseFailed(new common.StringCatter(e.toString()), null);
		}
		
		return new silver.core.PparseSucceeded(d, null);	
	}
	
	/**
	 * Convert a document of type Foreign DOM to Silver XML AST.
	 * 
	 * @param d A DOM Document (Silver type silver:xml:foreigntypes:XML_Document)
	 * @return An equivalent Silver AST type. (Silver type silver:xml:ast:XMLDocument)
	 */
	public static final silver.xml.ast.NXMLDocument documentF2N(org.w3c.dom.Document d) {
		final DocumentType dt = d.getDoctype();
		final NodeList nl = d.getChildNodes();
		
		silver.xml.ast.NXMLDocumentType sdt;
		
		if(dt != null) {
			sdt = new silver.xml.ast.PxmlDocumentType(
					new common.StringCatter(dt.getName()), 
					nodeListF2N(dt.getChildNodes())); 
		} else {
			sdt = new silver.xml.ast.PxmlNoDocumentType();
		}
		
		return new silver.xml.ast.PxmlDocument(sdt, nodeListF2N(nl));
	}
	
	/**
	 * Convert a document of type Silver XML AST to a Foreign DOM type
	 * 
	 * @param docAst Silver AST Document (Silver type silver:xml:ast:XMLDocument)
	 * @return An equivalent DOM document (Silver type silver:xml:foreigntypes:XML_Document)
	 */
	public static final Document documentN2F(silver.xml.ast.NXMLDocument docAst) {
		ensureParserSetup();
		
		Document docContext = parser.newDocument();
		
		deconvertXmlAstDocument(docAst, docContext);
		
		return docContext;
	}
	
	/**
	 * Produces a text document from a DOM tree
	 * 
	 * @param document DOM tree to unparse (Silver type silver:xml:foreigntypes:XML_Document)
	 * @return String output (Silver type String)
	 */
	public static final StringCatter documentF2String(Document document) {
		TransformerFactory tFactory = TransformerFactory.newInstance();
		Transformer transformer;
		try {
			transformer = tFactory.newTransformer();
		} catch (TransformerConfigurationException e1) {
			throw new RuntimeException(e1);
		}

		StringWriter sw = new StringWriter();
		
		DOMSource source = new DOMSource(document);
		StreamResult result = new StreamResult(sw);
		try {
			transformer.transform(source, result);
		} catch (TransformerException e) {
			throw new RuntimeException(e);
		}

		return new StringCatter(sw.toString());
	}

	/**
	 * @param document The Node or document to query
	 * @param querystring The XPath query to execute on this document
	 * @param namespace null, or a [(String, String)] namespace resolver info
	 * @return The foreign DOM response (Silver type silver:xml:foreigntypes:XML_NodeList)
	 */
	public static final NodeList xpathQueryNodeSet(Object document, String querystring, common.ConsCell namespace) {
		try {
			XPathFactory xpfactory = XPathFactory.newInstance();
			XPath xp = xpfactory.newXPath();
			if(namespace != null && !namespace.nil()) {
				xp.setNamespaceContext(new PairListNSContext(namespace));
			}
			XPathExpression xpe = xp.compile(querystring);
			
			return (NodeList)xpe.evaluate(document, XPathConstants.NODESET);
			
		} catch (XPathExpressionException e) {
			throw new TraceException("While evaluating XPath expression", e);
		}
	}
	
	/**
	 * @param document The Node or document to query
	 * @param querystring The XPath query to execute on this document
	 * @param namespace null, or a [(String, String)] namespace resolver info
	 * @return A string response (Silver type String)
	 */
	public static final StringCatter xpathQueryString(Object document, String querystring, common.ConsCell namespace) {
		try {
			XPathFactory xpfactory = XPathFactory.newInstance();
			XPath xp = xpfactory.newXPath();
			if(namespace != null && !namespace.nil()) {
				xp.setNamespaceContext(new PairListNSContext(namespace));
			}
			XPathExpression xpe = xp.compile(querystring);
			
			return new StringCatter((String)xpe.evaluate(document, XPathConstants.STRING));
			
		} catch (XPathExpressionException e) {
			throw new TraceException("While evaluating XPath expression", e);
		}
	}
	
	/**
	 * Convert a DOM NodeList to a silver one
	 * 
	 * @param nl a DOM NodeList (Silver type silver:xml:foreigntypes:XML_NodeList)
	 * @return a silver ast NodeList (Silver type silver:xml:ast:XMLNodeList)
	 */
	public static final silver.xml.ast.NXMLNodeList nodeListF2N(final NodeList nl) {
		
		silver.xml.ast.NXMLNodeList l = new silver.xml.ast.PxmlNodeListNil();
		
		for(int i = nl.getLength() - 1; i >= 0; i -- ) {
			final Node n = nl.item(i);
			
			switch(n.getNodeType()) {
			case Node.TEXT_NODE:
			case Node.CDATA_SECTION_NODE: // treating the same as text for now!
				// Convert the text data to Silver type
				common.StringCatter val = new common.StringCatter(n.getNodeValue());
				
				// Add this element to the list
				l = new silver.xml.ast.PxmlNodeListCons( new silver.xml.ast.PxmlNodeText(val), l);
				break;
			case Node.ELEMENT_NODE:
			case Node.ENTITY_NODE: // treating the same as an element for now!
				// Convert the name
				common.StringCatter name = new common.StringCatter(n.getNodeName());
				// Convert the attributes
				common.ConsCell/*silver.xml.ast.NXMLAttribute*/ attrs = attributesF2N(n.getAttributes());
				// Convert the children
				silver.xml.ast.NXMLNodeList children = nodeListF2N(n.getChildNodes());
				
				// Create the Node
				l = new silver.xml.ast.PxmlNodeListCons( new silver.xml.ast.PxmlNodeElement(name, attrs, children), l);
				break;
			case Node.COMMENT_NODE:
			case Node.DOCUMENT_TYPE_NODE: // for now: wtf?
				break; // ignoring comments!
			default:
				throw new SilverError("Unexpected type of XML node! " + n.getNodeType() + n.getNodeName() + n.toString());
			}
			
		}
		return l;
	}
	
	/**
	 * Convert a DOM Node List to a silver list of DOM nodes!
	 * 
	 * @param nl a DOM Node list (Silver type silver:xml:foreigntypes:XML_NodeList)
	 * @return a list of DOM Nodes (Silver type [silver:xml:foreigntypes:XML_Node])
	 */
	public static final common.ConsCell nodeListF2NPartial(final NodeList nl) {
		
		common.ConsCell l = common.ConsCell.nil;
		
		for(int i = nl.getLength() - 1; i >= 0; i -- ) {
			l = new common.ConsCell(nl.item(i), l);
		}
		
		return l;
	}
	
	/**
	 * Convert a DOM NamedNodeMap (attributes) to a list of silver attributes.
	 * 
	 * @param al DOM Attribute list
	 * @return silver ast attribute list (Silver type [silver:xml:ast:XMLAttribute])
	 */
	private static final common.ConsCell attributesF2N(final NamedNodeMap al) {
		
		common.ConsCell/*silver.xml.ast.NXMLAttribute*/ l = common.ConsCell.nil;
		
		for(int i = 0; i < al.getLength(); i++ ) {
			final Node n = al.item(i);
			final common.StringCatter key = new common.StringCatter(n.getNodeName());
			final common.StringCatter value = new common.StringCatter(n.getNodeValue());
			l = new common.ConsCell( new silver.xml.ast.PxmlAttribute(key, value), l);
		}
		
		return l;
	}
	
	private static final void deconvertXmlAstDocument(silver.xml.ast.NXMLDocument docAst, Document docContext) {
		silver.xml.ast.NXMLDocumentType dt = (NXMLDocumentType) docAst.getChild(0);
		silver.xml.ast.NXMLNodeList nl = (NXMLNodeList) docAst.getChild(1);
		mutateDocumentType(dt, docContext);
		mutateXmlAstNodeList(nl, docContext, docContext);
	}
	private static final void mutateDocumentType(silver.xml.ast.NXMLDocumentType docTypeAst, Document docContext) {
		if(docTypeAst instanceof silver.xml.ast.PxmlNoDocumentType) {
			// do nothing!
		} else if(docTypeAst instanceof silver.xml.ast.PxmlDocumentType) {
			// TODO: oh, bother. how?
		} else {
			throw new SilverInternalError("Unknown type in XML AST during unparse of doctype...");
		}
	}
	private static final void mutateXmlAstNodeList(silver.xml.ast.NXMLNodeList docNLAst, Node nodeContext, Document docContext) {
		NXMLNodeList current = docNLAst;
		while(current instanceof silver.xml.ast.PxmlNodeListCons) {
			Node n = deconvertXmlAstNode((NXMLNode)current.getChild(0), docContext);
			nodeContext.appendChild(n);
			current = (NXMLNodeList) current.getChild(1);
		}
	}
	private static final Node deconvertXmlAstNode(silver.xml.ast.NXMLNode docNodeAst, Document docContext) {
		if(docNodeAst instanceof silver.xml.ast.PxmlNodeElement) {
			StringCatter sc = (StringCatter) docNodeAst.getChild(0);
			common.ConsCell at = (ConsCell) docNodeAst.getChild(1);
			NXMLNodeList nl = (NXMLNodeList) docNodeAst.getChild(2);
			
			Element n = docContext.createElement(sc.toString());
			mutateAttributes(at, n, docContext);
			mutateXmlAstNodeList(nl, n, docContext);
			return n;
		}
		if(docNodeAst instanceof silver.xml.ast.PxmlNodeText) {
			StringCatter sc = (StringCatter) docNodeAst.getChild(0);
			
			Text t = docContext.createTextNode(sc.toString());
			return t;
		}
		throw new SilverInternalError("Unknown type in XML AST during unparse of node...");
		
	}
	private static final void mutateAttributes(common.ConsCell/*silver.xml.ast.NXMLAttribute*/ docAttrsAst, Element elem, Document docContext) {
		common.ConsCell current = docAttrsAst;
		
		while(!current.nil()) {
			NXMLAttribute at = (NXMLAttribute) current.head();
			elem.setAttribute(at.getChild(0).toString(), at.getChild(1).toString());
			current = current.tail();
		}
	}
	
	public static class PairListNSContext implements NamespaceContext {

		private final Map<String, String> resolver;
		
		/**
		 * Creates a namespace context resolver from a [(String, String)] Silver type.
		 * 
		 * @param current a key-value pair of prefixes to namespace URIs
		 */
		public PairListNSContext(common.ConsCell current) {
			resolver = new TreeMap<String, String>();
			
			for(NPair elem : new ConsCellCollection<NPair>(current)) {
				String fst = elem.getAnno_silver_core_fst().toString();
				String snd = elem.getAnno_silver_core_snd().toString();
				
				resolver.put(fst, snd);
			}
		}
		
		@Override
		public String getNamespaceURI(String prefix) {
			
			if(prefix == null)
				throw new IllegalArgumentException();
			
			String result = resolver.get(prefix);
			if(result != null)
				return result;
			
			if(prefix.equals(XMLConstants.XML_NS_PREFIX))
				return XMLConstants.XML_NS_URI;
			
			if(prefix.equals(XMLConstants.XMLNS_ATTRIBUTE))
				return XMLConstants.XMLNS_ATTRIBUTE_NS_URI;
			
			return XMLConstants.NULL_NS_URI;
		}

		@Override
		public String getPrefix(String namespaceURI) {
			throw new UnsupportedOperationException();

		}

		@Override
		public Iterator<String> getPrefixes(String namespaceURI) {
			throw new UnsupportedOperationException();
		}

	}

}
