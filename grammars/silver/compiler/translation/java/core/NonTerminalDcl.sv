grammar silver:compiler:translation:java:core;

aspect production nonterminalDcl
top::AGDcl ::= quals::NTDeclQualifiers 'nonterminal' id::Name tl::BracketedOptTypeExprs nm::NonterminalModifiers ';'
{
  local className :: String = "N" ++ id.name;
  
  local inhVar :: String = "count_inh__ON__" ++ id.name;
  local synVar :: String = "count_syn__ON__" ++ id.name;
  
  nondecorated local ntty::Type = nonterminalType(fName, map((.kindrep), tl.types), quals.data, isThisTracked);
  local myAnnos :: [NamedSignatureElement] =
    annotationsForNonterminal(ntty, top.env);

  local commaIfAnnos :: String = if length(myAnnos)!=0 then "," else "";
  local wantsTracking :: Boolean = ntty.isTracked;

  top.initProd := s"\t\tcommon.RTTIManager.registerNonterminal(${className}.nonterminalton);\n\n";
  top.initWeaving := s"""
	public static int ${inhVar} = 0;
	public static int ${synVar} = 0;""";

  local interfaces::[String] =
    map(makeAnnoName, map((.elementName), myAnnos)) ++
	if wantsTracking then ["common.Tracked"] else [];
  
  top.genFilesUnescapedUp := [id.name];
  top.genFiles := [(className ++ ".java", s"""
package ${makeName(top.grammarName)};

import java.util.*;
import silver.core.*;

public abstract class ${className} extends ${if quals.data then "common.DataNode" else "common.Node"} ${
  (if null(interfaces) then "" else 
    " implements " ++ implode(", ", interfaces)
  )} {

	public static final int num_inh_attrs = Init.${inhVar};
	public static final int num_syn_attrs = Init.${synVar};

	public static final String[] occurs_inh = new String[num_inh_attrs];
	public static final String[] occurs_syn = new String[num_syn_attrs];

	public static final common.Lazy[] defaultSynthesizedAttributes = new common.Lazy[num_syn_attrs];

	protected ${className}(${implode(", ",
			(if wantsTracking then ["final NOriginInfo origin"] else []) ++
			(if quals.data then [] else ["final boolean isUnique"]) ++
			map((.annoSigElem), myAnnos))}) {
${if quals.data then "" else "		super(isUnique);"}
		${if wantsTracking then "this.origin = origin;" else ""}
${implode("", map(makeAnnoAssign, myAnnos))}
	}

${implode("", map((.annoDeclElem), myAnnos))}

	@Override
	public final String[] getAnnoNames() {
		return new String[]{${implode(", ", map((.annoNameElem), myAnnos))}};
	}
	
	@Override
	public final Object getAnno(final String name) {
		${concat(map((.annoLookupElem), myAnnos))}{
			throw new common.exceptions.SilverInternalError("Invalid annotation " + name);
		}
	}

	@Override
	public final int getNumberOfSynAttrs() {
		return num_syn_attrs;
	}

	@Override
	public final common.Lazy getDefaultSynthesized(final int index) {
		return defaultSynthesizedAttributes[index];
	}
	
	@Override
	public final String getNameOfSynAttr(final int index) {
		return occurs_syn[index];
	}
${if quals.data then "" else s"""
	@Override
	public final int getNumberOfInhAttrs() {
		return num_inh_attrs;
	}

	@Override
	public final String getNameOfInhAttr(final int index) {
		return occurs_inh[index];
	}

	public static final class DecorationSiteWrapper extends ${className} {
		private common.DecoratedNode ref;

		public DecorationSiteWrapper(${implode(", ",
			(if wantsTracking then ["final NOriginInfo origin"] else []) ++
			["final common.DecoratedNode ref"])}) {
			super(${implode(", ",
			  (if wantsTracking then ["origin"] else []) ++
			  "true" ::
			  map(\ anno::NamedSignatureElement -> s"((${className})ref.getNode()).${anno.annoAccessorElem}", myAnnos)
			)});
			this.ref = ref;
		}

		@Override
		public common.DecoratedNode decorate(final common.DecoratedNode parent, final common.Lazy[] inhs, final common.Lazy decSite) {
			return ref.decorate(parent, inhs, decSite);
		}

		@Override
		public common.DecoratedNode decorate(final common.DecoratedNode parent, final common.Lazy[] inhs, final common.DecoratedNode fwdParent, final boolean prodFwrd) {
			return ref.decorate(parent, inhs, fwdParent, prodFwrd);
		}

		// Accessors used in reflection and debugging.
		// These need to dispatch to the ref Node.
		@Override
		public common.TypeRep getType() {
			return ref.getNode().getType();
		}

		@Override
		public String getName() {
			return ref.getNode().getName();
		}

		@Override
		public int getNumberOfChildren() {
			return ref.getNode().getNumberOfChildren();
		}

		@Override
		public boolean isChildDecorable(final int child) {
			return ref.getNode().isChildDecorable(child);
		}

		@Override
		public Object getChild(final int child) {
			return ref.getNode().getChild(child);
		}

		@Override
		public Object getChildLazy(final int child) {
			return ref.getNode().getChildLazy(child);
		}

		@Override
		public common.RTTIManager.Prodleton<? extends common.Node> getProdleton() {
			return ref.getNode().getProdleton();
		}

		// Accessors used only by DecoratedNode.
		// This should never happen.
		@Override
		public common.Lazy getChildDecSite(final int child) {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public common.Lazy[] getChildInheritedAttributes(final int index) {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public int getNumberOfLocalAttrs() {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public boolean isLocalDecorable(final int child) {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public String getNameOfLocalAttr(final int index) {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public common.Lazy getLocal(final int index) {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public common.Lazy getLocalDecSite(final int index) {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public boolean getLocalIsForward(final int index) {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public common.Lazy[] getLocalInheritedAttributes(final int index) {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public boolean hasForward() {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public common.Node evalForward(final common.DecoratedNode context) {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public common.Node evalUndecorate(final common.DecoratedNode context) {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public common.Lazy[] getForwardInheritedAttributes() {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		@Override
		public common.Lazy getSynthesized(final int index) {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should never be directly decorated!");
		}

		${if wantsTracking then s"""
		@Override
		public ${className} duplicate(common.Node redex, common.ConsCell notes) {
			throw new common.exceptions.SilverInternalError("Decoration site wrapper node should not exist in tree after undecoration!\n");
		}

		@Override
		public ${className} updateOriginInfo(silver.core.NOriginInfo oi) {
			return new DecorationSiteWrapper(oi, ref);
		}
""" else ""}
	}"""}

	public static final common.RTTIManager.Nonterminalton<${className}> nonterminalton = new Nonterminalton();

  public static final class Nonterminalton extends common.RTTIManager.Nonterminalton<${className}> {
      public String getName(){ return "${top.grammarName}:${id.name}"; }
  }

	${otImpl}
}
""")];

  local otImpl::String = if wantsTracking then s"""
  	protected final silver.core.NOriginInfo origin;

	@Override
	public final silver.core.NOriginInfo getOrigin() {
		return this.origin;
	}
""" else "";

}
