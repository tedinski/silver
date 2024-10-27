import silver:compiler:definition:origins;
import silver:util:cmdargs only CmdArgs;
import silver:compiler:driver;

-- Information on how to compute origins for stuff constructed/modified in different block contexts
-- How do we get an OriginContext representing this?
synthesized attribute contextRef :: String occurs on ContextOriginInfoSource;

-- Given a string holding java code to produce a NOriginRule[] array, produce a string holding java code
--  to produce a OriginContext for this context adding those rules (faster than getting contextRef and
--  adding rules)
synthesized attribute contextRefAddingRules :: (String ::= String) occurs on ContextOriginInfoSource;

-- Is this context something that's `interesting` (= er flag = isNewConstruction) all the time?
-- Only `false` for cases where we are in a production body
synthesized attribute alwaysConsideredInteresting :: Boolean occurs on ContextOriginInfoSource;

aspect production useContextLhsAndRules
top::ContextOriginInfoSource ::=
{
  top.contextRef = "new common.OriginContext(context.getNode(), null)";
  top.contextRefAddingRules = (\x::String -> s"new common.OriginContext(context.getNode(), ${x})");
  top.alwaysConsideredInteresting = false;
}

aspect production useRuntimePassedInfo
top::ContextOriginInfoSource ::=
{
  top.contextRef = "originCtx";
  top.contextRefAddingRules = (\x::String -> s"new common.OriginContext(${top.contextRef}, ${x})");
  top.alwaysConsideredInteresting = true;
}

aspect production useBogusInfo
top::ContextOriginInfoSource ::= name::String
{
  top.contextRef = "common.OriginContext."++name;
  top.contextRefAddingRules = (\x::String -> s"new common.OriginContext(${top.contextRef}, ${x})");
  top.alwaysConsideredInteresting = true;
}

function makeOriginContextRef
String ::= top::Decorated Expr --need .frame anno
{
  local rulesTrans :: [String] = (if top.config.tracingOrigins then [locRule] else []) ++ map((.translation), top.originRules);
  local loc :: Location = getParsedOriginLocationOrFallback(top);
  local locRule :: String = s"new silver.core.PtraceNote(new common.StringCatter(\"${top.grammarName}:${escapeString(loc.unparse)}\"))";

  return if top.config.noOrigins then "null" 
         else if length(rulesTrans)==0 
              then top.frame.originsContextSource.contextRef
              else top.frame.originsContextSource.contextRefAddingRules(s"new silver.core.NOriginNote[]{${implode(", ", rulesTrans)}}");
}

global newConstructionOriginUsingCtxRef :: String =
	"originCtx.makeNewConstructionOrigin(true)";

function makeNewConstructionOrigin
[String] ::= top::Decorated Expr  inInteresting::Boolean  --need .frame anno
{
  nondecorated local ty::Type = top.finalType.outputType;
  local interesting :: Boolean = top.frame.originsContextSource.alwaysConsideredInteresting || !top.isRoot || inInteresting;

  return if ty.isTracked
         then [makeOriginContextRef(top)++s".makeNewConstructionOrigin(${if interesting then "true" else "false"})"]
         else [];
}

function wrapAccessWithOT
String ::= top::Decorated Expr expr::String
{
  local ty :: Type = top.finalType;

  -- The complexity here is needed because of silver generics. A nonterminal like Maybe<a> is monomorphized in such a way
  -- that the parameter type is Object. As a result we can't tell, when it's possible that we are doing something on a type
  -- that may be a parameter, if it will want OI or not (or for that matter, if it's even a subclass of Node or if it's a
  -- boxed primitive). As a result our paths are:
  --  - directCopy is the fastpath for things we know want OI
  --  - noop is the "fastpath" where we do nothing, either because we know it's a Node and it dosen't want OI, or because
  --     we know it's a primitive
  --  - polyCopy is the slowpath that uses java instanceof to check if it's tracked, and then send OI if it is

  local polyCopy   :: String = s"${makeOriginContextRef(top)}.attrAccessCopyPoly(${expr})";
  local directCopy :: String = s"${makeOriginContextRef(top)}.attrAccessCopy(${expr})";
  local noop       :: String = expr;

  local impl :: String = if ty.transType == "Object" then polyCopy else
          (if ty.isTracked then directCopy else noop);

  return if (top.config.noRedex || top.config.noOrigins) then noop else impl;
  -- The extra (common.Node) cast in the non-generic non-primitive case is sometimes required for reasons I don't fully understand.

}
