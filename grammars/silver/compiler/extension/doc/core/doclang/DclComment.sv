grammar silver:compiler:extension:doc:core:doclang;
imports silver:compiler:extension:doc:core;
imports silver:langutil;

-- Comment is sequence of blocks
-- Blocks start with a newline or a @param/@return/@prodattr/@forward/...
-- Initial block is a 'normal' block even if no newline (but is other type if has @tag)

synthesized attribute blocks::[DclCommentBlock];

inherited attribute paramNames::[String] occurs on DclComment;
inherited attribute isForWhat::String occurs on DclComment;

nonterminal DclComment layout {} with docEnv, body, errors, location, downDocConfig, upDocConfig;

nonterminal DclCommentBlocks layout {} with blocks, location;
nonterminal DclCommentStrictBlocks layout {} with blocks, location;
nonterminal DclCommentBlock layout {} with body, location;

nonterminal ConfigValue layout {} with location;

nonterminal DclCommentLines layout {} with body, location;

nonterminal DclCommentParts layout {} with body, location;
nonterminal DclCommentPart layout {} with body, location;

parser parseDocComment::DclComment {
	silver:compiler:extension:doc:core:doclang;
}

concrete production normalDclComment
top::DclComment ::= InitialIgnore_t blocks::DclCommentBlocks FinalIgnore_t
{
	local paramBlocks::[Pair<String DclCommentBlock>] =
		flatMap((\x::DclCommentBlock ->
			         case x of
			         | paramBlock(_, _, id, _, _) -> [pair(id.lexeme, x)]
			         | _ -> [] end),
		        blocks.blocks);

	local paramBlocksSorted::[DclCommentBlock] =
		map((\x::Pair<String DclCommentBlock> -> x.snd),
			sortBy((\x::Pair<String DclCommentBlock> y::Pair<String DclCommentBlock> ->
				positionOf(stringEq, x.fst, top.paramNames) < positionOf(stringEq, y.fst, top.paramNames)),
					paramBlocks));

	local warningBlocks::[DclCommentBlock] =
		flatMap((\x::DclCommentBlock ->
			         case x of
			         | warningBlock(_, _, _) -> [x]
			         | _ -> [] end),
		        blocks.blocks);

	local returnBlocks::[DclCommentBlock] =
		flatMap((\x::DclCommentBlock ->
			         case x of
			         | returnBlock(_, _, _) -> [x]
			         | _ -> [] end),
		        blocks.blocks);

	local forwardBlocks::[DclCommentBlock] =
		flatMap((\x::DclCommentBlock ->
			         case x of
			         | forwardBlock(_, _, _) -> [x]
			         | _ -> [] end),
		        blocks.blocks);

	local prodAttrBlocks::[Pair<String DclCommentBlock>] =
		flatMap((\x::DclCommentBlock ->
			         case x of
			         | prodattrBlock(_, _, id, _, _) -> [pair(id.lexeme, x)]
			         | _ -> [] end),
		        blocks.blocks);

	local prodAttrBlocksSorted::[DclCommentBlock] =
		map((\x::Pair<String DclCommentBlock> -> x.snd),
			sortBy((\x::Pair<String DclCommentBlock> y::Pair<String DclCommentBlock> ->
				compareString(x.fst, y.fst) < 0), prodAttrBlocks));

	local commentBlocks::[DclCommentBlock] =
		flatMap((\x::DclCommentBlock ->
			         case x of
			         | commentBlock(_, _) -> [x]
			         | _ -> [] end),
		        blocks.blocks);

	local configArgs::[Pair<String ConfigValue>] =
		flatMap((\x::DclCommentBlock ->
			         case x of
			         | configBlock(_, _, name, _, _, _, value) -> [pair(name.lexeme, value)]
			         | _ -> [] end),
		        blocks.blocks);

	local errs::[String] =
		(if (length(paramBlocks) != length(top.paramNames)) && (length(paramBlocks) != 0)
		then ["Arity doesn't match in doc-comment"]
		else checkParams(top.paramNames, map(fst, paramBlocks))) ++
		(if length(forwardBlocks) > 1 then ["More than one forward block in doc-comment"] else []) ++
		(if length(returnBlocks) > 1 then ["More than one return block in doc-comment"] else []) ++
		(if length(returnBlocks) > 0 && top.isForWhat!="function" then ["@return in non-function doc-comment"] else []) ++
		(if length(forwardBlocks) > 0 && top.isForWhat!="production" then ["@forward in non-production doc-comment"] else []) ++
		(if length(prodAttrBlocks) > 0 && !(top.isForWhat=="function" || top.isForWhat == "production") then ["@prodattr in non function-or-production doc comment"] else []) ++
		(if length(paramBlocks) > 0 && !(top.isForWhat=="function" || top.isForWhat == "production") then ["@param in non function-or-production doc comment"] else []) ++
		confResult.fst;

	top.errors := map((\x::String -> wrn(top.location, x)), errs);

	top.body =
		implode("\n\n", map((.body),
			warningBlocks ++
			paramBlocksSorted ++ 
			prodAttrBlocksSorted ++
			returnBlocks ++
			forwardBlocks ++
			commentBlocks))
		++ "\n\n\n\n" ++ hackUnparse(configArgs) ++ "\n\n\n\n" ++ hackUnparse(confResult.snd);

	local confResult::Pair<[String] DocConfiguration> = processConfigOptions([], configArgs, top.downDocConfig);
	top.upDocConfig = confResult.snd;

}

function processConfigOptions
Pair<[String] DocConfiguration> ::= alreadyErrs::[String] args::[Pair<String ConfigValue>] conf::DocConfiguration
{
	local arg::Pair<String ConfigValue> =
		case args of
		| a::_ -> a
		end;

	local err::[String] =
		case arg of
		| pair("split", v) -> if !v.asBool.isJust then ["@config split takes 'on'/'off'/'true'/'false'"] else []
		| pair("weight", v) -> if !v.asInteger.isJust then ["@config weight takes an integer"] else []
		| pair("title", v) -> if !v.asString.isJust then ["@config title takes a string in quotes"] else []
		| pair("collapseChildren", v) -> if !v.asBool.isJust then ["@config collapseChildren takes 'on'/'off'/'true'/'false'"] else []
		| pair("noDocs", v) -> if !v.asBool.isJust then ["@config noDocs takes 'on'/'off'/'true'/'false'"] else []
		| pair(k, _) -> ["Unknown @config directive '"++k++"'"]
		end;

	local boundConf::DocConfiguration =
		case arg of
		| pair("split", v) -> splitConfig(v.asBool.fromJust, conf)
		| pair("weight", v) -> weightConfig(v.asInteger.fromJust, conf)
		| pair("title", v) -> titleConfig(v.asString.fromJust, conf)
		| pair("collapseChildren", v) -> collapseConfig(v.asBool.fromJust, conf)
		| pair("noDocs", v) -> noDocsConfig(v.asBool.fromJust, conf)
		end;

	return case args of
		   | [] -> pair(alreadyErrs, conf)
		   | _::r when length(err)!=0 -> processConfigOptions(err++alreadyErrs, r, conf)
		   | _::r -> processConfigOptions(alreadyErrs, r, boundConf)
		   end;
}

function checkParams
[String] ::= p::[String] b::[String]
{
	return case p, b of
		   | pn::p_, bn::b_ when pn==bn -> checkParams(p_, b_)
		   | pn::p_, bn::b_ -> s"Param '${pn}' in wrong order in doc-comment" :: checkParams(p_, b_)
		   | _, _ -> []
		   end;
}

abstract production errorDclComment
top::DclComment ::= content::String error::ParseError
{
	top.body = s"""(Comment parse error, raw content)
```
${content}
```
""";

	local errorMessage::Message =
        case error of
        | syntaxError(_, location, expected, matched) ->
            let printLoc::Location = childParserLoc(top.location, location, 0, 0, 0, 0)
            in wrn(printLoc,
                s"Doc Comment Parse Error at ${printLoc.filename} line ${toString(printLoc.line)} column ${toString(printLoc.column)}"
                ++ s"\n\tExpected a token of one of the following types: [${implode(", ", expected)}]"
                ++ s"\n\tInput currently matches: [${implode(", ", matched)}]") end
        | unknownParseError(s, f) -> wrn(top.location, s"Doc comment unknown parse error: unknownParseError(${s}, ${f})")
        end;

    top.errors := [errorMessage];

    top.upDocConfig = top.downDocConfig;
}




concrete production initialCommentBlocks
top::DclCommentBlocks ::= block::DclCommentLines blocks::DclCommentStrictBlocks
{
	top.blocks = commentBlock(terminal(EmptyLines_t, ""), block, location=top.location) :: blocks.blocks;
}

concrete production passThruCommentBlocks
top::DclCommentBlocks ::= blocks::DclCommentStrictBlocks
{
	top.blocks = blocks.blocks;
}



concrete production nilCommentBlocks
top::DclCommentStrictBlocks ::=
{
	top.blocks = [];
}

concrete production consCommentBlocks
top::DclCommentStrictBlocks ::= block::DclCommentBlock rest::DclCommentStrictBlocks  
{
	top.blocks = block :: rest.blocks;
}




concrete production commentBlock
top::DclCommentBlock ::= EmptyLines_t content::DclCommentLines
{
	top.body = content.body;
}

concrete production paramBlock
top::DclCommentBlock ::= Param_t Whitespace_t id::Id_t Whitespace_t content::DclCommentLines
{
	top.body = "Argument `" ++ id.lexeme ++ "`: " ++ content.body;
}

concrete production prodattrBlock
top::DclCommentBlock ::= Prodattr_t Whitespace_t id::Id_t Whitespace_t content::DclCommentLines
{
	top.body = "Production Attribute `" ++ id.lexeme ++ "`: " ++ content.body;
}

concrete production returnBlock
top::DclCommentBlock ::= Return_t Whitespace_t content::DclCommentLines
{
	top.body = "Return: " ++ content.body;
}

concrete production forwardBlock
top::DclCommentBlock ::= Forward_t Whitespace_t content::DclCommentLines
{
	top.body = "Forward: " ++ content.body;
}

concrete production warningBlock
top::DclCommentBlock ::= Warning_t Whitespace_t content::DclCommentLines
{
	top.body = "WARNING: " ++ content.body;
}

concrete production configBlock
top::DclCommentBlock ::= Config_t Whitespace_t param::Id_t Whitespace_t Equals_t Whitespace_t value::ConfigValue
{
	top.body = "@config " ++ param.lexeme ++ " = " ++ hackUnparse(value);
}

synthesized attribute asBool::Maybe<Boolean> occurs on ConfigValue;
synthesized attribute asString::Maybe<String> occurs on ConfigValue;
synthesized attribute asInteger::Maybe<Integer> occurs on ConfigValue;

concrete production kwdValue
top::ConfigValue ::= v::ConfigValueKeyword_t
{
	top.asBool = just(v.lexeme=="on" || v.lexeme=="true");
	top.asString = nothing();
	top.asInteger = nothing();
}

concrete production stringValue
top::ConfigValue ::= v::ConfigValueString_t
{
	top.asBool = nothing();
	top.asString = just(v.lexeme);
	top.asInteger = nothing();
}

concrete production integerValue
top::ConfigValue ::= v::ConfigValueInt_t
{
	top.asBool = nothing();
	top.asString = nothing();
	top.asInteger = just(toInt(v.lexeme));
}

concrete production lastCommentLines
top::DclCommentLines ::= body::DclCommentParts
{
	top.body = body.body;
}

concrete production consCommentLines
top::DclCommentLines ::= body::DclCommentParts Newline_t rest::DclCommentLines
{
	top.body = body.body ++ "\n" ++ rest.body;
}





concrete production firstCommentParts
top::DclCommentParts ::= part::DclCommentPart
{
	top.body = part.body;
}

concrete production snocCommentParts
top::DclCommentParts ::= rest::DclCommentParts part::DclCommentPart
{
	top.body = rest.body ++ part.body;
}


concrete production textCommentPart
top::DclCommentPart ::= part::CommentContent_t
{
	top.body = part.lexeme;
}

concrete production linkCommentPart
top::DclCommentPart ::= '@link' '[' id::Id_t ']'
{
	top.body = s"[${id.lexeme}](${id.lexeme})";
}
concrete production fileLinkCommentPart
top::DclCommentPart ::= '@file' '[' path::Path_t ']'
{
	top.body = s"[${path.lexeme}](github -> ${path.lexeme})";
}

concrete production escapedAtPart
top::DclCommentPart ::= '@@'
{
	top.body = "@";
}


terminal InitialIgnore_t /@+\{\- *\-* */;
terminal FinalIgnore_t /[\- \r\n]*\-\}/ dominates {CommentContent_t};

terminal EmptyLines_t /\n( *\-* *\r?\n)+ *\-* */;
terminal Newline_t /\r?\n *\-* */;

terminal CommentContent_t /([^@\r\n\-]|\-[^\r\n}])+/;

terminal EscapedAt_t '@@';

terminal Param_t /( *\-* *\r?\n)* *\-* *@(param|child)/ lexer classes {BLOCK_KWD};
terminal Return_t /( *\-* *\r?\n)* *\-* *@return/ lexer classes {BLOCK_KWD};
terminal Forward_t /( *\-* *\r?\n)* *\-* *@forward/ lexer classes {BLOCK_KWD};
terminal Prodattr_t /( *\-* *\r?\n)* *\-* *@prodattr/ lexer classes {BLOCK_KWD};
terminal Warning_t /( *\-* *\r?\n)* *\-* *@warning/ lexer classes {BLOCK_KWD};
terminal Config_t /( *\-* *\r?\n)* *\-* *@config/ lexer classes {BLOCK_KWD};

terminal ConfigValueKeyword_t /(on|off|true|false)/;
terminal ConfigValueString_t /[\"]([^\r\n\"\\]|[\\][\"]|[\\][\\]|[\\]b|[\\]n|[\\]r|[\\]f|[\\]t)*[\"]/;
terminal ConfigValueInt_t /[0-9]+/;

terminal Whitespace_t /[\t ]*/;
terminal Equals_t /=?/;

terminal Link_t '@link';
terminal FileLink_t '@file';
terminal OpenBracket_t '[';
terminal CloseBracket_t ']';
terminal Id_t /[a-zA-Z][a-zA-Z0-9_]*/;
terminal Path_t /[a-zA-Z0-9_\-\/\.]+/;

lexer class BLOCK_KWD dominates CommentContent_t;