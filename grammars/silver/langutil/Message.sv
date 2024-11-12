grammar silver:langutil;

@@{-
   - @config fileSplit
   -
   - ## A Universal error/warning message data structure
   -}

@{--
 - A Message represents a compiler output message (error/warning)
 -}
closed tracked data nonterminal Message with message, where, noLocOutput, output, severity;

@{--
 - The location of an error message.
 -}
synthesized attribute where :: Location;

@{--
 - The contents of the error message.
 -}
synthesized attribute message :: String;

@{--
 - A recommended way to turn this message into console output with location info.
 -}
synthesized attribute output :: String;

@{--
 - A recommended way to turn this message into console output without location info.
 -}
synthesized attribute noLocOutput :: String;

@{--
 - A convention for determining message severity.
 - err=2, wrn=1, info=0
 - TODO: Consider making this a custom datatype.
 -}
synthesized attribute severity :: Integer;

aspect default production
top::Message ::=
{
  top.noLocOutput =
    case top.severity of
    | 0 -> "info"
    | 1 -> "warning"
    | _ -> "error"
    end ++ ": " ++ top.message;
  top.output = s"${top.where.unparse}: ${top.noLocOutput}";
}

@{--
 - A error that should halt compilation before translation proceeds on the 
 - compilation unit the error occurs in.
 -}
abstract production err
top::Message ::= l::Location m::String
{
  top.where = l;
  top.message = m;
  top.severity = 2;
}

fun errFromOrigin Message ::= a::a m::String = err(getParsedOriginLocationOrFallback(a), m);

@{--
 - A warning that is not required to halt compilation before translation
 - proceeds on the compilation unit the warning occurs in.
 -}
abstract production wrn
top::Message ::= l::Location m::String
{
  top.where = l;
  top.message = m;
  top.severity = 1;
}

fun wrnFromOrigin Message ::= a::a m::String = wrn(getParsedOriginLocationOrFallback(a), m);

@{--
 - An informational message that does not halt compilation, but is usually
 - attached to an error or warning.
 -}
abstract production info
top::Message ::= l::Location m::String
{
  top.where = l;
  top.message = m;
  top.severity = 0;
}

fun infoFromOrigin Message ::= a::a m::String = info(getParsedOriginLocationOrFallback(a), m);

@{--
 - A group of messages.
 -}
abstract production nested
top::Message ::= l::Location m::String others::[Message]
{
  top.where = l;
  local chain::[OriginInfo] = getOriginInfoChain(top);
  top.message =
    if null(chain) || originatesInExt(tail(chain)).isJust
    -- If the message originates in extension-generated code,
    -- then the nested messages likely do as well.
    -- Suppress the origins errors from nested messages to avoid making diagnostics unreadable.
    then s"${m}\n${messagesToStringNoOriginsCheck(others)}"
    else s"${m}\n${messagesToString(others)}";
  top.noLocOutput = s"${top.message}\n";
  top.severity = foldr(max, 0, map((.severity), others));
}

-- Users can extend Message with more messages (e.g. dbg) as they desire
-- map, filter, etc should all be quite useful on messages

@{--
 - Determines if a list has any errors (or, optionally, warnings, too)
 -}
function containsErrors
Boolean ::= l::[Message] wError::Boolean
{
  local errSeverity::Integer = if wError then 1 else 2;
  return any(map(\ m::Message -> m.severity >= errSeverity, l));
}

@{--
 - Show a message as a string, specially reporting undesired errors from extension-generated code.
 -}
function showMessage
String ::= m::Message
{
  local chain::[OriginInfo] = getOriginInfoChain(m);
  local fromExt::Maybe<String> =
    -- The first item in the chain is the message itself;
    -- we don't want to complain about messages raised directly in extension productions as "extension generated".
    if null(chain) then nothing() else originatesInExt(tail(chain));
  local originsSource::Maybe<Location> = getParsedOriginLocationFromChain(chain);
  local fromExtMessage::String =
    "INTERNAL ERROR: The following error message originated in extension-generated code." ++
    "\nThis is probably indicative of a bug in the extension as opposed to your code." ++
    "\nThe offending extension was: '" ++ fromExt.fromJust ++ "' - please report this to it's developers." ++
    (if originsSource.isJust
     then "\nOrigins reports the following source location: " ++ originsSource.fromJust.unparse ++ "."
     else "\nOrigins chain terminates without location.") ++
    "\nThe error was: " ++ m.noLocOutput ++ "." ++ -- We do not expect the location to be useful/correct
    "\nOrigins chain follows:" ++
    "\n" ++ showOriginInfoChain(m) ++
    "\n\n";


  return if fromExt.isJust
         then fromExtMessage
         else m.output;
}

@{--
 - Returns a list of strings, ready to be printed to the command line.
 -}
fun messagesToString String ::= msgs::[Message] =
  implode("\n", map(showMessage, sortBy(messageLte, msgs)));

@{--
 - Returns a list of strings, without doing the check for an origin in extension-generated code.
 - This is useful for pretty-printing error productions to avoid a circularity.
 -}
fun messagesToStringNoOriginsCheck String ::= msgs::[Message] =
  implode("\n", map((.output), sortBy(messageLte, msgs)));

-- for use with sortBy
-- not an instance of Eq/Ord for now, does it really make sense to compare messages for equality?
fun messageLte Boolean ::= m1::Message m2::Message = m1.where <= m2.where;

