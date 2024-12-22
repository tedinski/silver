grammar silver:core;

instance Length String {
  length = stringLength;
}

@{--
 - Compute the length of a string.
 -
 - @param s The string to compute the length of.
 - @return  The length of the string.
 -}
function stringLength
Integer ::= s::String
{
  return error("foreign function");
} foreign {
  "java": return "Integer.valueOf(%s%.length())";
}

@{--
 - Fold a list of strings into one string, by interspersing a separator.
 -
 - @param sep  The separator to place between each string.
 - @param lst  The list of string to collapse.
 - @return  The combined string.
 -}
fun implode String ::= sep::String lst::[String] =
  if null(lst)
  then ""
  else head(lst) ++ if null(tail(lst))
                    then ""
                    else sep ++ implode(sep, tail(lst));

@{--
 - Split a string into a list of strings by a separator.  If the separtor
 - is the empty string then the string is split into single character strings.
 -
 - @param sep  The separator between each of the resulting strings.
 - @param str  The original string.
 - @return  The list of strings separated by sep in the original string.
 -}
fun explode [String] ::= sep::String str::String =
  if sep=="" then explodeSingle(str)
  else if str == "" then []
  else explodeNormal(sep, str);
function explodeNormal -- do not use
[String] ::= sep::String str::String
{
  local attribute i :: Integer;
  i = indexOf(sep, str);

  return if i == -1
         then [str]
         else substring(0, i, str) ::
              explodeNormal(sep, substring(i+length(sep), length(str), str));
}
fun explodeSingle [String] ::= str::String =
  if length(str) == 0
  then []
  else substring(0,1,str) ::
       explodeSingle (substring(1,length(str),str));

@{--
 - Find the index of a needle in the haystack.  (Indices are 0-based.)
 -
 - @param needle  The string to find.
 - @param haystack  The string to find it in.
 - @return  The index the string occurs at, or -1 if not found.
 -}
function indexOf
Integer ::= needle::String haystack::String
{
  return error("Not Yet Implemented: indexOf");
} foreign {
  "java" : return "Integer.valueOf(%haystack%.toString().indexOf(%needle%.toString()))";
}

@{--
 - Find the LAST index of a needle in the haystack.  (Indices are 0-based.)
 -
 - @param needle  The string to find.
 - @param haystack  The string to find it in.
 - @return  The index the string occurs at, or -1 if not found.
 -}
function lastIndexOf
Integer ::= needle::String haystack::String
{
  return error("Not Yet Implemented: lastIndexOf");
} foreign {
  "java" : return "Integer.valueOf(%haystack%.toString().lastIndexOf(%needle%.toString()))";
}

@{--
 - Return a substring of the original.  Indices are 0-based.
 -
 - @param start  The 0-based index to start at. Inclusive.
 - @param endl  The 0-based index to end before.  (Exclusive.)
 - @param str  The original string.
 - @return  The resulting substring.
 -}
function substring
String ::= start::Integer endl::Integer str::String
{
  return error("Not Yet Implemented: substring");
} foreign {
  "java" : return "(new common.StringCatter(%str%.toString().substring(%start%, %endl%)))";
}

@{--
 - Tests if one string is a prefix of another
 -
 - @param pre  The prefix.
 - @param s  The string to check the prefix of.
 - @return  true if pre is a prefix of s.  false otherwise.
 -}
function startsWith
Boolean ::= pre::String s::String
{
  return error("Not Yet Implemented: startsWith");
} foreign {
  "java" : return "Boolean.valueOf(%s%.toString().startsWith(%pre%.toString()))";
}

@{--
 - Tests if one string is a postfix of another
 -
 - @param post  The postfix.
 - @param s  The string to check the postfix of.
 - @return  true if post is a postfix of s.  false otherwise.
 -}
function endsWith
Boolean ::= post::String s::String
{
  return error("Not Yet Implemented: endsWith");
} foreign {
  "java" : return "Boolean.valueOf(%s%.toString().endsWith(%post%.toString()))";
}

@{--
 - Replaces all instances of 'search' with 'replace' in 'str'
 -
 - @param search  The string to replace
 - @param replace  The string to substitute in
 - @param str  The string to operate on
 - @return  The modified form of 'str'
 -}
function substitute
String ::= search::String replace::String str::String
{
  return error("Not Yet Implemented: substitute");
} foreign {
  "java" : return "new common.StringCatter(%str%.toString().replace((CharSequence)%search%.toString(),(CharSequence)%replace%.toString()))";
}

@{--
 - Return a string with 's' repeated 'n' times.
 -
 - @param n  The number of times to repeat the string
 - @param s  The string to repeat
 - @return  The string with 'n' copies of 's'
 -}
function replicate
String ::= n::Integer s::String
{ return error("Not Yet Implemented: replicate"); }
foreign {
 "java" : return "new common.StringCatter(new String(new char[%n%.intValue()]).replace(\"\\0\", %s%.toString()))";
}


@{--
 - Tests if all characters of a string are digits.  Partially unicode aware.
 - See java's Character.isDigit(char).
 -
 - @param str  The string to check
 - @return  true if all characters are digits.  false otherwise.
 -}
function isDigit
Boolean ::= str::String
{
  return error("Not Yet Implemented: isDigit");
} foreign {
  "java" : return "common.Util.isDigit(%str%.toString())";
}

@{--
 - Tests if all characters of a string are letters.  Partially unicode aware.
 - See java's Character.isLetter(char).
 -
 - @param str  The string to check
 - @return  true if all characters are letters.  false otherwise.
 -}
function isAlpha
Boolean ::= str::String
{
  return error("Not Yet Implemented: isAlpha");
} foreign {
  "java" : return "common.Util.isAlpha(%str%.toString())";
}

@{--
 - Tests if all characters of a string are whitespace.  Partially unicode aware.
 - See java's Character.isWhitespace(char).
 -
 - Includes space, tab, newline, carriage return, and more.
 -
 - @param str  The string to check
 - @return  true if all characters are whitespace.  false otherwise.
 -}
function isSpace
Boolean ::= str::String
{
  return error("Not Yet Implemented: isSpace");
} foreign {
  "java" : return "common.Util.isSpace(%str%.toString())";
}

@{--
 - Tests if all characters of a string are lower case.  Partially unicode aware.
 - See java's Character.isLowerCase(char).
 -
 - @param str  The string to check
 - @return  true if all characters are lower case.  false otherwise.
 -}
function isLower
Boolean ::= str::String
{
  return error("Not Yet Implemented: isLower");
} foreign {
  "java" : return "common.Util.isLower(%str%.toString())";
}

@{--
 - Tests if all characters of a string are upper case.  Partially unicode aware.
 - See java's Character.isUpperCase(char).
 -
 - @param str  The string to check
 - @return  true if all characters are upper case.  false otherwise.
 -}
function isUpper
Boolean ::= str::String
{
  return error("Not Yet Implemented: isUpper");
} foreign {
  "java" : return "common.Util.isUpper(%str%.toString())";
}

@{--
 - Converts this String to lowercase. See Java's String.toLowerCase().
 -
 - @param str  The string to convert.
 - @return  The lowercase string.
 -}
function toLowerCase
String ::= str::String
{
  return error("Not Yet Implemented: toLowerCase");
} foreign {
  "java" : return "(new common.StringCatter(%str%.toString().toLowerCase()))";
}

@{--
 - Converts this String to uppercase. See Java's String.toUpperCase().
 -
 - @param str  The string to convert.
 - @return  The uppercase string.
 -}
function toUpperCase
String ::= str::String
{
  return error("Not Yet Implemented: toUpperCase");
} foreign {
  "java" : return "(new common.StringCatter(%str%.toString().toUpperCase()))";
}

@{--
 - Safely converts a string to an integer.
 -
 - @param str  The string to convert
 - @return  The converted integer wrapped in just, or nothing if the
 -   conversion failed (e.g. not a number, or the number was too large)
 -}
function toIntSafe
Maybe<Integer> ::= str::String
{
  return error("Not Yet Implemented: toIntSafe");
} foreign {
  "java" : return "common.Util.safetoInt(%str%.toString())";
}

@{--
 - String append. Use overloaded append or ++ instead.
 -}
function stringAppend
String ::= s1::String s2::String
{
  return error("Foreign function");
} foreign {
  "java" : return "new common.StringCatter(%s1%, %s2%)";
}

@{--
 - Converts a list of code points to a string. Note that due to Java's use of
 - UCS-2, code points greater than 0xFFFF (i.e. and characters outside the Basic
 - Multilingual Plane) aren't supported.
 -}
function charsToString
String ::= chars::[Integer]
{
  return error("Foreign Function");
} foreign {
  "java" : return "common.StringCatter.fromChars(%chars%)";
}

@{--
 - Converts a string to a list of its UCS-2 characters. Note that this means
 - that surrogate pairs are (probably?) not supported, and characters outside
 - the Basic Multilingual Plane aren't as a consequence.
 -}
function stringToChars
[Integer] ::= str::String
{
  return error("Foreign Function");
} foreign {
  "java" : return "%str%.toChars()";
}

@{--
 - Replace all special characters in a string with their escape sequences.
 -}
function escapeString
String ::= s::String
{
  return error("Foreign function");
} foreign {
  "java" : return "(common.Util.escapeString(%s%))";
}

@{--
 - Replace all escape sequences in a string with corresponding special characters.
 -}
function unescapeString
String ::= s::String
{
  return error("Foreign function");
} foreign {
  "java" : return "(common.Util.unescapeString(%s%))";
}

@{--
 - Strips extra leading and trailing whitespace from a string.
 -}
function stripExtraWhiteSpace 
String ::= str::String 
{ return implode ("", stripExtraWhiteSpaceHelper(
                           woLeadingOrEndingWhiteSpace)) ; 

  local attribute woLeadingOrEndingWhiteSpace :: [String] ;
  woLeadingOrEndingWhiteSpace 
    = reverse((dropWhile(isSpace,
        reverse(dropWhile(isSpace, explode("",str)))))) ;
}

function stripExtraWhiteSpaceHelper
[String] ::= ss::[String]
{ return if   null(ss) 
         then [ ]
         else 
         if   hd==" " || hd=="\n" || hd=="\t"
         then (if null(tail(ss))
               then [ ] 
               else (if   nxt==" " || nxt=="\n" || nxt=="\t"
                     then stripExtraWhiteSpaceHelper(tail(ss)) -- drop hd
                     else " " :: stripExtraWhiteSpaceHelper(tail(ss))
                          -- replace hd with " "
                    )
              )
         else hd :: stripExtraWhiteSpaceHelper(tail(ss)) ;

  local attribute hd::String ;
  hd = head(ss) ;

  local attribute nxt::String ;
  nxt = head(tail(ss)) ;
}

@{--
 - Strips all whitespace from a string.
 -}
fun stripWhiteSpace String ::= s::String = implode ("", stripWhiteSpaceHelper(explode("",s)));

function stripWhiteSpaceHelper
[String] ::= ss::[String]
{ return if   null(ss) 
         then [ ]
         else 
         if   hd==" " || hd=="\n" || hd=="\t"
         then stripWhiteSpaceHelper(tail(ss)) 
         else hd :: stripWhiteSpaceHelper(tail(ss)) ;

  local attribute hd::String ;
  hd = head(ss) ;
}

@{--
 - Adds line numbers to a string
 -}
function addLineNumbers
String ::= code::String
{ return addLineNums(1, 2, lines) ;
  local lines::[String] = explode("\n",code) ;
}

function addLineNums
String ::= next::Integer width::Integer lines::[String]
{ return if null(lines)
         then ""
         else pad ++ ln ++ ": " ++ head(lines) ++ "\n" ++
              addLineNums(next+1, width, tail(lines)) ;
  local ln::String = toString(next); 
  local pad::String = implode("", repeat(" ", width - length(ln)) ) ;
}

function hashString
Integer ::= s::String
{
  return error("Foreign function");
} foreign {
  "java": return "%s%.toString().hashCode()";
}
