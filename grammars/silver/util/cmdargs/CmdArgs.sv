grammar silver:util:cmdargs;


@{-
  - The type of lists of arguments given on the command line
  -
  - Define a new production (as a cons cell for the CmdArgs list) for each flag given on the command line:
  - - For a flag that takes no arguments on the command line, define a production of type (CmdArgs ::= CmdArgs)
  - - For a flag that takes a single argument, define a production of type (CmdArgs ::= String CmdArgs)
  - - For a flag that takes more arguments, define a prodution of type (CmdArgs ::= [String] CmdArgs)
  -
  - This shouldn't have inherited attributes, but can't be data because of how we abuse forwarding for defining flags.
  -}
nonterminal CmdArgs with cmdRemaining, cmdError;

@{-
  - The remaining arguments from the commandline after parsing the flags
  -}
synthesized attribute cmdRemaining :: [String];
@{-
  - The errors from parsing commandline arguments
  -}
synthesized attribute cmdError :: Maybe<String>;

@{-
  - A specification of a flag for @link[interpretCmdArgs].
  -
  - The `name` is the string that should be present in the arguments list in
  - order for this flag to be recognized. In an example `-o` flag, it would be
  - `"-o"`.
  -
  - The `paramString` is a string describing the parameters the flag takes, for
  - use in the help text. In our running example, this might be
  - `just("<file>")`. For flags that don't take an argument, this should be
  - `nothing()`.
  -
  - The `help` is a string describing the usage of the flag. Typically, this is
  - an English-language string that does *not* start with a capital letter, nor
  - end with a period. Often the imperative voice is used (e.g. "place the
  - output into <file>" rather than "the output file is <file>").
  -
  - The `flagParser` is the `Flag` value used to handle the flag.
  -
  - Putting these together, the `FlagSpec` for our example `-o` flag might look
  - something like:
  -
  - ```silver
  - flagSpec(name="-o", paramString=just("<file>"),
  -   help="place the output into <file>", flagParser=option(outFlag))
  - ```
  -}
data FlagSpec = flagSpec
  with name, paramString, help, flagParser;

annotation name::String;
annotation paramString::Maybe<String>;
annotation help::String;
annotation flagParser::Flag;

@{-
  - Produce a parsed list of arguments using the given flags from the given input
  -
  - @param flags  A list of FlagSpecs
  - @param input  A list of strings, generally the commandline arguments
  - @return The parsed list of arguments
  - @warning The flag names in the flags parameter MUST start with a hyphen
  -}
function interpretCmdArgs
CmdArgs ::= flags::[FlagSpec]  input::[String]
{
  local matchingFlagSpec::Maybe<FlagSpec> = lookup(
    head(input),
    map(\flag::FlagSpec -> (flag.name, flag), flags));

  -- Partial! Only demand if matchingFlagSpec.isJust
  local matchingFlag::Flag = matchingFlagSpec.fromJust.flagParser;
  matchingFlag.flagInput = input;
  matchingFlag.flagOriginal = interpretCmdArgs(flags, matchingFlag.flagOutput);
  
  return if null(input) then endCmdArgs([])
         else if !matchingFlagSpec.isJust
         then if startsWith("-", head(input))
              then errorCmdArgs("Unrecognized flag: " ++ head(input))
              else endCmdArgs(input)
         else matchingFlag.flagModified;
}

@{- Formats the --help text for the given FlagSpecs. -}
function flagSpecsToHelpText
String ::= flagSpecs::[FlagSpec]
{
  -- Output looks like (where _ = space, >>>> = tab):
  --
  -- __--flag1________>>>>flag1 help
  -- __--flag2 <path>_>>>>flag2 help
  --   \____________/\___/\________/
  --       \            \         \
  --        flag part    pad part  help part

  local unpaddedFlagParts::[(String, FlagSpec)] =
    map(\flagSpec::FlagSpec ->
          ( flagSpec.name ++ mapOrElse("",
                                       \paramString::String ->
                                         " " ++ paramString,
                                       flagSpec.paramString)
          , flagSpec
          ),
        sortByKey(\flagSpec::FlagSpec -> flagSpec.name,
                  flagSpecs));
  local longestUnpaddedFlagPart::Integer =
    foldl(max, 0,
          map(\flagPartItem::(String, FlagSpec) -> length(flagPartItem.1),
              unpaddedFlagParts));
  local lines::[String] =
    map(\flagPartItem::(String, FlagSpec) ->
          -- Leading space
          "  " ++
          -- Basic flag part
          flagPartItem.1 ++
          -- Flag part padding
          replicate(longestUnpaddedFlagPart - length(flagPartItem.1), " ") ++
          -- Pad part
          " \t" ++
          -- Help part
          flagPartItem.2.help ++
          -- Trailing newline
          "\n",
        unpaddedFlagParts);
   return implode("", lines);
}

@{--
  - For defining base, default values for any attributes on CmdArgs
  -
  - @param remaining  Commandline arguments remaining after parsing flags
  -}
abstract production endCmdArgs
top::CmdArgs ::= remaining::[String]
{
  top.cmdRemaining = remaining;
  top.cmdError = nothing();
}

@{--
  - Only used when an error is encountered attempting to parse an option.
  - One should always check for .cmdError.isJust BEFORE accessing any other attributes.
  -
  - @param errmsg  Error message
  -}
abstract production errorCmdArgs
top::CmdArgs ::= errmsg::String
{
  top.cmdRemaining = [];
  top.cmdError = just(errmsg);
  forwards to endCmdArgs([]); -- Well, this is an abuse, but this whole thing is an abuse, really.
}

@{--
  - Flags are a representation of what to do with command line flags/options.
  - It should not be necessary to define any new flags.
  -}
nonterminal Flag with flagInput, flagOutput, flagOriginal, flagModified;

inherited attribute flagInput::[String];
synthesized attribute flagOutput::[String];
inherited attribute flagOriginal::CmdArgs;
synthesized attribute flagModified::CmdArgs;

@{--
 - In the terminology I've just made up, a 'flag' is a cmd line option
 - with no parameters.
 -
 - @param ast  Production for handling this commandline option being given
 -}
abstract production flag
top::Flag ::= ast::(CmdArgs ::= CmdArgs)
{
  top.flagOutput = tail(top.flagInput);
  top.flagModified = ast(top.flagOriginal);
}

@{--
 - In the terminology I've just made up, an 'option' is a cmd line option
 - with one, single parameter.
 -
 - @param ast  Production for handling this commandline option being given
 -}
abstract production option
top::Flag ::= ast::(CmdArgs ::= String CmdArgs)
{
  top.flagOutput = if null(tail(top.flagInput)) then [] else tail(tail(top.flagInput));
  top.flagModified = if null(tail(top.flagInput))
                     then errorCmdArgs(head(top.flagInput) ++ " is missing its parameter.")
                     else ast(head(tail(top.flagInput)), top.flagOriginal);
}

@{--
 - In the terminology I've just made up, 'nOptions' is a cmd line option
 - with n parameters.
 -
 - @param n  The number of arguments expected by the flag
 - @param ast  Production for handling this commandline option being given
 -}
abstract production nOptions
top::Flag ::= n::Integer  ast::(CmdArgs ::= [String] CmdArgs)
{
  top.flagOutput =
      if length(top.flagInput) <= n + 1
      then []
      else drop(n + 1, top.flagInput);
  top.flagModified =
      if length(top.flagInput) < n + 1
      then errorCmdArgs(head(top.flagInput) ++ " only has " ++
                        toString(length(top.flagInput)) ++
                        " parameters, when it should have " ++
                        toString(n))
      else ast(take(n, drop(1, top.flagInput)), top.flagOriginal);
}

