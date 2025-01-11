grammar silver:compiler:composed:Default;

import silver:compiler:host;

parser svParse::File {
  silver:compiler:host;
}

fun main IO<Integer> ::= args::[String] = cmdLineRun(args, svParse);
