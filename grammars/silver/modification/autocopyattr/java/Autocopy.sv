grammar silver:modification:autocopyattr:java;
import silver:modification:autocopyattr;

import silver:definition:core;
import silver:definition:env;
import silver:definition:type:syntax;
import silver:definition:type;

import silver:translation:java:core;
import silver:translation:java:type;

import silver:util;


aspect production attributeDclAuto
top::AGDcl ::= 'autocopy' 'attribute' a::Name '<' tl::TypeList '>' '::' te::Type ';'
{
  local attribute className :: String;
  className = "D" ++ a.name;

  top.javaClasses = [[className,
		
"package " ++ makeName(top.grammarName) ++ ";\n\n" ++

"import java.util.*;\n\n" ++

"public class " ++ className ++ " extends common.Decorator {\n\n" ++

"public static final " ++ className ++ " singleton = new " ++ className ++ "();\n\n" ++

"\tpublic void decorate(Class production) {\n" ++
"\t\tdecorateAutoCopy(production, \"" ++ fName ++ "\");\n" ++
"\t}\n" ++
"}\n"
		]];
		
  top.setupInh := "";
  top.initProd := "";
  top.initValues := "";
  top.postInit := "";
}

aspect production attributionDcl
top::AGDcl ::= 'attribute' a::QName '<' tlat::TypeList '>' 'occurs' 'on' nt::QName '<' tlnt::TypeList '>' ';'
{
  -- TODO: like the other occurs, maybe this should be moved to setupInh?
  top.initProd <- 
    case a.lookupAttribute.dcl of
      autocopyDcl(_,_,_,_) ->  "\t\t" ++ makeNTClassName(nt.lookupType.fullName) ++ ".decorators.add(" ++ makeDecoratorClassName(a.lookupAttribute.fullName) ++ ".singleton);\n"
    | _ -> ""
    end;
}

function makeDecoratorClassName
String ::= s::String {
  return makeClassNameHelp(split(":", s), "D");
}
