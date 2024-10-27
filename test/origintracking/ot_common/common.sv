imports silver:testing;
imports silver:reflect;
imports silver:langutil;

exports silver:testing;
exports silver:reflect;
exports silver:langutil;

function identityHashCode
Integer ::= nt::a
{
  return error("Not impl");
} foreign {
  "java" : return "(System.identityHashCode(%nt%))";
}