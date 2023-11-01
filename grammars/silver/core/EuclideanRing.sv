grammar silver:core;

@{- Provides the `/` and `%` operators.
  -
  - Laws:
  -
  - * Integral Domain (TODO: are these equivalent?):
  -   * `one != zero`
  -   * `(a != zero && b != zero) -> mul(a, b) != zero`
  - * Non-negativity of `degree`: `degree(x) >= 0`
  - * Quotient: `(b != zero) -> (add(mul(div(a, b), b), mod(a, b)) = a)`
  - * `degree`-`mod` interaction: `(b != zero) -> (mod(a, b) = 0 || degree(mod(a, b)) < degree(b))`
  - * `degree`-`mul` interaction: `(a != zero && b != zero) -> (degree(a) <= degree(mul(a, b)))`
  -}
class CommutativeRing a => EuclideanRing a {
  degree :: (Integer ::= a);
  div :: (a ::= a a);
  mod :: (a ::= a a);
}

instance EuclideanRing Integer {
  degree = \n -> if n < 0 then -n else n;
  div = divInteger;
  mod = modInteger;
}

function divInteger
Integer ::= a::Integer b::Integer
{
  return error("Foreign function");
} foreign {
  "java": return "(%a% / (int)%b%)";
}

function modInteger
Integer ::= a::Integer b::Integer
{
  return error("Foreign function");
} foreign {
  "java": return "(%a% % (int)%b%)";
}

instance EuclideanRing Float {
  degree = \n -> if n < 0.0 then toInteger(-n) else toInteger(n);
  div = divFloat;
  mod = modFloat;
}

function divFloat
Float ::= a::Float b::Float
{
  return error("Foreign function");
} foreign {
  "java": return "(%a% / (float)%b%)";
}

function modFloat
Float ::= a::Float b::Float
{
  return error("Foreign function");
} foreign {
  "java": return "(%a% % (float)%b%)";
}

@{- Computes the greatest common divisor of two numbers. -}
function gcd
Eq a, EuclideanRing a => a ::= a::a  b::a
{
  return
    if b == zero then
      a
    else
      gcd(b, mod(a, b));
}

@{- Computes the least common multiple of two numbers. -}
function lcm
Eq a, EuclideanRing a => a ::= a::a  b::a
{
  return
    if a == zero || b == zero then
      zero
    else
      div(mul(a, b), gcd(a, b));
}
