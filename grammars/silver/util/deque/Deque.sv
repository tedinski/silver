grammar silver:util:deque;

imports silver:core with reverse as listReverse;

-- This is all based on Okasaki 1998.

nonterminal Deque<a>;

abstract production deque
top::Deque<a> ::= ln::Integer l::[a] rn::Integer r::[a]
{}

fun empty Deque<a> ::= = deque(0, [], 0, []);

function cons
Deque<a> ::= e::a q::Deque<a>
{
  return case q of deque(ln,l,rn,r) -> check(ln+1,e::l,rn,r) end;
}
function head
a ::= q::Deque<a>
{
  return case q of 
  | deque(_,[],_,x::_) -> x -- single element
  | deque(_,x::_,_,_) -> x
  | _ -> error("Requested head of empty deque")
  end;
}
function tail
Deque<a> ::= q::Deque<a>
{
  return case q of 
  | deque(_,[],_,_::_) -> empty() -- single element
  | deque(ln,lh::lt,rn,r) -> check(ln-1, lt, rn, r)
  | _ -> error("Requested tail of empty deque")
  end;
}
function snoc
Deque<a> ::= q::Deque<a> e::a
{
  return case q of deque(ln,l,rn,r) -> check(ln,l,rn+1,e::r) end;
}
function last
a ::= q::Deque<a>
{
  return case q of 
  | deque(_,x::_,_,[]) -> x -- single element
  | deque(_,_,_,x::_) -> x
  | _ -> error("Requested last of empty deque")
  end;
}
function init
Deque<a> ::= q::Deque<a>
{
  return case q of 
  | deque(_,_::_,_,[]) -> empty() -- single element
  | deque(ln,l,rn,rh::rt) -> check(ln, l, rn-1, rt)
  | _ -> error("Requested init of empty deque")
  end;
}
function isEmpty
Boolean ::= q::Deque<a>
{
  return case q of deque(ln,_,rn,_) -> ln == 0 && rn == 0 end;
}
function reverse
Deque<a> ::= q::Deque<a>
{
  return case q of deque(ln,l,rn,r) -> deque(rn,r,ln,l) end;
}

function check
Deque<a> ::= lenf::Integer f::[a] lenr::Integer r::[a]
{
  local mid::Integer = (lenf + lenr) / 2;
  local rest::Integer = lenf + lenr - mid;
  return if lenf > 2 * lenr + 1 then
           let fprime ::[a]= take(mid,f),
               rprime ::[a] = r ++ listReverse(drop(mid,f))
            in deque(mid, fprime, rest, rprime) end
         else if lenr > 2*lenf + 1 then
           let rprime ::[a]= take(mid, r),
               fprime ::[a]= f ++ listReverse(drop(mid, r))
            in deque(rest, fprime, mid, rprime) end
         else deque(lenf, f, lenr, r);
}

