grammar silver:core;

closed nonterminal State<s a> with stateIn<s>, stateOut<s>, stateVal<a>;

inherited attribute stateIn<s>::s;
synthesized attribute stateOut<s>::s;
synthesized attribute stateVal<a>::a;

abstract production bindState
top::State<s b> ::= st::State<s a> fn::(State<s b> ::= a)
{
  st.stateIn = top.stateIn;
  local newState::State<s b> = fn(st.stateVal);
  newState.stateIn = st.stateOut;
  top.stateOut = newState.stateOut;
  
  top.stateVal = newState.stateVal;
}

abstract production returnState
top::State<s a> ::= x::a
{
  top.stateOut = top.stateIn;
  top.stateVal = x;
}

abstract production getState
top::State<s s> ::= 
{
  top.stateOut = top.stateIn;
  top.stateVal = top.stateIn;
}

abstract production setState
top::State<s Unit> ::= newState::s
{
  top.stateOut = newState;
  top.stateVal = unit();
}

abstract production modifyState
top::State<s Unit> ::= fun::(s ::= s)
{
  top.stateOut = fun(top.stateIn);
  top.stateVal = unit();
}

abstract production fixState
top::State<s a> ::= fn::(State<s a> ::= a)
{
  local st::State<s a> = fn(st.stateVal);
  st.stateIn = top.stateIn;
  top.stateOut = st.stateOut;
  top.stateVal = st.stateVal;
}

instance Functor State<a _> {
  map = liftM1;
}

instance Apply State<a _> {
  ap = apM;
}

instance Applicative State<a _> {
  pure = returnState;
}

instance Bind State<a _> {
  bind = bindState;
}

instance Monad State<a _> {}

instance MonadFix State<a _> {
  mfix = fixState;
}

function runState
Pair<s a> ::= st::State<s a> initialState::s
{
  st.stateIn = initialState;
  return (st.stateOut, st.stateVal);
}

function evalState
a ::= st::State<s a> initialState::s
{
  return runState(^st, initialState).snd;
}