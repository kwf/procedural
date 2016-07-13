

include "Prelude.dfy"
include "SourceSyntax.dfy"
include "SourceTyping.dfy"

// BIG STEP SEMANTICS

type State = map<Id, Expr>

predicate method TypeState(delta: Delta, gamma: Gamma, s: State) {
  forall id :: id in s ==>
    id in gamma &&
    TypeExpr(delta, gamma, s[id], gamma[id])
}

predicate method ValidState(s: State) {
  forall id | id in s :: SyntacticValue(s[id])
}

predicate method SyntacticValue(e: Expr) {
  e.Unit? || e.False? || e.True? || e.Literal?
}

predicate ApplyDenotes(op: Op, e1: Expr, e2: Expr, result: Expr) {
  match op
    case BoolOp(boolOp) =>
      exists b1, b2, r ::
        IsBool(b1, e1) &&
        IsBool(b2, e1) &&
        IsBool(r, result) &&
        BoolOpDenotes(boolOp, b1, b2, r)
    case RelOp(relOp)   =>
      exists v1, v2, r ::
        IsLiteral(v1, e1) &&
        IsLiteral(v2, e2) &&
        IsBool(r, result) &&
        RelOpDenotes(relOp, v1, v2, r)
    case MathOp(mathOp) =>
      exists v1, v2, r ::
        IsLiteral(v1, e1) &&
        IsLiteral(v2, e2) &&
        IsLiteral(r, result) &&
        MathOpDenotes(mathOp, v1, v2, r)
}

predicate method IsBool(b: bool, e: Expr) {
  if e == True then b == true else
  if e == False then b == false else
  false
}

predicate method IsLiteral(i: int, e: Expr) {
  if !e.Literal? then false
  else match e case Literal(l) => l == i
}

predicate method BoolOpDenotes(op: BoolOp, b1: bool, b2: bool, result: bool) {
  match op
    case Or  => result == b1 || b2
    case And => result == b1 && b2
}

predicate method RelOpDenotes(op: RelOp, v1: int, v2: int, result: bool) {
  match op
    case Eq  => result == (v1 == v2)
    case NEq => result == (v1 != v2)
    case LT  => result == (v1 < v2)
    case LTE => result == (v1 <= v2)
}

predicate method MathOpDenotes(op: MathOp, v1: int, v2: int, result: int) {
  match op
    case Plus      =>           result == v1 + v2
    case Times     =>           result == v1 * v2
    case Minus     =>           result == v1 - v2
    case DividedBy => v2 != 0 ==> result == v1 / v2  // division by zero is undefined
    case Mod       => v2 != 0 ==> result == v1 % v2  // division by zero is undefined
}

inductive predicate EvalExpr(d: TopLevel, s: State, e: Expr, r: Expr)
  requires ValidState(s)
{
  if e.Unit? || e.True? || e.False? || e.Literal? then r == e
  else match e
    case Id(id) =>
      id in s && r == s[id]
    case Not(e') =>
      exists b ::
        EvalBool(d, s, e', b) &&
        r == if b then False else True
    case Apply(e1, op, e2) =>
      exists v1, v2 ::
        EvalExpr(d, s, e1, v1) &&
        EvalExpr(d, s, e2, v2) &&
        ApplyDenotes(op, v1, v2, r)
    case IfThenElse(e1, e2, e3) =>
      exists b :: EvalBool(d, s, e1, b) &&
        if b then EvalExpr(d, s, e2, r)
             else EvalExpr(d, s, e3, r)
    case Call(p, es) =>
      exists vs ::
        EvalList(d, s, es, vs) &&
        EvalCall(d, p, vs, r)
}

inductive predicate EvalList(d: TopLevel, s: State, es: List<Expr>, rs: List<Expr>)
  requires ValidState(s)
{
  Length(es) == Length(rs) &&
  forall evaluation ::
    evaluation in Elements(Zip(es, rs)) ==>
      var (e, r) := evaluation; EvalExpr(d, s, e, r)
}

inductive predicate EvalBool(d: TopLevel, s: State, e: Expr, b: bool)
  requires ValidState(s)
{
  exists v :: EvalExpr(d, s, e, v) && IsBool(b, v)
}

inductive predicate EvalCall(d: TopLevel, p: Id, args: List<Expr>, result: Expr) {
  p in d &&
  var (params, body) := d[p];
  Length(params) == Length(args) &&
  (forall a :: a in Elements(args) ==> SyntacticValue(a)) &&
  var s := NewState(params, args);
  exists s' | ValidState(s') ::
     EvalBlock(d, body, s, s', Just(result)) ||                  // normal return
    (EvalBlock(d, body, s, s', Nothing) && result == Expr.Unit)  // auto-unit return
}

function method NewState(params: List<Id>, vs: List<Expr>): map<Id, Expr>
  requires Length(vs) == Length(params)
  requires forall v :: v in Elements(vs) ==> SyntacticValue(v)
  ensures ValidState(NewState(params, vs))
{
  NormalFormNewState(params, vs);
  MapFromList(Zip(params, vs))
}

lemma NormalFormNewState(params: List<Id>, vs: List<Expr>)
  requires Length(vs) == Length(params)
  requires forall v :: v in Elements(vs) ==> SyntacticValue(v)
  ensures ValidState(MapFromList(Zip(params, vs)))
{
  if !vs.Nil? {
    NormalFormNewState(params.Tail, vs.Tail);
  }
}

inductive predicate EvalStatement(d: TopLevel, c: Statement, s: State, s'': State, r: Maybe<Expr>)
  requires ValidState(s)
  requires ValidState(s'')
{
  match c
    case Var(id, _, e) =>
      r.Nothing? &&
      exists v ::
        EvalExpr(d, s, e, v) &&
        s'' == s[id := v]
    case Assign(id, e) =>
      r.Nothing? &&
      exists v ::
        EvalExpr(d, s, e, v) &&
        s'' == s[id := v]
    case IfThenElse(e1, c2, c3) =>
      exists b :: EvalIfStatement(d, e1, c2, c3, s, s'', r, b)
    case While(e, c) =>
      exists b :: EvalBool(d, s, e, b) &&
        if !b
          then s == s'' && r == Nothing
          else exists s', broken ::
            EvalWhileLoop(d, e, c, s, s', s'', r, broken)
    case Return(e) =>
      exists v ::
      EvalExpr(d, s, e, v) &&
      r == Just(v) &&
      s == s''
    case Read(maybeId, t) =>
      r.Nothing? &&
      if maybeId.Just? then
        var id := maybeId.FromJust;
        Havoc(id, t, s, s'')
      else s == s''
    case Print(_, es) =>
      r.Nothing? &&
      s == s'' &&
      exists vs :: EvalList(d, s, es, vs)
    case Call(maybeId, p, es) =>
      r.Nothing? &&
      exists vs, r ::
        EvalList(d, s, es, vs) &&
        EvalCall(d, p, vs, r) &&
        if maybeId.Just? then var id := maybeId.FromJust;
           s'' == s[id := r]
           else s == s''
}

inductive predicate EvalIfStatement(d: TopLevel, e: Expr, c1: Block, c2: Block, s: State, s': State, r: Maybe<Expr>, b: bool)
  requires ValidState(s)
  requires ValidState(s')
{
  EvalBool(d, s, e, b) &&
    if b then EvalBlock(d, c1, s, s', r)
         else EvalBlock(d, c2, s, s', r)
}

inductive predicate EvalWhileLoop(d: TopLevel, e: Expr, c: Block, s: State, s': State, s'': State, r: Maybe<Expr>, broken: bool)
  requires ValidState(s)
  requires ValidState(s'')
{
  ValidState(s') &&
    exists r' :: EvalBlock(d, c, s, s', r') &&
    if r'.Just?
      then r == r' && s' == s'' && broken == true
      else EvalStatement(d, While(e, c), s', s'', r) && broken == false
}

inductive predicate Havoc(id: Id, t: Type, s: State, s': State)
  requires ValidState(s)
  requires ValidState(s')
{
  match t
    case Unit => s' == s[id := Expr.Unit]
    case Bool => s' == s[id := True] || s' == s[id := False]
    case Int =>
      id in s' && s'[id].Literal? &&  // in new state, the id is an int literal
      (forall k :: (k in s ==> k in s')) &&  // new state has domain >= old state
      forall k :: (k in s && k != id ==> s[k] == s'[k]) &&  // all keys != id are preserved in new state
      (k !in s && k != id ==> k !in s')  // no new keys (except maybe id) are introduced
}

inductive predicate EvalBlock(d: TopLevel, cs: Block, s: State, s'': State, result: Maybe<Expr>)
  requires ValidState(s)
  requires ValidState(s'')
{
  match cs
    case Nil =>
      result.Nothing? && s == s''
    case Cons(c, cs') =>
      exists r, s' | ValidState(s') && EvalStatement(d, c, s, s', r) ::
        if r.Just?
          then r == result && s' == s''
          else EvalBlock(d, cs', s', s'', result)
}

predicate EvalProgram(d: TopLevel, result: Expr)
{
  EvalCall(d, 0, Nil, Expr.Unit)
}
