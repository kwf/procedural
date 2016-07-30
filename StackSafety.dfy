
include "Prelude.dfy"
include "Common.dfy"
include "Primitives.dfy"
include "StackSyntax.dfy"
include "StackTyping.dfy"
include "StackSemantics.dfy"

function ArbitraryValue(t: Type): value
  ensures TypeValue(ArbitraryValue(t)) == t
{
  match t
    case Int =>
      var v: int :| true;
      integer(v)
    case Bool =>
      var v: bool :| true;
      boolean(v)
    case Unit =>
      unit
}

lemma ProgressBool(o: BoolOp, v1: bool, v2: bool)
  ensures exists v :: BoolOpDenotes(o, v1, v2, v)
{
  match o
    case And => assert BoolOpDenotes(o, v1, v2, v1 && v2);
    case Or  => assert BoolOpDenotes(o, v1, v2, v1 || v2);
}

lemma ProgressRel(o: RelOp, v1: int, v2: int)
  ensures exists v :: RelOpDenotes(o, v1, v2, v)
{
  match o
    case Eq  => assert RelOpDenotes(o, v1, v2, v1 == v2);
    case NEq => assert RelOpDenotes(o, v1, v2, v1 != v2);
    case LT  => assert RelOpDenotes(o, v1, v2, v1 <  v2);
    case LTE => assert RelOpDenotes(o, v1, v2, v1 <= v2);
}

lemma ProgressMath(o: MathOp, v1: int, v2: int)
  ensures exists v :: MathOpDenotes(o, v1, v2, v)
{
  match o
    case Plus => assert MathOpDenotes(o, v1, v2, v1 + v2);
    case Times => assert MathOpDenotes(o, v1, v2, v1 * v2);
    case Minus => assert MathOpDenotes(o, v1, v2, v1 - v2);
    case DividedBy =>
      if v2 != 0 {
        assert MathOpDenotes(o, v1, v2, v1 / v2);
      } else {
        var v :| true;
        assert MathOpDenotes(o, v1, v2, v);
      }
    case Mod =>
      if v2 != 0 {
        assert MathOpDenotes(o, v1, v2, v1 % v2);
      } else {
        var v :| true;
        assert MathOpDenotes(o, v1, v2, v);
      }
}

lemma ProgressOperation(o: operation, s: sigma)
  requires exists t: Type :: TypeOperation(o) == (TypeSigma(s), t)
  ensures exists v :: StepOperation(o, s, v) && TypeValue(v) == TypeOperation(o).1
{
  match o
    case not =>
      assert StepOperation(o, s, boolean(!s[0].getBoolean));
    case const(x) =>
      assert StepOperation(o, s, x);
    case read(t) =>
      assert StepOperation(o, s, ArbitraryValue(t));
    case printf(format) =>
      assert StepOperation(o, s, unit);
    case binary(o) =>
      match o
        case MathOp(o) =>
          ProgressMath(o, s[0].getInteger, s[1].getInteger);
          var v :| MathOpDenotes(o, s[0].getInteger, s[1].getInteger, v);
          assert StepOperation(binary(MathOp(o)), s, integer(v));
        case BoolOp(o) =>
          ProgressBool(o, s[0].getBoolean, s[1].getBoolean);
          var v :| BoolOpDenotes(o, s[0].getBoolean, s[1].getBoolean, v);
          assert StepOperation(binary(BoolOp(o)), s, boolean(v));
        case RelOp(o) =>
          ProgressRel(o, s[0].getInteger, s[1].getInteger);
          var v :| RelOpDenotes(o, s[0].getInteger, s[1].getInteger, v);
          assert StepOperation(binary(RelOp(o)), s, boolean(v));
}

lemma ProgressCommand(c: command, s: sigma, S: Sigma)
  requires Prefix(S, TypeSigma(s))
  requires exists S' :: TypeCommand(c, S) == Just(S')
  ensures  exists s' :: StepCommand(c, s, s')
                  //&& Prefix(TypeCommand(c, S).FromJust, TypeSigma(s'))
{
  match c
    case pop(n) =>
      assert StepCommand(c, s, s[n..]);
    case load(n) =>
      assert StepCommand(c, s, [s[n]] + s);
    case store(n) =>
      assert StepCommand(c, s, s[n := s[0]][1..]);
    case apply(n, o) =>
      var (So, t) := TypeOperation(o);
      assert TypeSigma(s[..n]) == So;
      ProgressOperation(o, s[..n]);
      var v :| StepOperation(o, s[..n], v);
      assert StepCommand(c, s, [v] + s[n..]);
}

lemma ProgressJump(SigmaH: Sigma, D: Delta, d: delta, j: jump, Phi: Phi, phi: phi)
  requires TypeProgram(SigmaH, D, d)
  requires TypeJump(D, SigmaH, j, Phi)
  requires ValidStack(D, phi)
  requires SubPhi(Phi, TypePhi(D, phi))
  requires j != halt
  ensures  exists phi', b' :: StepJump(d, j, phi, phi', b')
                        //&& TypeBlock(D, SigmaH, b', TypePhi(D, phi'))
{
  match j
    case goto(nu) =>
      assert StepJump(d, j, phi, phi, d[nu]);
    case branch(nu1, nu2) =>
      var nu := phi[0].0;
      var s  := phi[0].1;
      var b  := s[0].getBoolean;
      assert StepJump(d, j, phi, [(nu, s[1..])] + phi[1..], d[if b then nu1 else nu2]);
    case call(n, nuJ, nuR) =>
      var nu := phi[0].0;
      var s  := phi[0].1;
      var (s1, s2) := Split(n, s);
      assert StepJump(d, j, phi, [(nuR, s1), (nu, s2)] + phi[1..], d[nuJ]);
    case ret(n) =>
      var nuR := phi[0].0;
      var s_check := phi[0].1[..n];
      var nu := phi[1].0;
      var s  := phi[1].1;
      assert StepJump(d, j, phi, [(nu, s_check + s)] + phi[2..], d[nuR]);
}

lemma ProgressBlock(SigmaH: Sigma, D: Delta, d: delta, b: block, Phi: Phi, phi: phi)
  requires TypeProgram(SigmaH, D, d)
  requires TypeBlock(D, SigmaH, b, Phi)
  requires ValidStack(D, phi)
  requires SubPhi(Phi, TypePhi(D, phi))
  ensures  (b == (Nil, halt) && Prefix(SigmaH, Phi.out[0].1)) ||
           exists phi', b' :: StepBlock(d, b, phi, phi', b')
{
  var (cs, j) := b;
  match cs
    case Cons(c, cs) =>
      var nu := phi[0].0;
      var s := phi[0].1;
      var S := Phi.out[0].1;
      ProgressCommand(c, s, S);
      var s' :| StepCommand(c, s, s');
      assert StepBlock(d, b, phi, phi[0 := (nu, s')], (cs, j));
    case Nil =>
      if j != halt {
        ProgressJump(SigmaH, D, d, j, Phi, phi);
        var phi', b' :| StepJump(d, j, phi, phi', b');
        assert StepBlock(d, b, phi, phi', b');
      }
}
