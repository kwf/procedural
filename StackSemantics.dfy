
include "Prelude.dfy"
include "Common.dfy"
include "Primitives.dfy"
include "StackTyping.dfy"
include "StackSubtyping.dfy"

predicate method StepOperation(o: operation, s: sigma, v: value)
{
  match o
    case not =>
      |s| == 1 && s[0].boolean? &&
      v.boolean? &&
      s[0].getBoolean == !v.getBoolean
    case const(x) =>
      |s| == 0 &&
      v == x
    case read(t) =>
      |s| == 0 &&
      TypeValue(v) == t
    case printf(format) =>
      v == unit &&
      var types := SeqFromList(Lefts(format));
      |s| == |types| &&
      forall i | 0 <= i < |s| :: TypeValue(s[i]) == types[i]
    case binary(o) =>
      |s| == 2 &&
      match o
        case RelOp(o) =>
          v.boolean? &&
          s[0].integer? && s[1].integer? &&
          RelOpDenotes(o, s[0].getInteger, s[1].getInteger, v.getBoolean)
        case MathOp(o) =>
          v.integer? &&
          s[0].integer? && s[1].integer? &&
          MathOpDenotes(o, s[0].getInteger, s[1].getInteger, v.getInteger)
        case BoolOp(o) =>
          v.boolean? &&
          s[0].boolean? && s[1].boolean? &&
          BoolOpDenotes(o, s[0].getBoolean, s[1].getBoolean, v.getBoolean)
}

predicate method StepCommand(c: command, s: sigma, s': sigma)
{
  match c
    case store(n) =>
      n < |s| &&
      s' == s[n := s[0]][1..]
    case load(n) =>
      n < |s| &&
      s' == [s[n]] + s
    case pop(n) =>
      n <= |s| &&
      s' == s[n ..]
    case apply(n, o) =>
      n <= |s| &&
      var (s1, s2) := Split(n, s);
      0 < |s'| &&
      StepOperation(o, s1, s'[0]) &&
      s'[1..] == s2
}

predicate method StepJump(d: delta, j: jump, phi: phi, phi': phi, b: block)
{
  match j
    case halt => false
    case goto(nu) =>
      nu in d &&
      phi == phi' &&
      b == d[nu]
    case branch(nu1, nu2) =>
      nu1 in d && nu2 in d &&
      0 < Length(phi) == Length(phi') &&
      var nu := Nth(0, phi).0;
      var s := Nth(0, phi).1;
      0 < Length(s) &&
      phi' == [(nu, s[1..])] + phi[1..] &&
      s[0].boolean? &&
      b == d[if s[0].getBoolean then nu1 else nu2]
    case call(n, nuJ, nuR) =>
      nuJ in d && nuR in d &&
      0 < |phi| == |phi'| - 1 &&
      var nu := phi[0].0;
      var s := phi[0].1;
      n <= |s| &&
      var (s1, s2) := Split(n, s);
      phi' == [(nuR, s1), (nu, s2)] + phi[1..] &&
      b == d[nuJ]
    case ret(n) =>
      0 < |phi| - 1 == |phi'| &&
      var nuR := phi[0].0;
      var ss  := phi[0].1;
      n <= |ss| &&
      var (s_check, _) := Split(n, ss);
      var nu := phi[1].0;
      var s  := phi[1].1;
      phi' == [(nu, s_check + s)] + phi[2..] &&
      nuR in d && b == d[nuR]
}

predicate method StepBlock(d: delta, b: block, phi: phi, phi': phi, b': block)
{
  var (cs, j) := b;
  match cs
    case Nil => StepJump(d, j, phi, phi', b')
    case Cons(c, cs) =>
      0 < |phi| == |phi'| &&
      var nu := phi[0].0;
      var s  := phi[0].1;
      nu == phi'[0].0 &&
      phi[1..] == phi'[1..] &&
      var s' := phi'[0].1;
      StepCommand(c, s, s') &&
      b' == (cs, j)
}

inductive predicate StepBlockStar(d: delta, b: block, phi: phi, phi'': phi, b'': block)
{
  (b == b'' && phi == phi'') ||
    exists b', phi' ::
      StepBlock(d, b, phi, phi', b') &&
      StepBlockStar(d, b', phi', phi'', b'')
}
