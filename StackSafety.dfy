
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

lemma SafetyOperation(o: operation, s: sigma)
  requires TypeOperation(o).0 == TypeSigma(s)
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

lemma SafetyCommand(c: command, s: sigma, S: Sigma)
  requires Prefix(S, TypeSigma(s))
  requires exists S' :: TypeCommand(c, S) == Just(S')
  ensures  exists s' :: StepCommand(c, s, s') &&
                  Prefix(TypeCommand(c, S).FromJust, TypeSigma(s'))
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
      SafetyOperation(o, s[..n]);
      var v :| StepOperation(o, s[..n], v) && TypeValue(v) == TypeOperation(o).1;
      assert StepCommand(c, s, [v] + s[n..]);
}

lemma PreservationJump(SigmaH: Sigma, D: Delta, d: delta, j: jump, Phi: Phi, phi: phi, phi': phi, b': block)
  requires TypeProgram(SigmaH, D, d)
  requires TypeJump(D, SigmaH, j, Phi)
  requires ValidStack(D, phi)
  requires SubPhi(Phi, TypePhi(D, phi))
  requires StepJump(d, j, phi, phi', b')
  requires j != halt
  ensures  TypeBlock(D, SigmaH, b', TypePhi(D, phi'))
{
  match j

    case goto(nu) =>

      SubPhiTransitive(D[nu], Phi, TypePhi(D, phi));
      TypeBlockExpansion(D, SigmaH, d[nu], D[nu], TypePhi(D, phi));

    case branch(nu1, nu2) =>

      var nu := phi[0].0;
      var s  := phi[0].1;
      var b  := s[0].getBoolean;
      var nuJ := if b then nu1 else nu2;
      var phi' := [(nu, s[1..])] + phi[1..];
      var (PhiR, S) := Phi.out[0];
      var Phi' := MkPhi([(PhiR, S[1..])] + Phi.out[1..]);
      SubPhiTransitive(D[nuJ], Phi', TypePhi(D, phi'));
      TypeBlockExpansion(D, SigmaH, d[nuJ], D[nuJ], TypePhi(D, phi'));

    case call(n, nuJ, nuR) =>

      var nu := phi[0].0;
      var s  := phi[0].1;
      var (s1, s2) := Split(n, s);
      var (PhiR, S) := Phi.out[0];
      var (S1, S2) := Split(n, S);

      // Eventual Phi required by the call
      var Phi' := MkPhi([(D[nuR], S1), (PhiR, S2)] + Phi.out[1..]);

      // Connecting split types to split values
      // We split the Sigmas and sigmas, and we want to ensure they're still prefixes
      assert Prefix(S, TypeSigma(s));
      calc {
        Prefix(S, TypeSigma(s));
        Prefix(S1 + S2, TypeSigma(s)[..n] + TypeSigma(s)[n..]);
        { PrefixSplit(n, S, TypeSigma(s)); }
        Prefix(S1, TypeSigma(s)[..n]) && Prefix(S2, TypeSigma(s)[n..]);
        { MapSeqSplit(n, TypeValue, s); }
        Prefix(S1, TypeSigma(s1)) && Prefix(S2, TypeSigma(s2));
      }
      assert Prefix(S1, TypeSigma(s1));
      assert Prefix(S2, TypeSigma(s2));

      // This proof segment is tricky:
      // If we add a MkPhi to every line in the calc, it doesn't work
      // All we're doing here is unfolding TypePhi(D, thephi) completely
      var thephi := [(nuR, s1), (nu, s2)];
      calc {
        TypePhi(D, thephi).out;
        MapSeq(TypeFrame(D), thephi);
        { assert forall i | 0 <= i < |thephi| ::
          MapSeq(TypeFrame(D), thephi)[i] ==
          TypeFrame(D)(thephi[i]); }
        [TypeFrame(D)(thephi[0]), TypeFrame(D)(thephi[1])];
        [(D[nuR], TypeSigma(s1)), (D[nu], TypeSigma(s2))];
      }
      assert TypePhi(D, thephi) ==
        MkPhi([(D[nuR], TypeSigma(s1)), (D[nu], TypeSigma(s2))]);

      // Putting it all together
      var Phi'01 := MkPhi(Phi'.out [0..2]);
      var phi'01 := TypePhi(D, phi'[0..2]);
      var Phi'n  := MkPhi(Phi'.out [2..]);
      var phi'n  := TypePhi(D, phi'[2..]);
      assert SubPhi(D[nu], PhiR);
      SubPhiReflexive(D[nuR]);
      assert SubPhi(Phi'01, phi'01);  // <-- all this proof effort above, to show this line
      assert SubPhi(Phi'n,  phi'n);
      calc {
        SubPhi(Phi'01, phi'01) && SubPhi(Phi'n, phi'n);
        { SubPhiJoin(Phi'01, Phi'n, phi'01, phi'n); }
        SubPhi(MkPhi(Phi'01.out + Phi'n.out), MkPhi(phi'01.out + phi'n.out));
        SubPhi(Phi', MkPhi(phi'01.out + phi'n.out));
        { MapSeqHomomorphism(TypeFrame(D), phi'[0..2], phi'[2..]); }
        SubPhi(Phi', TypePhi(D, phi'));
      }
      assert SubPhi(Phi', TypePhi(D, phi'));  // <-- and all that to show this
      assert SubPhi(D[nuJ], Phi');  // which when we combine it with this...

      SubPhiTransitive(D[nuJ], Phi', TypePhi(D, phi'));  // ...lets us say this
      TypeBlockExpansion(D, SigmaH, d[nuJ], D[nuJ], TypePhi(D, phi'));

    case ret(n) =>
}

lemma ProgressJump(SigmaH: Sigma, D: Delta, d: delta, j: jump, Phi: Phi, phi: phi)
  requires TypeProgram(SigmaH, D, d)
  requires TypeJump(D, SigmaH, j, Phi)
  requires ValidStack(D, phi)
  requires SubPhi(Phi, TypePhi(D, phi))
  requires j != halt
  ensures  exists phi', b' :: StepJump(d, j, phi, phi', b')
{
  match j
    case goto(nu) =>
      assert StepJump(d, j, phi, phi, d[nu]);
    case branch(nu1, nu2) =>
      var nu := phi[0].0;
      var s  := phi[0].1;
      var b  := s[0].getBoolean;
      var nuJ := if b then nu1 else nu2;
      var phi' := [(nu, s[1..])] + phi[1..];
      var (PhiR, S) := Phi.out[0];
      var Phi' := MkPhi([(PhiR, S[1..])] + Phi.out[1..]);
      assert StepJump(d, j, phi, phi', d[nuJ]);
    case call(n, nuJ, nuR) =>
      var nu := phi[0].0;
      var s  := phi[0].1;
      var (s1, s2) := Split(n, s);
      var (PhiR, S) := Phi.out[0];
      var (S1, S2) := Split(n, S);
      var phi' := [(nuR, s1), (nu, s2)] + phi[1..];
      var Phi' := MkPhi([(D[nuR], S1), (PhiR, S2)] + Phi.out[1..]);
      assert StepJump(d, j, phi, phi', d[nuJ]);
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
      SafetyCommand(c, s, S);
      var s' :| StepCommand(c, s, s');
      assert StepBlock(d, b, phi, phi[0 := (nu, s')], (cs, j));
    case Nil =>
      if j != halt {
        ProgressJump(SigmaH, D, d, j, Phi, phi);
        var phi', b' :| StepJump(d, j, phi, phi', b');
        assert StepBlock(d, b, phi, phi', b');
      }
}
