
include "Prelude.dfy"
include "Common.dfy"
include "Primitives.dfy"
include "StackSyntax.dfy"
include "StackTyping.dfy"
include "StackSemantics.dfy"

// PROGRESS: PRIMITIVES

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

// PROGRESS: OPERATIONS & COMMANDS

lemma ProgressOperation(o: operation, s: sigma)
  requires TypeOperation(o).0 == TypeSigma(s)
  ensures exists v :: StepOperation(o, s, v)
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
  requires TypeCommand(c, S).Just?
  ensures  exists s' :: StepCommand(c, s, s')
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
      var v :| StepOperation(o, s[..n], v) && TypeValue(v) == TypeOperation(o).1;
      assert StepCommand(c, s, [v] + s[n..]);
}

// PRESERVATION: OPERATIONS & COMMANDS

lemma PreservationOperation(o: operation, s: sigma, v: value)
  requires TypeOperation(o).0 == TypeSigma(s)
  requires StepOperation(o, s, v)
  ensures  TypeValue(v) == TypeOperation(o).1
{
  match o
    case not =>
    case const(x) =>
    case read(t) =>
    case binary(o) =>
    case printf(format) =>
      assert TypeOperation(o).1 == Unit;
      assume false; // TODO: Why does it not see that v == unit?
      assert v == unit;
}

lemma PreservationCommand(c: command, s: sigma, S: Sigma, s': sigma)
  requires Prefix(S, TypeSigma(s))
  requires TypeCommand(c, S).Just?
  requires StepCommand(c, s, s')
  ensures  Prefix(TypeCommand(c, S).FromJust, TypeSigma(s'))
{
  match c
    case pop(n) =>
    case load(n) =>
    case store(n) =>
    case apply(n, o) =>
      forall v | StepOperation(o, s[..n], v) {
        PreservationOperation(o, s[..n], v);
  }
}

// PROGRESS: JUMPS

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

// PROGRESS: BLOCKS

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

// PRESERVATION: JUMPS

lemma PreservationJumpGoto(SigmaH: Sigma, D: Delta, d: delta, j: jump, Phi: Phi, phi: phi, phi': phi, b': block)
  requires TypeProgram(SigmaH, D, d)
  requires TypeJump(D, SigmaH, j, Phi)
  requires ValidStack(D, phi)
  requires SubPhi(Phi, TypePhi(D, phi))
  requires StepJump(d, j, phi, phi', b')
  requires j.goto?
  ensures  TypeBlock(D, SigmaH, b', TypePhi(D, phi'))
{
  match j case goto(nu) =>

  SubPhiTransitive(D[nu], Phi, TypePhi(D, phi));
  TypeBlockExpansion(D, SigmaH, d[nu], D[nu], TypePhi(D, phi));
}

lemma PreservationJumpBranch(SigmaH: Sigma, D: Delta, d: delta, j: jump, Phi: Phi, phi: phi, phi': phi, b': block)
  requires TypeProgram(SigmaH, D, d)
  requires TypeJump(D, SigmaH, j, Phi)
  requires ValidStack(D, phi)
  requires SubPhi(Phi, TypePhi(D, phi))
  requires StepJump(d, j, phi, phi', b')
  requires j.branch?
  ensures  TypeBlock(D, SigmaH, b', TypePhi(D, phi'))
{
  match j case branch(nu1, nu2) =>

  var nu := phi[0].0;
  var s  := phi[0].1;
  var b  := s[0].getBoolean;
  var nuJ := if b then nu1 else nu2;
  var phi' := [(nu, s[1..])] + phi[1..];
  var (PhiR, S) := Phi.out[0];
  var Phi' := MkPhi([(PhiR, S[1..])] + Phi.out[1..]);
  SubPhiTransitive(D[nuJ], Phi', TypePhi(D, phi'));
  TypeBlockExpansion(D, SigmaH, d[nuJ], D[nuJ], TypePhi(D, phi'));
}

lemma PreservationJumpCall(SigmaH: Sigma, D: Delta, d: delta, j: jump, Phi: Phi, phi: phi, phi': phi, b': block)
  requires TypeProgram(SigmaH, D, d)
  requires TypeJump(D, SigmaH, j, Phi)
  requires ValidStack(D, phi)
  requires SubPhi(Phi, TypePhi(D, phi))
  requires StepJump(d, j, phi, phi', b')
  requires j.call?
  ensures  TypeBlock(D, SigmaH, b', TypePhi(D, phi'))
{
  match j case call(n, nuJ, nuR) =>

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

  // NOTE: This proof segment is tricky:
  // If we add a MkPhi to every line in the calc, it doesn't work
  // All we're doing here is unfolding TypePhi(D, thephi) completely
  // Why doesn't this happen automatically?
  // Also, this calc statement cannot be moved below the var statements below,
  // for completely mysterious reasons.
  calc {
    TypePhi(D, [(nuR, s1), (nu, s2)]).out;
    [(D[nuR], TypeSigma(s1)), (D[nu], TypeSigma(s2))];
  }

  // Putting it all together
  var Phi'01 := MkPhi(Phi'.out [0..2]);
  var phi'01 := TypePhi(D, phi'[0..2]);
  var Phi'n  := MkPhi(Phi'.out [2..]);
  var phi'n  := TypePhi(D, phi'[2..]);

  assert SubPhi(D[nu], PhiR);
  SubPhiReflexive(D[nuR]);
  assert SubPhi(Phi'01, phi'01);  // <-- all this proof effort above, to show this line

  assert SubPhi(Phi'n,  phi'n);  // this bit is more trivial

  // Assmebling the final SubPhi proof: Phi' <: TypePhi(D, phi')
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
  TypeBlockExpansion(D, SigmaH, d[nuJ], D[nuJ], TypePhi(D, phi'));  // boom.
}

lemma PreservationJumpRet(SigmaH: Sigma, D: Delta, d: delta, j: jump, Phi: Phi, phi: phi, phi': phi, b': block)
  requires TypeProgram(SigmaH, D, d)
  requires TypeJump(D, SigmaH, j, Phi)
  requires ValidStack(D, phi)
  requires SubPhi(Phi, TypePhi(D, phi))
  requires StepJump(d, j, phi, phi', b')
  requires j.ret?
  ensures  TypeBlock(D, SigmaH, b', TypePhi(D, phi'))
{
  match j case ret(n) =>

  var nuR         := phi    [0].0;
  var PhiR        := Phi.out[0].0;
  var s_check     := phi    [0].1[..n];
  var S_check     := Phi.out[0].1[..n];
  var nu          := phi    [1].0;
  var PhiR_origin := Phi.out[1].0;
  var s_origin    := phi    [1].1;
  var S_origin    := Phi.out[1].1;

  var Phi' := MkPhi([(PhiR_origin, S_check + S_origin)] + Phi.out[2..]);

  assert SubPhi(PhiR, Phi');
  assert SubPhi(D[nuR], PhiR);
  SubPhiTransitive(D[nuR], PhiR, Phi');

  calc {
    TypePhi(D, [(nu, s_check + s_origin)]).out;
    [(D[nu], TypeSigma(s_check + s_origin))];
    { MapSeqHomomorphism(TypeValue, s_check, s_origin); }
    [(D[nu], TypeSigma(s_check) + TypeSigma(s_origin))];
  }

  // Putting it all together
  var Phi'0 := MkPhi(Phi'.out [0..1]);
  var phi'0 := TypePhi(D, phi'[0..1]);
  var Phi'n := MkPhi(Phi'.out [1..]);
  var phi'n := TypePhi(D, phi'[1..]);

  assert SubPhi(Phi'0, phi'0);

  calc {
    SubPhi(Phi, TypePhi(D, phi));
    { SubPhiSplit(1, Phi, TypePhi(D, phi)); }
    SubPhi(Phi'n, MkPhi(TypePhi(D, phi).out[2..]));
    SubPhi(Phi'n, MkPhi(MapSeq(TypeFrame(D), phi)[2..]));
    { MapSeqSplit(1, TypeFrame(D), phi); }
    SubPhi(Phi'n, MkPhi(MapSeq(TypeFrame(D), phi[2..])));
    SubPhi(Phi'n, TypePhi(D, phi[2..]));
    { assert phi[2..] == phi'[1..]; }
    SubPhi(Phi'n, TypePhi(D, phi'[1..]));
    SubPhi(Phi'n, phi'n);
  }
  assert SubPhi(Phi'n, phi'n);

  // Assembling the final SubPhi proof: Phi' <: TypePhi(D, phi')
  calc {
    SubPhi(Phi'0, phi'0) && SubPhi(Phi'n, phi'n);
    { SubPhiJoin(Phi'0, Phi'n, phi'0, phi'n); }
    SubPhi(MkPhi(Phi'0.out + Phi'n.out), MkPhi(phi'0.out + phi'n.out));
    SubPhi(Phi', MkPhi(phi'0.out + phi'n.out));
    { MapSeqHomomorphism(TypeFrame(D), phi'[0..1], phi'[1..]); }
    SubPhi(Phi', TypePhi(D, phi'));
  }
  assert SubPhi(Phi', TypePhi(D, phi'));

  SubPhiTransitive(D[nuR], Phi', TypePhi(D, phi'));
  TypeBlockExpansion(D, SigmaH, d[nuR], D[nuR], TypePhi(D, phi'));
}

lemma PreservationJump(SigmaH: Sigma, D: Delta, d: delta, j: jump, Phi: Phi, phi: phi, phi': phi, b': block)
  requires TypeProgram(SigmaH, D, d)
  requires TypeJump(D, SigmaH, j, Phi)
  requires ValidStack(D, phi)
  requires SubPhi(Phi, TypePhi(D, phi))
  requires StepJump(d, j, phi, phi', b')
  ensures  TypeBlock(D, SigmaH, b', TypePhi(D, phi'))
{
  match j
    case goto(nu) =>
      PreservationJumpGoto(SigmaH, D, d, j, Phi, phi, phi', b');
    case branch(nu1, nu2) =>
      PreservationJumpBranch(SigmaH, D, d, j, Phi, phi, phi', b');
    case call(n, nuJ, nuR) =>
      PreservationJumpCall(SigmaH, D, d, j, Phi, phi, phi', b');
    case ret(n) =>
      PreservationJumpRet(SigmaH, D, d, j, Phi, phi, phi', b');
}

lemma PreservationBlock(SigmaH: Sigma, D: Delta, d: delta, b: block, Phi: Phi, phi: phi, phi': phi, b': block)
  requires TypeProgram(SigmaH, D, d)
  requires TypeBlock(D, SigmaH, b, Phi)
  requires ValidStack(D, phi)
  requires SubPhi(Phi, TypePhi(D, phi))
  requires StepBlock(d, b, phi, phi', b')
  ensures  TypeBlock(D, SigmaH, b', TypePhi(D, phi'))
{
  var (cs, j) := b;
  match cs
    case Cons(c, cs) =>
      var s    := phi[0].1;
      var PhiR := Phi.out[0].0;
      var S    := Phi.out[0].1;
      var s'   := phi'[0].1;
      var S'   := TypeCommand(c, S).FromJust;
      var Phi' := MkPhi([(PhiR, S')] + Phi.out[1..]);
      PreservationCommand(c, s, S, s');
      TypeBlockExpansion(D, SigmaH, b', Phi', TypePhi(D, phi'));
    case Nil =>
      if j != halt {
        PreservationJump(SigmaH, D, d, j, Phi, phi, phi', b');
      }
}
