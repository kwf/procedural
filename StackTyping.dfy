
include "Prelude.dfy"
include "Common.dfy"
include "StackSyntax.dfy"
include "StackSubtyping.dfy"

function method Split<A>(n: nat, v: List<A>): (List<A>, List<A>)
  requires n <= Length(v)
{
  (Take(n, v), Drop(n, v))
}

function method Uncons<A>(v: List<A>): (A, List<A>)
  requires 0 < Length(v)
  ensures Length(Uncons(v).1) == Length(v) - 1
{
  (v.Head, v.Tail)
}

function method TypeValue(v: value): Type {
  match v
    case integer(_) => Int
    case boolean(_) => Bool
    case unit       => Unit
}

function method TypeSigma(s: sigma): Sigma {
  MapList(TypeValue, s)
}

predicate method ValidStack(D: Delta, phi: phi) {
  forall frame | frame in Elements(phi) :: frame.0 in D
}

function method TypeFrame(D: Delta): ((nu, sigma)) -> (Phi, Sigma) {
  (frame: (nu, sigma)) requires frame.0 in D =>
    (D[frame.0], TypeSigma(frame.1))
}

function method TypePhi(D: Delta, phi: phi): Phi
  requires ValidStack(D, phi)
{
  MkPhi(MapList(TypeFrame(D), phi))
}

function method TypeOperation(o: operation): (Sigma, Type) {
  match o
    case not => (Cons(Bool, Nil), Bool)
    case read(t) => (Nil, t)
    case printf(format) => (Lefts(format), Unit)
    case const(v) =>
      match v {
        case integer(_) => (Nil, Int)
        case boolean(_) => (Nil, Bool)
        case unit       => (Nil, Unit)
      }
    case binary(o) =>
      match o
        case BoolOp(_) => (Cons(Bool, Cons(Bool, Nil)), Bool)
        case RelOp(_)  => (Cons(Int, Cons(Int, Nil)),   Bool)
        case MathOp(_) => (Cons(Int, Cons(Int, Nil)),   Int)
}

function method TypeCommand(c: command, S: Sigma): Maybe<Sigma> {
  match c
    case store(n) =>
      if n < Length(S)
        then Just(ReplaceNth(n, S, S.Head).Tail)
        else Nothing
    case load(n) =>
      if n < Length(S)
        then Just(Cons(Nth(n, S), S))
        else Nothing
    case pop(n) =>
      if n <= Length(S)
        then Just(Drop(n, S))
        else Nothing
    case apply(n, o) =>
      if n <= Length(S)
        then var (S', S'') := Split(n, S);
             var (So, t) := TypeOperation(o);
             if S' == So
               then Just(Cons(t, S''))
               else Nothing
        else Nothing
}

function method TypeCommands(cs: List<command>, S: Sigma): Maybe<Sigma>
  decreases cs
{
  match cs
    case Nil => Just(S)
    case Cons(c, cs) =>
      BindMaybe(TypeCommand(c, S), S' => TypeCommands(cs, S'))
}

predicate method TypeJump(D: Delta, SigmaH: Sigma, j: jump, P: Phi) {
  match j
    case goto(n) =>
      n in D && SubPhi(D[n], P)
    case halt =>
      P.out != Nil &&
      var ((PhiR', SigmaH'), Phi_rest) := Uncons(P.out);
      Prefix(SigmaH, SigmaH')
    case branch(n1, n2) =>
      P.out != Nil &&
      n1 in D && n2 in D &&
      var ((PhiR, S), Phi_rest) := Uncons(P.out);
      S != Nil &&
      var (t, S') := Uncons(S);
      t == Bool &&
      var P' := MkPhi(Cons((PhiR, S'), Phi_rest));
      SubPhi(D[n1], P') && SubPhi(D[n2], P')
    case call(n, nJ, nR) =>
      P.out != Nil &&
      nJ in D && nR in D &&
      var ((PhiR, S), Phi_rest) := Uncons(P.out);
      n < Length(S) &&
      var (S1, S2) := Split(n, S);
      SubPhi(D[nJ], MkPhi(Cons((D[nR], S1), Cons((PhiR, S2), Phi_rest))))
    case ret(n) =>
      Length(P.out) >= 2 &&
      var ((PhiR, S), Phi_rest) := Uncons(P.out);
      var ((PhiR_origin, S_origin), Phi_rest_rest)  := Uncons(Phi_rest);
      n <= Length(S) &&
      var (S_check, _) := Split(n, S);
      SubPhi(PhiR, MkPhi(Cons((PhiR_origin, Append(S_check, S_origin)), Phi_rest_rest)))
}

predicate method TypeBlock(D: Delta, SigmaH: Sigma, b: block, P: Phi) {
  var (cs, j) := b;
  P.out != Nil &&
  var ((PhiR, S), P_rest) := Uncons(P.out);
  match TypeCommands(cs, S)
    case Nothing => false
    case Just(S_final) => TypeJump(D, SigmaH, j, MkPhi(Cons((PhiR, S_final), P_rest)))
}

predicate TypeProgram(SigmaH: Sigma, D: Delta, d: delta) {
  (forall i :: i in D <==> i in d) &&
  forall i :: i in D ==> TypeBlock(D, SigmaH, d[i], D[i])
}

lemma TypeCommandExpansion(c: command, S1: Sigma, S1_out: Sigma, S2: Sigma)
  requires Prefix(S1, S2)
  requires TypeCommand(c, S1) == Just(S1_out)
  ensures  exists S2_out :: TypeCommand(c, S2) == Just(S2_out)
{
  PrefixProperty(S1, S2);
  match c
    case store(n) =>
    case load(n) =>
    case pop(n) =>
    case apply(n, o) =>
      PrefixSplit(n, S1, S2);
}

lemma TypeCommandPrefixPreservation(c: command, S1: Sigma, S2: Sigma, S1': Sigma, S2': Sigma)
  requires Prefix(S1, S2)
  requires TypeCommand(c, S1) == Just(S1')
  requires TypeCommand(c, S2) == Just(S2')
  ensures  Prefix(S1', S2')
{
  PrefixProperty(S1, S2);
  match c
    case store(n) =>
      PrefixReplace(n, S1, S2, S1.Head);
    case load(n) =>
    case pop(n) =>
      PrefixSplit(n, S1, S2);
    case apply(n, o) =>
      PrefixSplit(n, S1, S2);
}

lemma TypeCommandsExpansion(cs: List<command>, S1: Sigma, S1_out: Sigma, S2: Sigma)
  requires Prefix(S1, S2)
  requires TypeCommands(cs, S1) == Just(S1_out)
  ensures  exists S2_out :: TypeCommands(cs, S2) == Just(S2_out) && Prefix(S1_out, S2_out)
{
  match cs
    case Nil =>
    case Cons(c, cs') =>
      var S1' := TypeCommand(c, S1).FromJust;

      TypeCommandExpansion(c, S1, S1', S2);
      var S2' := TypeCommand(c, S2).FromJust;

      TypeCommandPrefixPreservation(c, S1, S2, S1', S2');
      TypeCommandsExpansion(cs', S1', S1_out, S2');
}

lemma TypeBlockExpansion(D: Delta, SigmaH: Sigma, b: block, P: Phi, P': Phi)
  requires TypeBlock(D, SigmaH, b, P)
  requires SubPhi(P, P')
  ensures  TypeBlock(D, SigmaH, b, P')
{
  var (cs, j) := b;
  var ((PhiR,  S),  Phi_rest)  := Uncons(P.out);
  var ((PhiR', S'), Phi_rest') := Uncons(P'.out);
  match TypeCommands(cs, S)
    case Just(S_final) =>
      TypeCommandsExpansion(cs, S, S_final, S');
      var S_final' := TypeCommands(cs, S').FromJust;
      match j
        case goto(n) =>
          var Phi_final  := MkPhi(Cons((PhiR,  S_final),  Phi_rest));
          var Phi_final' := MkPhi(Cons((PhiR', S_final'), Phi_rest'));
          SubPhiTransitive(D[n], Phi_final, Phi_final');
        case halt =>
        case branch(n1, n2) =>
          var (_, S_final)  := Uncons(S_final);
          var (_, S_final') := Uncons(S_final');
          var Phi_final  := MkPhi(Cons((PhiR,  S_final),  Phi_rest));
          var Phi_final' := MkPhi(Cons((PhiR', S_final'), Phi_rest'));
          SubPhiTransitive(D[n1], Phi_final, Phi_final');
          SubPhiTransitive(D[n2], Phi_final, Phi_final');
        case call(n, nJ, nR) =>
          var (S1,  S2)  := Split(n, S_final);
          var (S1', S2') := Split(n, S_final');
          var Phi_final  := Cons((D[nR], S1),  Cons((PhiR,  S2),  Phi_rest));
          var Phi_final' := Cons((D[nR], S1'), Cons((PhiR', S2'), Phi_rest'));
          SubPhiReflexive(D[nR]);
          SubPhiTransitive(D[nJ], MkPhi(Phi_final), MkPhi(Phi_final'));
        case ret(n) =>
          var (S_check,  _) := Split(n, S_final);
          var (S_check', _) := Split(n, S_final');
          var ((PhiR_origin,  S_origin),  Phi_rest_rest)  := Uncons(Phi_rest);
          var ((PhiR_origin', S_origin'), Phi_rest_rest') := Uncons(Phi_rest');
          var Phi_final  :=  MkPhi(Cons((PhiR_origin,  Append(S_check,  S_origin)),  Phi_rest_rest));
          var Phi_final' :=  MkPhi(Cons((PhiR_origin', Append(S_check', S_origin')), Phi_rest_rest'));
          SubPhiTransitive(PhiR, Phi_final, Phi_final');
          SubPhiAllContravariant(P, P');
          SubPhiTransitive(PhiR', PhiR, Phi_final');
}

lemma Example()
  ensures TypeBlock(map[0 := MkPhi(Nil)], Nil, (Nil, goto(0)), MkPhi(Cons((MkPhi(Nil), Nil), Nil)))
{
}


// What I want:
//    - pattern matching on sequences using literal and slice notation
//    - non-linear patterns?
//    - maybe something like "if pat := exp then ... else ..."? or case defaults?
//    From these, we get the ability to succinctly match against structure that we need.
