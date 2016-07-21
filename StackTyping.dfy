
include "Prelude.dfy"
include "Common.dfy"
include "StackSyntax.dfy"

function method TypeValue(v: value): Type {
  match v
    case integer(_) => Int
    case boolean(_) => Bool
    case unit       => Unit
}

function method TypeOperation(o: operation): (Sigma, Type) {
  match o
    case not => ([Bool], Bool)
    case read(t) => ([], t)
    case printf(format) => (SeqFromList(Lefts(format)), Unit)
    case const(v) =>
      match v {
        case integer(_) => ([], Int)
        case boolean(_) => ([], Bool)
        case unit       => ([], Unit)
      }
    case binary(o) =>
      match o
        case BoolOp(_) => ([Bool, Bool], Bool)
        case RelOp(_)  => ([Int, Int],   Bool)
        case MathOp(_) => ([Int, Int],   Int)
}

function method TypeCommand(c: command, S: Sigma): Maybe<Sigma> {
  match c
    case store(n) =>
      if n < |S| && S != []
        then Just(S[n := S[n]])
        else Nothing
    case load(n) =>
      if n < |S|
        then Just([S[n]] + S)
        else Nothing
    case pop(n) =>
      if n <= |S|
        then Just(S[|S| - n .. |S|])
        else Nothing
    case apply(n, o) =>
      if n <= |S|
        then var S'  := S[0 .. n];
             var S'' := S[n .. |S|];
             var (So, t) := TypeOperation(o);
             if S' == So
               then Just([t] + S'')
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

function method Split<A>(n: nat, v: seq<A>): (seq<A>, seq<A>)
  requires n <= |v|
  ensures var (xs, ys) := Split(n, v); |xs| == n && |ys| == |v| - n
{
  var xs := v[.. n];
  var ys := v[n ..];
  (xs, ys)
}

function method Uncons<A>(v: seq<A>): (A, seq<A>)
  requires 0 < |v|
  ensures |Uncons(v).1| == |v| - 1
{
  var (xs, ys) := Split(1, v);
  (xs[0], ys)
}

predicate method TypeJump(D: Delta, SigmaH: Sigma, j: jump, P: Phi) {
  match j
    case goto(n) =>
      n in D && P == D[n]
    case halt =>
      0 < |P.out| &&
      var ((PhiR', SigmaH'), Phi_rest) := Uncons(P.out);
      SigmaH' == SigmaH
    case branch(n1, n2) =>
      0 < |P.out| &&
      n1 in D && n2 in D &&
      var ((PhiR, S), Phi_rest) := Uncons(P.out);
      S != [] &&
      var (t, S') := Uncons(S);
      t == Bool &&
      var P' := Phi([(PhiR, S')] + Phi_rest);
      D[n1] == D[n2] == P'
    case call(n, nJ, nR) =>
      0 < |P.out| &&
      nJ in D && nR in D &&
      var ((PhiR, S), Phi_rest) := Uncons(P.out);
      n < |S| &&
      var (S1, S2) := Split(n, S);
      D[nJ] == Phi([(D[nR], S1), (PhiR, S2)] + Phi_rest)
    case ret(n) =>
      |P.out| >= 2 &&
      var ((Phi(PhiR_now), SS), Phi_rest) := Uncons(P.out);
      n <= |SS| &&
      var (S_check, S_nope) := Split(n, SS);
      var ((PhiR,  S),   Phi_rest')  := Uncons(Phi_rest);
      0 < |PhiR_now| &&
      var ((PhiR', SS'), Phi_rest'') := Uncons(PhiR_now);
      n <= |SS'| &&
      var (S_check', S') := Split(n, SS');
      S == S' &&
      S_check == S_check' &&
      PhiR == PhiR' &&
      Phi_rest' == Phi_rest''
}

predicate method TypeBlock(D: Delta, SigmaH: Sigma, b: block, P: Phi) {
  var (cs, j) := b;
  0 < |P.out| &&
  var ((PhiR, S), P_rest) := Uncons(P.out);
  match TypeCommands(cs, S)
    case Nothing => false
    case Just(S') => TypeJump(D, SigmaH, j, Phi([(PhiR, S')] + P_rest))
}

// What I want:
//    - pattern matching on sequences using literal and slice notation
//    - non-linear patterns?
//    - maybe something like "if pat := exp then ... else ..."? or case defaults?
//    From these, we get the ability to succinctly match against structure that we need.
