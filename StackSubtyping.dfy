
include "StackSyntax.dfy"

predicate method Prefix<A(==)>(s: List<A>, t: List<A>) {
  match s
  case Nil => true
  case Cons(h, s') => t.Cons? && t.Head == h && Prefix(s', t.Tail)
}

lemma PrefixReflexive<A(==)>(s: List<A>)
  ensures Prefix(s, s)
{
}

lemma PrefixAntisymmetric<A(==)>(s: List<A>, t: List<A>)
  requires Prefix(s, t)
  requires Prefix(t, s)
  ensures s == t
{
}

lemma PrefixTransitive<A(==)>(r: List<A>, s: List<A>, t: List<A>)
  requires Prefix(r, s)
  requires Prefix(s, t)
  ensures  Prefix(r, t)
{
}

// The next two lemmas give an equivalent formulation of Prefix in terms of Length and Nth:

lemma PrefixProperty<A(==)>(s: List<A>, t: List<A>)
  requires Prefix(s, t)
  ensures Length(s) <= Length(t) &&
          forall i | 0 <= i < Length(s) :: Nth(i, s) == Nth(i, t)
{
}

lemma PrefixProperty'<A(==)>(s: List<A>, t: List<A>)
  requires Length(s) <= Length(t) &&
           forall i | 0 <= i < Length(s) :: Nth(i, s) == Nth(i, t)
  ensures Prefix(s, t)
{
  match s
  case Nil =>
  case Cons(h, s') =>
    NthProperties(s);
    PrefixProperty'(s', t.Tail);
}

// other lemmas about Prefix

lemma PrefixReplace<A>(n: nat, s: List<A>, t: List<A>, a: A)
  requires Prefix(s, t) && n < Length(s)
  ensures (PrefixProperty(s, t);
           Prefix(ReplaceNth(n, s, a), ReplaceNth(n, t, a)))
{
  if n == 0 {
    assert ReplaceNth(n, t, a) == Cons(a, t.Tail);
  } else {
    PrefixProperty(s.Tail, t.Tail);
  }
}

lemma PrefixSplit<A(==)>(n: nat, xs: List<A>, ys: List<A>)
  requires n <= Length(xs)
  requires Prefix(xs, ys)
  ensures  Prefix(Drop(n, xs), Drop(n, ys))
  ensures  Take(n, xs) == Take(n, ys) && Prefix(Take(n, xs), Take(n, ys))
{
}

predicate method SubPhiSigned(p: bool, s: Phi, t: Phi)
  decreases s, t
{
  var s, t := s.out, t.out;
  (if p then Length(s) <= Length(t)
        else Length(t) <= Length(s)) &&
  forall i | 0 <= i < Length(if p then s else t) ::
    SubPhiSigned(!p, Nth(i, s).0, Nth(i, t).0) &&
    if p then Prefix(Nth(i, s).1, Nth(i, t).1)
         else Prefix(Nth(i, t).1, Nth(i, s).1)
}

predicate method SubPhi(s: Phi, t: Phi)
{
  SubPhiSigned(true, s, t) && SubPhiSigned(false, t, s)
}

lemma SubPhiReflexiveSigned(p: bool, s: Phi)
  ensures SubPhiSigned(p, s, s) && SubPhiSigned(!p, s, s)
  decreases s
{
  var s := s.out;
  forall i | 0 <= i < Length(s)
    ensures SubPhiSigned(!p, Nth(i, s).0, Nth(i, s).0)
    ensures Prefix(Nth(i, s).1, Nth(i, s).1)
  {
    SubPhiReflexiveSigned(!p, Nth(i, s).0);
    PrefixReflexive(Nth(i, s).1);
  }
}

lemma SubPhiReflexive(s: Phi)
  ensures SubPhi(s, s)
{
  SubPhiReflexiveSigned(true, s);
}

lemma SubPhiAntisymmetricSigned(p: bool, s: Phi, t: Phi)
  decreases s, t
  requires SubPhiSigned(p, s, t)
  requires SubPhiSigned(!p, s, t)
  ensures  s == t
{
  var s, t := s.out, t.out;
  forall i | 0 <= i < Length(s)
    ensures Nth(i, s) == Nth(i, t)
  {
    PrefixAntisymmetric(Nth(i, s).1, Nth(i, t).1);
    SubPhiAntisymmetricSigned(p, Nth(i, s).0, Nth(i, t).0);
  }
  NthExtensionality(s, t);
}

lemma SubPhiAntisymmetric(s: Phi, t: Phi)
  decreases s, t
  requires SubPhi(s, t)
  requires SubPhi(t, s)
  ensures  s == t
{
  SubPhiAntisymmetricSigned(true, s, t);
}

lemma SubPhiTransitiveSigned(p: bool, r: Phi, s: Phi, t: Phi)
  decreases s
  requires SubPhiSigned(p, r, s)
  requires SubPhiSigned(p, s, t)
  ensures  SubPhiSigned(p, r, t)
{
  var r, s, t := r.out, s.out, t.out;
  forall i | 0 <= i < Length(if p then r else t)
    ensures SubPhiSigned(!p, Nth(i, r).0, Nth(i, t).0)
    ensures if p then Prefix(Nth(i, r).1, Nth(i, t).1)
                 else Prefix(Nth(i, t).1, Nth(i, r).1)
  {
    if p {
      PrefixTransitive(Nth(i, r).1, Nth(i, s).1, Nth(i, t).1);
    } else {
      PrefixTransitive(Nth(i, t).1, Nth(i, s).1, Nth(i, r).1);
    }
    SubPhiTransitiveSigned(!p, Nth(i, r).0, Nth(i, s).0, Nth(i, t).0);
  }
}

lemma SubPhiTransitive(r: Phi, s: Phi, t: Phi)
  requires SubPhi(r, s)
  requires SubPhi(s, t)
  ensures  SubPhi(r, t)
{
  SubPhiTransitiveSigned(true, r, s, t);
  SubPhiTransitiveSigned(false, t, s, r);
}

lemma SubPhiAllContravariantSigned(p: bool, s: Phi, t: Phi)
  decreases s, t
  requires SubPhiSigned(p, s, t)
  ensures  forall i | 0 <= i < Length(if p then s.out else t.out) ::
             SubPhiSigned(!p, Nth(i, s.out).0, Nth(i, t.out).0)
{
  var (s, t) := (s.out, t.out);
  forall i | 0 <= i < Length(if p then s else t)
    ensures SubPhiSigned(!p, Nth(i, s).0, Nth(i, t).0)
  {
    SubPhiAllContravariantSigned(!p, Nth(i, s).0, Nth(i, t).0);
  }
}

lemma SubPhiAllContravariant(s: Phi, t: Phi)
  requires SubPhi(s, t)
  ensures  forall i | 0 <= i < Length(s.out) :: SubPhi(Nth(i, t.out).0, Nth(i, s.out).0)
{
  SubPhiAllContravariantSigned(true, s, t);
  forall i | 0 <= i < Length(s.out) {
    SubPhiFlip(Nth(i, t.out).0, Nth(i, s.out).0);
  }
}

lemma SubPhiFlipSigned(p: bool, s: Phi, t: Phi)
  decreases s, t
  requires SubPhiSigned(p,  s, t)
  ensures  SubPhiSigned(!p, t, s)
{
  var (s, t) := (s.out, t.out);
  forall i | 0 <= i < Length(if p then s else t)
    ensures SubPhiSigned(p, Nth(i, t).0, Nth(i, s).0)
  {
    SubPhiFlipSigned(!p, Nth(i, s).0, Nth(i, t).0);
  }
}

lemma SubPhiFlip(s: Phi, t: Phi)
  requires SubPhiSigned(true, s, t) || SubPhiSigned(false, t, s)
  ensures  SubPhi(s, t)
{
  if SubPhiSigned(true, s, t) {
    SubPhiFlipSigned(true, s, t);
  } else {
    SubPhiFlipSigned(false, t, s);
  }
}

lemma SubPhiSplit(n: nat, Phi1: Phi, Phi2: Phi)
  requires n < Length(Phi1.out)
  requires SubPhi(Phi1, Phi2)
  ensures  SubPhi(MkPhi(Take(n, Phi1.out)), MkPhi(Take(n, Phi2.out)))
  ensures  SubPhi(MkPhi(Drop(n, Phi1.out)), MkPhi(Drop(n, Phi2.out)))
{
  if n == 0 {
  } else {
    var s', t' := Phi1.out.Tail, Phi2.out.Tail;
    forall i | 0 <= i < Length(s')
      ensures SubPhiSigned(false, Nth(i, s').0, Nth(i, t').0)
      ensures Prefix(Nth(i, s').1, Nth(i, t').1)
      ensures SubPhiSigned(true, Nth(i, t').0, Nth(i, s').0)
      ensures Prefix(Nth(i, s').1, Nth(i, t').1)
    {
      assert Nth(i, s') == Nth(i+1, Phi1.out);
    }

    SubPhiSplit(n-1, MkPhi(Phi1.out.Tail), MkPhi(Phi2.out.Tail));

    var m, k := Take(n, Phi1.out), Take(n, Phi2.out);
    TakeLength(n, Phi1.out);
    forall i | 0 <= i < Length(m)
      ensures SubPhiSigned(false, Nth(i, m).0, Nth(i, k).0)
      ensures Prefix(Nth(i, m).1, Nth(i, k).1)
      ensures SubPhiSigned(true, Nth(i, k).0, Nth(i, m).0)
      ensures Prefix(Nth(i, m).1, Nth(i, k).1)
    {
      NthTake(i, n, Phi1.out);
    }
  }
}

lemma SubPhiJoin(Phi1a: Phi, Phi1b: Phi, Phi2a: Phi, Phi2b: Phi)
  requires SubPhi(Phi1a, Phi2a)
  requires SubPhi(Phi1b, Phi2b)
  requires Length(Phi1a.out) == Length(Phi2a.out)
  ensures  SubPhi(MkPhi(Append(Phi1a.out, Phi1b.out)), MkPhi(Append(Phi2a.out, Phi2b.out)))
{
}
