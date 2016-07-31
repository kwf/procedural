
include "StackSyntax.dfy"

predicate method Prefix<A(==)>(s: seq<A>, t: seq<A>) {
  |s| <= |t| &&
    forall i | 0 <= i < |s| :: s[i] == t[i]
}

lemma PrefixReflexive<A(==)>(s: seq<A>)
  ensures Prefix(s, s)
{
}

lemma PrefixAntisymmetric<A(==)>(s: seq<A>, t: seq<A>)
  requires Prefix(s, t)
  requires Prefix(t, s)
  ensures s == t
{
}

lemma PrefixTransitive<A(==)>(r: seq<A>, s: seq<A>, t: seq<A>)
  requires Prefix(r, s)
  requires Prefix(s, t)
  ensures  Prefix(r, t)
{
}

lemma PrefixSplit<A(==)>(n: nat, xs: seq<A>, ys: seq<A>)
  requires n < |xs|
  requires Prefix(xs, ys)
  ensures  Prefix(xs[..n], ys[..n])
  ensures  Prefix(xs[n..], ys[n..])
{
}

predicate method SubPhiSigned(p: bool, s: Phi, t: Phi)
  decreases s, t
{
  var s, t := s.out, t.out;
  (if p then |s| <= |t|
        else |t| <= |s|) &&
  forall i | 0 <= i < |if p then s else t| ::
    SubPhiSigned(!p, s[i].0, t[i].0) &&
    if p then Prefix(s[i].1, t[i].1)
         else Prefix(t[i].1, s[i].1)
}

predicate method SubPhi(s: Phi, t: Phi)
{
  SubPhiSigned(true, s, t) && SubPhiSigned(false, t, s)
}

lemma SubPhiReflexiveSigned(p: bool, s: Phi)
  ensures SubPhiSigned(p, s, s) && SubPhiSigned(!p, s, s)
{
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
  var (s, t) := (s.out, t.out);
  forall i | 0 <= i < |s|
    ensures s[i] == t[i]
  {
    PrefixAntisymmetric(s[i].1, t[i].1);
    SubPhiAntisymmetricSigned(p, s[i].0, t[i].0);
  }
  assert s == t;
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
  var (r, s, t) := (r.out, s.out, t.out);
  forall i | 0 <= i < |if p then r else t|
    ensures SubPhiSigned(!p, r[i].0, t[i].0);
  {
    if p {
      PrefixTransitive(r[i].1, s[i].1, t[i].1);
    } else {
      PrefixTransitive(t[i].1, s[i].1, r[i].1);
    }
    SubPhiTransitiveSigned(!p, r[i].0, s[i].0, t[i].0);
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
  ensures  forall i | 0 <= i < |if p then s.out else t.out| ::
             SubPhiSigned(!p, s.out[i].0, t.out[i].0)
{
  var (s, t) := (s.out, t.out);
  forall i | 0 <= i < |if p then s else t|
    ensures SubPhiSigned(!p, s[i].0, t[i].0)
  {
    SubPhiAllContravariantSigned(!p, s[i].0, t[i].0);
  }
}

lemma SubPhiAllContravariant(s: Phi, t: Phi)
  requires SubPhi(s, t)
  ensures  forall i | 0 <= i < |s.out| :: SubPhi(t.out[i].0, s.out[i].0)
{
  SubPhiAllContravariantSigned(true, s, t);
  forall i | 0 <= i < |s.out| {
    SubPhiFlip(t.out[i].0, s.out[i].0);
  }
}

lemma SubPhiFlipSigned(p: bool, s: Phi, t: Phi)
  decreases s, t
  requires SubPhiSigned(p,  s, t)
  ensures  SubPhiSigned(!p, t, s)
{
  var (s, t) := (s.out, t.out);
  forall i | 0 <= i < |if p then s else t|
    ensures SubPhiSigned(p, t[i].0, s[i].0)
  {
    SubPhiFlipSigned(!p, s[i].0, t[i].0);
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
  requires n < |Phi1.out|
  requires SubPhi(Phi1, Phi2)
  ensures  SubPhi(MkPhi(Phi1.out[..n]), MkPhi(Phi2.out[..n]))
  ensures  SubPhi(MkPhi(Phi1.out[n..]), MkPhi(Phi2.out[n..]))
{
}

lemma SubPhiJoin(Phi1a: Phi, Phi1b: Phi, Phi2a: Phi, Phi2b: Phi)
  requires SubPhi(Phi1a, Phi2a)
  requires SubPhi(Phi1b, Phi2b)
  requires |Phi1a.out| == |Phi2a.out|
  ensures  SubPhi(MkPhi(Phi1a.out + Phi1b.out), MkPhi(Phi2a.out + Phi2b.out))
{
}
