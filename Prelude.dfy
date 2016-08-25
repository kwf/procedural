// Stuff I would want from a standard library

function method Absurd<A>(): A
  requires false
{
  Absurd()
}

function method Fst<A,B>(p: (A,B)): A { p.0 }
function method Snd<A,B>(p: (A,B)): B { p.1 }

datatype List<A> = Cons(Head: A, Tail: List<A>) | Nil

function method SeqFromList<A>(xs: List<A>): seq<A>
{
  match xs
    case Nil => []
    case Cons(x, xs) =>
      [x] + SeqFromList(xs)
}

function method Length(xs: List): nat {
  match xs
    case Nil          => 0
    case Cons(_, xs') => 1 + Length(xs')
}

lemma {:induction xs} SmallerThanList<A>(x: A, xs: List<A>)
  requires x in Elements(xs)
  ensures x < xs
{
}

lemma AllSmallerThanList<A>(xs: List<A>)
  ensures forall x :: x in Elements(xs) ==> x < xs
{
  forall x | x in Elements(xs) {
    SmallerThanList(x, xs);
  }
}

function method MapList<A,B>(f: A -> B, xs: List<A>): List<B>
  requires forall x :: f.reads(x) == {}
  requires forall x :: x in Elements(xs) ==> f.requires(x)
  ensures Length(xs) == Length(MapList(f, xs))
{
  match xs
    case Nil => Nil
    case Cons(x, xs') => Cons(f(x), MapList(f, xs'))
}

function method MapFromList<A, B>(pairs: List<(A, B)>): map<A,B> {
  Foldr(map[],
    ((ab: (A, B), m: map<A,B>) =>
    var (a, b) := ab;
    m[a := b]),
      pairs)
}

function method Elements<A>(xs: List<A>): set<A>
{
  Foldr({}, ((x, s) => {x} + s), xs)
}

predicate method NoDuplicates<A(==)>(xs: List<A>) {
  |Elements(xs)| == Length(xs)
}

function method {:fuel (Length<A>), 3} {:fuel (Length<B>), 3}
ZipWith<A,B,C>(f: (A, B) -> C, xs: List<A>, ys: List<B>): List<C>
  requires forall x, y :: f.reads(x, y) == {}
  requires forall x, y :: x in Elements(xs) && y in Elements(ys) ==> f.requires(x, y)
    requires Length(xs) == Length(ys)
    ensures  Length(ZipWith(f, xs, ys)) == Length(xs) == Length(ys)
{
  match (xs, ys)
    case (Nil, Nil) => Nil
    case (Cons(x, xs'), Cons(y, ys')) => Cons(f(x, y), ZipWith(f, xs', ys'))
}

function method Zip<A,B>(xs: List<A>, ys: List<B>): List<(A,B)>
  requires Length(xs) == Length(ys)
  ensures  Length(Zip(xs, ys)) == Length(xs) == Length(ys)
{
  ZipWith((x,y) => (x,y), xs, ys)
}

function method Foldr<A, B>(b: B, k: (A, B) -> B, xs: List<A>): B
  requires forall x, y :: k.reads(x, y) == {}
  requires forall x, y :: k.requires(x, y)
  decreases xs
{
  match xs
    case Nil => b
    case Cons(x, xs') => k(x, Foldr(b, k, xs'))
}

predicate method All<A>(p: A -> bool, xs: List<A>)
  requires forall x :: p.reads(x) == {}
  requires forall x :: x in Elements(xs) ==> p.requires(x)
{
  Foldr(true, (x, y) => x && y, MapList(p, xs))
}

predicate method Any<A>(p: A -> bool, xs: List<A>)
  requires forall x :: p.reads(x) == {}
  requires forall x :: x in Elements(xs) ==> p.requires(x)
{
  Foldr(false, (x, y) => x || y, MapList(p, xs))
}

predicate method And(xs: List<bool>) {
  All(x => x, xs)
}

predicate method Or(xs: List<bool>) {
  Any(x => x, xs)
}

function method Union<A>(xs: List<set<A>>): set<A> {
  Foldr({}, ((x, y) => x + y), xs)
}

datatype Maybe<A> = Just(FromJust: A) | Nothing

function method MapMaybe<A,B>(x: Maybe<A>, f: A -> B): Maybe<B>
  requires forall x :: f.reads(x) == {}
  requires forall y :: x == Just(y) ==> f.requires(y)
{
  match x
    case Nothing => Nothing
    case Just(x) => Just(f(x))
}

function method BindMaybe<A,B>(x: Maybe<A>, f: A -> Maybe<B>): Maybe<B>
  requires forall x :: f.reads(x) == {}
  requires forall y :: x == Just(y) ==> f.requires(y)
{
  match x
    case Nothing => Nothing
    case Just(x) => f(x)
}

function method IsJust<A>(x: Maybe<A>): bool
  ensures (exists y :: x == Just(y)) <==> IsJust(x)
{
  match x
    case Just(_) => true
    case Nothing => false
}

datatype Either<A,B> = Left(A) | Right(B)

function method Either<A,B,R>(f: A -> R, g: B -> R, e: Either<A,B>): R
  requires forall a :: f.reads(a) == {}
  requires forall b :: g.reads(b) == {}
  requires forall a :: e == Left(a)  ==> f.requires(a)
  requires forall b :: e == Right(b) ==> g.requires(b)
{
  match e
    case Left(l)  => f(l)
    case Right(r) => g(r)
}

function method Lefts<A,B>(es: List<Either<A,B>>): List<A> {
  match es
    case Nil                 => Nil
    case Cons(Left(l),  es') => Cons(l, Lefts(es'))
    case Cons(Right(_), es') => Lefts(es')
}

function method Rights<A,B>(es: List<Either<A,B>>): List<B> {
  match es
    case Nil                 => Nil
    case Cons(Left(_),  es') => Rights(es')
    case Cons(Right(r), es') => Cons(r, Rights(es'))
}

function method Nth<A>(n: nat, xs: List<A>): A
  requires n < Length(xs)
  ensures Nth(n, xs) < xs
{
  match xs
    case Cons(x, xs) =>
      if 0 < n then Nth(n - 1, xs) else x
}

lemma NthProperties<A>(xs: List<A>)
  ensures xs != Nil ==> Nth(0, xs) == xs.Head && forall i | 0 <= i < Length(xs.Tail) :: Nth(i, xs.Tail) == Nth(i+1, xs)
{
  match xs
  case Nil =>
  case Cons(h, xs') => assert Nth(0, xs) == h;
}

lemma NthExtensionality<A>(xs: List<A>, ys: List<A>)
  requires Length(xs) == Length(ys)
  requires forall i | 0 <= i < Length(xs) :: Nth(i, xs) == Nth(i, ys)
  ensures xs == ys
{
  NthProperties(xs);
}

function method ReplaceNth<A>(n: nat, xs: List<A>, a: A): List<A>
  requires n < Length(xs)
{
  match xs
    case Cons(x, xs') =>
      if n == 0 then Cons(a, xs') else Cons(x, ReplaceNth(n-1, xs', a))
}

function method Take<A>(n: nat, xs: List<A>): List<A>
{
  if n != 0
     then match xs
       case Nil => Nil
       case Cons(x, xs) => Cons(x, Take(n - 1, xs))
     else Nil
}

lemma TakeLength<A>(n: nat, xs: List<A>)
  ensures Length(Take(n, xs)) <= n
  ensures Length(Take(n, xs)) == n || Length(Take(n, xs)) == Length(xs)
{
}

lemma NthTake<A>(n: nat, k: nat, xs: List<A>)
  requires n < k <= Length(xs)
  ensures (TakeLength(k, xs); Nth(n, Take(k, xs)) == Nth(n, xs))
{
  if n == 0 {
    assert Nth(n, Take(k, xs)) == Take(k, xs).Head;
  } else {
    NthTake(n-1, k-1, xs);
    TakeLength(k, xs);
  }
}

function method Drop<A>(n: nat, xs: List<A>): List<A>
{
  if n != 0
     then match xs
        case Nil => Nil
        case Cons(_, xs) => Drop(n - 1, xs)
     else xs
}

function method Append<A>(xs: List<A>, ys: List<A>): List<A>
  ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
{
  match xs
    case Nil => ys
    case Cons(x, xs) => Cons(x, Append(xs, ys))
}

lemma NthAppend<A>(i: nat, xs: List<A>, ys: List<A>)
  requires 0 <= i < Length(Append(xs, ys))
  ensures i < Length(xs) ==> Nth(i, Append(xs, ys)) == Nth(i, xs)
  ensures Length(xs) <= i ==> Nth(i, Append(xs, ys)) == Nth(i - Length(xs), ys)
{
}

// function method MapSeq<A,B>(f: A -> B, xs: seq<A>): seq<B>
//   requires forall a :: f.reads(a) == {}
//   requires forall a | a in xs :: f.requires(a)
//   ensures |xs| == |MapSeq(f, xs)|
//   ensures forall i | 0 <= i < |xs| :: MapSeq(f, xs)[i] == f(xs[i])
// {
//   if |xs| == 0 then [] else
//     var x  := xs[0];
//     var xs := xs[1..];
//     [f(x)] + MapSeq(f, xs)
// }

// lemma MapSeqHomomorphism<A,B>(f: A -> B, xs: seq<A>, ys: seq<A>)
//   requires forall a :: f.reads(a) == {}
//   requires forall a | a in xs :: f.requires(a)
//   requires forall a | a in ys :: f.requires(a)
//   ensures MapSeq(f, xs) + MapSeq(f, ys) == MapSeq(f, xs + ys)
// {
//   if |xs| == 0 {
//     assert MapSeq(f, []) + MapSeq(f, ys) == MapSeq(f, ys);
//   } else {
//     var xs := xs[1..];
//     MapSeqHomomorphism(f, xs, ys);
//   }
// }

// lemma MapSeqSplit<A,B>(n: nat, f: A -> B, xs: seq<A>)
//   requires forall a :: f.reads(a) == {}
//   requires forall a | a in xs :: f.requires(a)
//   requires n < |xs|
//   ensures  MapSeq(f, xs)[..n] == MapSeq(f, xs[..n])
//   ensures  MapSeq(f, xs)[n..] == MapSeq(f, xs[n..])
// {
// }

// function method ZipSeq<A,B>(xs: seq<A>, ys: seq<B>): seq<(A, B)>
//   requires |xs| == |ys|
//   ensures  |xs| == |ys| == |ZipSeq(xs, ys)|
//   ensures forall i | 0 <= i < |xs| :: ZipSeq(xs, ys)[i] == (xs[i], ys[i])
// {
//   if |xs| == 0 then [] else
//     var x  := xs[0];
//     var y  := ys[0];
//     var xs := xs[1..];
//     var ys := ys[1..];
//     [(x, y)] + ZipSeq(xs, ys)
// }
