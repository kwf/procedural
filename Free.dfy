function method Max(x: int, y: int): int
{
  if x > y then x else y
}

predicate BoundedAboveBy(a: int, s: set<int>) {
  forall e | e in s :: e < a
}

function Fresh(s: set<int>): int
  ensures BoundedAboveBy(Fresh(s), s)
{
  if |s| == 0 then 0 else
    var x :| x in s;
    var y := Fresh(s - {x});
    BoundedAboveExpansion(Max(x, y) + 1, x, s - {x});
    Max(x, y) + 1
}

lemma BoundedAboveExpansion(a: int, e: int, s: set<int>)
  requires BoundedAboveBy(a, s)
  requires e < a
  ensures  BoundedAboveBy(a, s + {e})
{
}

predicate Reflexive<A>(f: (A, A) -> bool)
  requires forall a, b :: f.requires(a, b) && f.reads(a, b) == {}
{
  forall a :: f(a, a)
}

predicate Antisymmetric<A>(f: (A, A) -> bool)
  requires forall a, b :: f.requires(a, b) && f.reads(a, b) == {}
{
  forall a, b :: f(a, b) && f(b, a) ==> a == b
}

predicate Transitive<A>(f: (A, A) -> bool)
  requires forall a, b :: f.requires(a, b) && f.reads(a, b) == {}
{
  forall a, b, c :: f(a, b) && f(b, c) ==> f(a, c)
}

predicate PartialOrder<A>(f: (A, A) -> bool)
  requires forall a, b :: f.requires(a, b) && f.reads(a, b) == {}
{
  Reflexive(f) && Antisymmetric(f) && Transitive(f)
}

predicate Trichotomy<A>(f: (A, A) -> bool)
  requires forall a, b :: f.requires(a, b) && f.reads(a, b) == {}
{
  forall a, b :: f(a, b) || f(b, a)
}

predicate TotalOrder<A>(f: (A, A) -> bool)
  requires forall a, b :: f.requires(a, b) && f.reads(a, b) == {}
{
  PartialOrder(f) && Trichotomy(f)
}

function MaxWith<A>(f: (A, A) -> bool, x: A, y: A): A
  requires forall a, b :: f.requires(a, b) && f.reads(a, b) == {}
  requires TotalOrder(f)
  ensures  f(x, MaxWith(f, x, y))
  ensures  f(y, MaxWith(f, x, y))
  ensures  MaxWith(f, x, y) == x || MaxWith(f, x, y) == y
{
  if f(x, y) then y else x
}

predicate BoundedAboveWith<A>(f: (A, A) -> bool, a: A, s: set<A>)
  requires forall a, b :: f.requires(a, b) && f.reads(a, b) == {}
  requires TotalOrder(f)
{
  forall e | e in s :: f(e, a) && e != a
}

lemma BoundedAboveExpansionWith<A>(f: (A, A) -> bool, a: A, e: A, s: set<A>)
  requires forall a, b :: f.requires(a, b) && f.reads(a, b) == {}
  requires TotalOrder(f)
  requires BoundedAboveWith(f, a, s)
  requires f(e, a) && e != a
  ensures  BoundedAboveWith(f, a, s + {e})
{
}

function FreshWith<A>(compare: (A, A) -> bool, succ: A -> A, base: A, s: set<A>): A
  requires forall a, b :: compare.requires(a, b) && compare.reads(a, b) == {}
  requires forall a :: succ.requires(a) && succ.reads(a) == {}
  requires forall a :: compare(a, succ(a)) && a != succ(a)
  requires TotalOrder(compare)
  ensures  BoundedAboveWith(compare, FreshWith(compare, succ, base, s), s)
{
  if |s| == 0 then base else
  var x :| x in s;
  var y := FreshWith(compare, succ, base, s - {x});
  BoundedAboveExpansionWith(compare, succ(MaxWith(compare, x, y)), x, s - {x});
  succ(MaxWith(compare, x, y))
}

function Fresh'(s: set<int>): int
  ensures BoundedAboveBy(Fresh'(s), s)
{
  FreshWith((x, y) => x <= y, x => x + 1, 0, s)
}
