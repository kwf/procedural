
include "Prelude.dfy"
include "Common.dfy"
include "SourceSyntax.dfy"
include "StackSyntax.dfy"
include "Free.dfy"

function method Domain<A,B>(m: map<A,B>): set<A> {
  set k | k in m :: k
}

function method Remove<A,B>(k': A, m: map<A,B>): map<A,B> {
  map k | k in m && k != k' :: m[k]
}

function ShiftAway'(diff: nu, avoid: set<nu>, d: delta): delta
  decreases d
{
  if |d| == 0 then d else
  var nu :| nu in d;
  if nu in avoid
    then ShiftAway'(diff, avoid, Remove(nu, d))[nu + diff := PushAway(diff, avoid, d[nu])]
    else ShiftAway'(diff, avoid, Remove(nu, d))[nu        := PushAway(diff, avoid, d[nu])]
}

function PushName(diff: nu, avoid: set<nu>, nu: nu): nu
{
  if nu in avoid then nu + diff else nu
}

function PushAway(diff: nu, avoid: set<nu>, b: block): block
{
  var (cs, j) := b;
  (cs, if j.halt? || j.ret? then j
       else match j {
         case goto(nu) =>
           goto(PushName(diff, avoid, nu))
         case branch(nu1, nu2) =>
           branch(PushName(diff, avoid, nu1),
                  PushName(diff, avoid, nu2))
         case call(n, nuJ, nuR) =>
           call(n, PushName(diff, avoid, nuJ),
                   PushName(diff, avoid, nuR))
  })
}

function ShiftAway(avoid: set<nu>, d: delta): delta
{
  var diff := Fresh(Domain(d));
  ShiftAway'(diff, avoid, d)
}

type alignment = map<nu, int>

function CompileExpression(align: alignment, entry: nu, exit: nu, e: Expr): Maybe<delta>
{
  match e
    case Unit       => Just(map[entry := (Cons(apply(0, const(unit)),Nil),           goto(exit))])
    case False      => Just(map[entry := (Cons(apply(0, const(boolean(false))),Nil), goto(exit))])
    case True       => Just(map[entry := (Cons(apply(0, const(boolean(true))),Nil),  goto(exit))])
    case Literal(i) => Just(map[entry := (Cons(apply(0, const(integer(i))),Nil),     goto(exit))])
    case Id(v)      =>
      if v >= 0 && v in align then
                       Just(map[entry := (Cons(load(align[v]), Nil),                 goto(exit))])
      else Nothing
    // case Not(e)     =>
    //   var e' := CompileExpression(align, entry, )
}
