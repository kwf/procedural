
// Stuff I would want from a standard library

function method Absurd<A>(): A
  requires false
{
  Absurd()
}

function method Fst<A,B>(p: (A,B)): A { p.0 }
function method Snd<A,B>(p: (A,B)): B { p.1 }

datatype List<A> = Cons(A, List<A>) | Nil

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

function method MapList<A,B>(f: A -> B, xs: List<A>): List<B>
  requires forall x :: f.reads(x) == {}
  requires forall x :: x in Elements(xs) ==> f.requires(x)
  ensures Length(xs) == Length(MapList(f, xs))
{
  match xs
    case Nil => Nil
    case Cons(x, xs') => Cons(f(x), MapList(f, xs'))
}

function method ZipWith<A,B,C>(f: (A, B) -> C, xs: List<A>, ys: List<B>): List<C>
  requires forall x, y :: f.reads(x, y) == {}
  requires forall x, y :: f.requires(x, y)
  requires Length(xs) == Length(ys)
  ensures  Length(ZipWith(f, xs, ys)) == Length(xs) == Length(ys)
{
  match (xs, ys)
    case (Nil, Nil) => Nil
    case (Cons(x, xs'), Cons(y, ys')) => Cons(f(x, y), ZipWith(f, xs', ys'))
    // proving that mismatched lists are impossible
    case (Cons(x, xs'), Nil) => assert (Length(Cons(x, xs')) != Length<A>(Nil)); Absurd()
    case (Nil, Cons(y, ys')) => assert (Length(Cons(y, ys')) != Length<B>(Nil)); Absurd()
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
  requires forall x :: p.requires(x)
{
  Foldr(true, (x, y) => x && y, MapList(p, xs))
}

predicate method Any<A>(p: A -> bool, xs: List<A>)
  requires forall x :: p.reads(x) == {}
  requires forall x :: p.requires(x)
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

datatype Maybe<A> = Just(A) | Nothing

function method MapMaybe<A,B>(x: Maybe<A>, f: A -> B): Maybe<B>
  requires forall x :: f.reads(x) == {}
  requires forall x :: f.requires(x)
{
  match x
    case Nothing => Nothing
    case Just(x) => Just(f(x))
}

function method BindMaybe<A,B>(x: Maybe<A>, f: A -> Maybe<B>): Maybe<B>
  requires forall x :: f.reads(x) == {}
  requires forall x :: f.requires(x)
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
  requires forall a :: f.requires(a)
  requires forall b :: g.requires(b)
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
// SYNTAX

type Id = int

datatype Type = Unit | Bool | Int

datatype Expr = Unit | False | True | Literal(int) | Id(Id)
              | Not(Expr) | Apply(Expr, Op, Expr)
              | IfThenElse(Expr, Expr, Expr)
              | Call(Id, List<Expr>)



datatype Op = RelOp(RelOp) | BoolOp(BoolOp) | MathOp(MathOp)

datatype RelOp = Eq | NEq | LT | LTE

datatype BoolOp = Or | And

datatype MathOp = Plus | Minus | Times | DividedBy | Mod

type Program = map<Id, Decl>

type Decl = Either<Function, Procedure>

datatype Procedure = Procedure(List<(Id, Type)>, Type, Block)

datatype Function = Function(List<(Id, Type)>, Type, Block)

type Block = List<Statement>

datatype Statement = Var(Id, Type)
                   | Assign(Id, Expr)
                   | IfThenElse(Expr, Block, Block)
                   | While(Expr, Block)
                   | Return(Expr)
                   | Call(Maybe<Id>, Id, List<Expr>)
                   | Read(Maybe<Id>, Type)
                   | Print(FormatString, List<Expr>)

type FormatString = List<Either<Type, string>>

// FREE VARIABLES

function method FV_Gamma_Expr(e: Expr): set<Id>
  decreases e
{
  match e
    case Unit                   => {}
    case False                  => {}
    case True                   => {}
    case Literal(_)             => {}
    case Id(id)                 => {id}
    case Not(e1)                => FV_Gamma_Expr(e1)
    case Apply(e1, _, e2)       => FV_Gamma_Expr(e1) + FV_Gamma_Expr(e2)
    case IfThenElse(e1, e2, e3) => FV_Gamma_Expr(e1) + FV_Gamma_Expr(e2) + FV_Gamma_Expr(e3)
    case Call(_, es)            => Union(MapList(e' requires e' < e => FV_Gamma_Expr(e'), es))
}

function method FV_Gamma_Expr_List(es: List<Expr>): set<Id>
  decreases es
{
  match es
    case Nil => {}
    case Cons(e, es') => FV_Gamma_Expr(e) + FV_Gamma_Expr_List(es')
}

function method FV_Gamma_Statement(s: Statement): set<Id>
{
  match s
    case Var(v, _)             => {v}
    case Assign(v, _)          => {v}
    case IfThenElse(e, s1, s2) => FV_Gamma_Expr(e) + FV_Gamma_Block(s1) + FV_Gamma_Block(s2)
    case While(e, s)           => FV_Gamma_Expr(e) + FV_Gamma_Block(s)
    case Return(e)             => FV_Gamma_Expr(e)
    case Call(maybeId, _, es)  =>
      FV_Gamma_Expr_List(es) +
      (match maybeId case Just(v) => {v} case Nothing => {})
    case Read(maybeId, _)      =>
      (match maybeId case Just(v) => {v} case Nothing => {})
    case Print(_, es)          =>
      FV_Gamma_Expr_List(es)
}

function method FV_Gamma_Block(ss: Block): set<Id>
{
  match ss
    case Nil => {}
    case Cons(s, ss') => FV_Gamma_Statement(s) + FV_Gamma_Block(ss')
}


// TYPING

datatype Purity = Pure | Impure

datatype Certainty = Yes | Perhaps

type Delta = map<Id, (List<Type>, Type, Purity)> // env. of declarations

type Gamma = map<Id, Type> // env. of values

predicate method TypeExpr(delta: Delta, gamma: Gamma, e: Expr, t: Type) {
  match e
    // literals
    case Unit                      => t == Type.Unit
    case False                     => t == Bool
    case True                      => t == Bool
    case Literal(_)                => t == Int
    // variables
    case Id(id)                    => id in gamma && gamma[id] == t
    // operations
    case Not(e)                    => t == Bool && TypeExpr(delta, gamma, e,  Bool)
    case Apply(e1, RelOp(op), e2)  => t == Bool && TypeExpr(delta, gamma, e1, Int)
                                                && TypeExpr(delta, gamma, e2, Int)
    case Apply(e1, BoolOp(op), e2) => t == Bool && TypeExpr(delta, gamma, e1, Bool)
                                                && TypeExpr(delta, gamma, e2, Bool)
    case Apply(e1, MathOp(op), e2) => t == Int  && TypeExpr(delta, gamma, e1, Int)
                                                && TypeExpr(delta, gamma, e2, Int)
    // if-expressions
    case IfThenElse(e1, e2, e3) => TypeExpr(delta, gamma, e1, Bool)
                                && TypeExpr(delta, gamma, e2, t)
                                && TypeExpr(delta, gamma, e3, t)
    // calling of pure functions
    case Call(id, arguments) =>
      id in delta &&
      var (argTypes, retType, purity) := delta[id];
        t == retType &&
        purity == Pure &&
        TypeList(delta, gamma, arguments, argTypes)
}

predicate method TypeList(delta: Delta, gamma: Gamma, es: List<Expr>, ts: List<Type>)
{
  Length(es) == Length(ts) &&
    (match (es, ts)
      case (Nil, Nil) => true
      case (Cons(x, xs'), Nil) => assert (Length(Cons(x, xs')) != Length<Expr>(Nil)); Absurd()
      case (Nil, Cons(y, ys')) => assert (Length(Cons(y, ys')) != Length<Type>(Nil)); Absurd()
      case (Cons(e, es'), Cons(t, ts')) =>
        TypeExpr(delta, gamma, e, t) && TypeList(delta, gamma, es', ts'))
  // and(zipWith((e, t) => TypeExpr(delta, gamma, e, t), es, ts))
}

function method CheckStatement(delta: Delta, gamma: Gamma, rho: Type, s: Statement): Maybe<Gamma>
  decreases s
{
  match s
    case Var(id, t) =>
      if id !in gamma
      then Just(gamma[id := t])
      else Nothing
    case Assign(id, e) =>
      if id in gamma && TypeExpr(delta, gamma, e, gamma[id])
      then Just(gamma)
      else Nothing
    case IfThenElse(e, s1, s2) =>
      if !TypeExpr(delta, gamma, e, Bool) then Nothing else
      BindMaybe(CheckBlock(delta, gamma, rho, s1), gamma1 =>
      BindMaybe(CheckBlock(delta, gamma, rho, s2), gamma2 =>
      if gamma1 == gamma2 then Just(gamma1) else Nothing))
    case While(e, s) =>
      if !TypeExpr(delta, gamma, e, Bool)
      then Nothing
      else if CheckBlock(delta, gamma, rho, s) == Just(gamma)
           then Just(gamma)
           else Nothing
    case Call(maybeId, id, arguments) =>
      if id !in delta then Nothing else
      var (argTypes, retType, purity) := delta[id];
      if (match maybeId
           case Just(v) => v in gamma && gamma[v] == retType
           case Nothing => true) &&
         TypeList(delta, gamma, arguments, argTypes)
      then Just(gamma)
      else Nothing
    case Return(e) =>
      if TypeExpr(delta, gamma, e, rho) then Just(gamma) else Nothing
    case Read(maybeId, t) =>
      if (match maybeId
            case Nothing => true
            case Just(v) =>
              v in gamma && gamma[v] == t)
      then Just(gamma)
      else Nothing
    case Print(spec, arguments) =>
      if TypeList(delta, gamma, arguments, Lefts(spec)) then Just(gamma) else Nothing
}

function method CheckBlock(delta: Delta, gamma: Gamma, rho: Type, ss: Block): Maybe<Gamma>
  decreases ss
{
  match ss
    case Nil => Just(gamma)
    case Cons(s, ss') =>
      BindMaybe(CheckStatement(delta, gamma, rho, s), gamma' =>
      CheckBlock(delta, gamma', rho, ss'))
}

predicate method CertainBlock(ss: Block)
{
  match ss
    case Nil => false
    case Cons(s, ss') => CertainStatement(s) || CertainBlock(ss')
  // any(x => CertainStatement(x), ss)
}

predicate method CertainStatement(s: Statement)
{
  match s
    case Return(_)             => true
    case IfThenElse(_, s1, s2) => CertainBlock(s1) && CertainBlock(s2)
    case Var(_, _)             => false
    case Assign(_, _)          => false
    case While(_, _)           => false
    case Call(_, _, _)         => false
    case Read(_, _)            => false
    case Print(_, _)           => false
}

predicate method PureBlock(delta: Delta, ss: Block)
{
  match ss
    case Nil => true
    case Cons(s, ss') => PureStatement(delta, s) && PureBlock(delta, ss')
  // all(x => PureStatement(delta, x), ss)
}

predicate method PureStatement(delta: Delta, s: Statement)
{
  match s
    case Print(_, _)           => false
    case Read(_, _)            => false
    case IfThenElse(_, s1, s2) => PureBlock(delta, s1) && PureBlock(delta, s2)
    case While(_, s)           => PureBlock(delta, s)
    case Var(_, _)             => true
    case Assign(_, _)          => true
    case Return(_)             => true
    case Call(_, id, _)        =>
      id in delta &&
      (var (_, _, purity) := delta[id];
      purity == Pure)
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

predicate method TypeDecl(delta: Delta, declaration: Decl) {
  Either(
    ((func: Function) =>
      var Function(args, retType, ss) := func;
      PureBlock(delta, ss) &&            //            <--- functions must be pure
      (retType != Type.Unit ==> CertainBlock(ss)) &&
      NoDuplicates(MapList(Fst, args)) &&
      IsJust(CheckBlock(delta, MapFromList(args), retType, ss))),
    ((proc: Procedure) =>
      var Procedure(args, retType, ss) := proc;
      (retType != Type.Unit ==> CertainBlock(ss)) &&
      NoDuplicates(MapList(Fst, args)) &&
      IsJust(CheckBlock(delta, MapFromList(args), retType, ss))),
    declaration)
}

// BIG STEP SEMANTICS

type State = map<Id, Expr>

predicate method Value(e: Expr) {
  match e
    case Unit                => true
    case False               => true
    case True                => true
    case Literal(_)          => true
    case Id(_)               => false
    case Not(_)              => false
    case IfThenElse(_, _, _) => false
    case Call(_, _)          => false
    case Apply(_, _, _)      => false
}

inductive predicate Eval(delta: Delta, s: State, e: Expr, v: Expr)
