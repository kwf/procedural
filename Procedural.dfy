
// Stuff I would want from a standard library

function method absurd<A>(): A
  requires false
{
  absurd()
}

function method fst<A,B>(p: (A,B)): A { p.0 }
function method snd<A,B>(p: (A,B)): B { p.1 }

datatype List<A> = Cons(A, List<A>) | Nil

function method length(xs: List): nat {
  match xs
    case Nil          => 0
    case Cons(_, xs') => 1 + length(xs')
}

function method mapList<A,B>(f: A -> B, xs: List<A>): List<B>
  requires forall x :: f.reads(x) == {}
  requires forall x :: f.requires(x)
  ensures length(xs) == length(mapList(f, xs))
{
  match xs
    case Nil => Nil
    case Cons(x, xs') => Cons(f(x), mapList(f, xs'))
}

function method zipWith<A,B,C>(f: (A, B) -> C, xs: List<A>, ys: List<B>): List<C>
  requires forall x, y :: f.reads(x, y) == {}
  requires forall x, y :: f.requires(x, y)
  requires length(xs) == length(ys)
  ensures  length(zipWith(f, xs, ys)) == length(xs) == length(ys)
{
  match (xs, ys)
    case (Nil, Nil) => Nil
    case (Cons(x, xs'), Cons(y, ys')) => Cons(f(x, y), zipWith(f, xs', ys'))
    // proving that mismatched lists are impossible
    case (Cons(x, xs'), Nil) => assert (length(Cons(x, xs')) != length<A>(Nil)); absurd()
    case (Nil, Cons(y, ys')) => assert (length(Cons(y, ys')) != length<B>(Nil)); absurd()
}

function method foldr<A, B>(b: B, k: (A, B) -> B, xs: List<A>): B
  requires forall x, y :: k.reads(x, y) == {}
  requires forall x, y :: k.requires(x, y)
  decreases xs
{
  match xs
    case Nil => b
    case Cons(x, xs') => k(x, foldr(b, k, xs'))
}

predicate method all<A>(p: A -> bool, xs: List<A>)
  requires forall x :: p.reads(x) == {}
  requires forall x :: p.requires(x)
{
  foldr(true, (x, y) => x && y, mapList(p, xs))
}

predicate method any<A>(p: A -> bool, xs: List<A>)
  requires forall x :: p.reads(x) == {}
  requires forall x :: p.requires(x)
{
  foldr(false, (x, y) => x || y, mapList(p, xs))
}

predicate method and(xs: List<bool>) {
  all(x => x, xs)
}

predicate method or(xs: List<bool>) {
  any(x => x, xs)
}

function method union<A>(xs: List<set<A>>): set<A> {
  foldr({}, ((x, y) => x + y), xs)
}

datatype Maybe<A> = Just(A) | Nothing

function method mapMaybe<A,B>(x: Maybe<A>, f: A -> B): Maybe<B>
  requires forall x :: f.reads(x) == {}
  requires forall x :: f.requires(x)
{
  match x
    case Nothing => Nothing
    case Just(x) => Just(f(x))
}

function method bindMaybe<A,B>(x: Maybe<A>, f: A -> Maybe<B>): Maybe<B>
  requires forall x :: f.reads(x) == {}
  requires forall x :: f.requires(x)
{
  match x
    case Nothing => Nothing
    case Just(x) => f(x)
}

function method isJust<A>(x: Maybe<A>): bool
  ensures (exists y :: x == Just(y)) <==> isJust(x)
{
  match x
    case Just(_) => true
    case Nothing => false
}

datatype Either<A,B> = Left(A) | Right(B)

function method either<A,B,R>(f: A -> R, g: B -> R, e: Either<A,B>): R
  requires forall a :: f.reads(a) == {}
  requires forall b :: g.reads(b) == {}
  requires forall a :: f.requires(a)
  requires forall b :: g.requires(b)
{
  match e
    case Left(l)  => f(l)
    case Right(r) => g(r)
}

function method lefts<A,B>(es: List<Either<A,B>>): List<A> {
  match es
    case Nil                 => Nil
    case Cons(Left(l),  es') => Cons(l, lefts(es'))
    case Cons(Right(_), es') => lefts(es')
}

function method rights<A,B>(es: List<Either<A,B>>): List<B> {
  match es
    case Nil                 => Nil
    case Cons(Left(_),  es') => rights(es')
    case Cons(Right(r), es') => Cons(r, rights(es'))
}

// SYNTAX

type Id = int

datatype Type = Unit | Bool | Int

datatype Expr = Unit | False | True | Literal(int) | Id(Id)
              | Not(Expr) | Apply(Expr, Op, Expr)
              | IfThenElse(Expr, Expr, Expr)
              | Call(Id, List<Expr>)

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
    case Call(_, es)            => FV_Gamma_Expr_List(es) // union(mapList(e => FV_Gamma_Expr(e), es))
}

function method FV_Gamma_Expr_List(es: List<Expr>): set<Id>
  decreases es
{
  match es
    case Nil => {}
    case Cons(e, es') => FV_Gamma_Expr(e) + FV_Gamma_Expr_List(es')
}

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

type FormatString = List<Either<Type, string>>

// TYPING

datatype Purity = Pure | Impure

datatype Certainty = Yes | Perhaps

function method boolFromCertainty(c: Certainty): bool {
  match c
    case Yes => true
    case Perhaps => false
}

function method certaintyFromBool(b: bool): Certainty {
  if b then Yes else Perhaps
}

function method CertAnd(c1: Certainty, c2: Certainty): Certainty {
  certaintyFromBool(boolFromCertainty(c1) && boolFromCertainty(c2))
}

function method CertOr(c1: Certainty, c2: Certainty): Certainty {
  certaintyFromBool(boolFromCertainty(c1) || boolFromCertainty(c2))
}

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
  length(es) == length(ts) &&
    (match (es, ts)
      case (Nil, Nil) => true
      case (Cons(x, xs'), Nil) => assert (length(Cons(x, xs')) != length<Expr>(Nil)); absurd()
      case (Nil, Cons(y, ys')) => assert (length(Cons(y, ys')) != length<Type>(Nil)); absurd()
      case (Cons(e, es'), Cons(t, ts')) =>
        TypeExpr(delta, gamma, e, t) && TypeList(delta, gamma, es', ts'))
  // and(zipWith((e, t) => TypeExpr(delta, gamma, e, t), es, ts))
}

// predicate TypeStatement(delta: Delta, gamma: Gamma, rho: Type, s: Statement, gamma': Gamma)
//   decreases s
// {
//   match s
//     case Var(id, t) =>
//       id !in gamma &&
//       gamma' == gamma[id := t]
//     case Assign(id, e) =>
//       id in gamma &&
//       TypeExpr(delta, gamma, e, gamma[id])
//     case IfThenElse(e, s1, s2) =>
//       TypeExpr(delta, gamma, e, Bool) &&
//       TypeBlock(delta, gamma, rho, s1, gamma') &&
//       TypeBlock(delta, gamma, rho, s1, gamma')
//     case While(e, s) =>
//       TypeExpr(delta, gamma, e, Bool) &&
//       TypeBlock(delta, gamma, rho, s, gamma)
//     case Call(maybeId, id, arguments) =>
//       id in delta &&
//       var (argTypes, retType, purity) := delta[id];
//         (match maybeId
//           case Just(v) => v in gamma && gamma[v] == retType
//           case Nothing => true) &&
//         TypeList(delta, gamma, arguments, argTypes)
//     case Return(e) =>
//       TypeExpr(delta, gamma, e, rho)
//     case Read(maybeId, t) =>
//       (match maybeId
//         case Nothing => true
//         case Just(v) =>
//           v in gamma && gamma[v] == t)
//     case Print(spec, arguments) =>
//       TypeList(delta, gamma, arguments, lefts(spec))
// }

function method CheckStatement(delta: Delta, gamma: Gamma, rho: Type, s: Statement): Maybe<Gamma>
  decreases s
  // soundness
  // ensures forall gamma' :: CheckStatement(delta, gamma, rho, s) == Just(gamma')
  //                 ==> TypeStatement(delta, gamma, rho, s, gamma')
  // completeness (TODO: this isn't true yet -- need to prune domain of gamma')
  // ensures forall gamma' :: TypeStatement(delta, gamma, rho, s, gamma')
  //                 ==> CheckStatement(delta, gamma, rho, s) == Just(gamma')
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
      bindMaybe(CheckBlock(delta, gamma, rho, s1), gamma1 =>
      bindMaybe(CheckBlock(delta, gamma, rho, s2), gamma2 =>
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
      if TypeList(delta, gamma, arguments, lefts(spec)) then Just(gamma) else Nothing
}

// inductive lemma CheckStatement_sound(delta: Delta, gamma: Gamma, rho: Type, s: Statement, gamma': Gamma)
//   requires CheckStatement(delta, gamma, rho, s) == Just(gamma')
//   ensures  TypeStatement(delta, gamma, rho, s, gamma')
// {
//   match s
//     case Var(id, t) =>
//     case Assign(id, e) =>
//     case IfThenElse(e, s1, s2) =>
//       CheckBlock_sound(delta, gamma, rho, s1, gamma');
//       CheckBlock_sound(delta, gamma, rho, s2, gamma');
//     case While(e, s) =>
//       if gamma == gamma' {
//         CheckBlock_sound(delta, gamma, rho, s, gamma);
//       }
//     case Call(maybeId, id, arguments) =>
//     case Return(e) =>
//     case Read(maybeId, t) =>
//     case Print(spec, arguments) =>
// }

// predicate TypeBlock(delta: Delta, gamma: Gamma, rho: Type, ss: Block, gamma'': Gamma)
//   decreases ss
// {
//   match ss
//     case Nil => true
//     case Cons(s, ss') =>
//       exists gamma' ::
//         TypeStatement(delta, gamma, rho, s, gamma') &&
//         TypeBlock(delta, gamma', rho, ss', gamma'')
// }

function method CheckBlock(delta: Delta, gamma: Gamma, rho: Type, ss: Block): Maybe<Gamma>
  decreases ss
{
  match ss
    case Nil => Just(gamma)
    case Cons(s, ss') =>
      bindMaybe(CheckStatement(delta, gamma, rho, s), gamma' =>
      CheckBlock(delta, gamma', rho, ss'))
}

// inductive lemma CheckBlock_sound(delta: Delta, gamma: Gamma, rho: Type, ss: Block, gamma'': Gamma)
//   requires CheckBlock(delta, gamma, rho, ss) == Just(gamma'')
//   ensures  TypeBlock(delta, gamma, rho, ss, gamma'')
// {
//   match ss
//     case Nil =>
//     case Cons(s, ss') =>
//       var gamma' :| CheckStatement(delta, gamma, rho, s) == Just(gamma');
//       CheckStatement_sound(delta, gamma, rho, s, gamma');
//       CheckBlock_sound(delta, gamma', rho, ss', gamma'');
//       CheckBlock_reassemble(delta, gamma, rho, s, ss', gamma', gamma'');
// }

// lemma CheckBlock_reassemble(delta: Delta, gamma: Gamma, rho: Type, s: Statement, ss: Block, gamma': Gamma, gamma'': Gamma)
//   requires CheckBlock(delta, gamma, rho, Cons(s, ss)) == Just(gamma'')
//   requires TypeStatement(delta, gamma, rho, s, gamma')
//   requires TypeBlock(delta, gamma', rho, ss, gamma'')
//   ensures  TypeBlock(delta, gamma, rho, Cons(s, ss), gamma'')
// {
// }

predicate method certainBlock(ss: Block)
{
  match ss
    case Nil => false
    case Cons(s, ss') => certainStatement(s) || certainBlock(ss')
  // any(x => certainStatement(x), ss)
}

predicate method certainStatement(s: Statement)
{
  match s
    case Return(_)             => true
    case IfThenElse(_, s1, s2) => certainBlock(s1) && certainBlock(s2)
    case Var(_, _)             => false
    case Assign(_, _)          => false
    case While(_, _)           => false
    case Call(_, _, _)         => false
    case Read(_, _)            => false
    case Print(_, _)           => false
}

predicate method pureBlock(delta: Delta, ss: Block)
{
  match ss
    case Nil => true
    case Cons(s, ss') => pureStatement(delta, s) && pureBlock(delta, ss')
  // all(x => pureStatement(delta, x), ss)
}

predicate method pureStatement(delta: Delta, s: Statement)
{
  match s
    case Print(_, _)           => false
    case Read(_, _)            => false
    case IfThenElse(_, s1, s2) => pureBlock(delta, s1) && pureBlock(delta, s2)
    case While(_, s)           => pureBlock(delta, s)
    case Var(_, _)             => true
    case Assign(_, _)          => true
    case Return(_)             => true
    case Call(_, id, _)        =>
      id in delta &&
      (var (_, _, purity) := delta[id];
      purity == Pure)
}

function method mapFromList<A, B>(pairs: List<(A, B)>): map<A,B> {
  foldr(map[],
        ((ab: (A, B), m: map<A,B>) =>
            var (a, b) := ab;
            m[a := b]),
        pairs)
}

function method elements<A>(xs: List<A>): set<A>
{
  foldr({}, ((x, s) => {x} + s), xs)
}

predicate method noDuplicates<A(==)>(xs: List<A>) {
  |elements(xs)| == length(xs)
}

predicate method TypeDecl(delta: Delta, declaration: Decl) {
  either(
    ((func: Function) =>
      var Function(args, retType, ss) := func;
      pureBlock(delta, ss) &&            //            <--- functions must be pure
      (retType != Type.Unit ==> certainBlock(ss)) &&
      noDuplicates(mapList(fst, args)) &&
      isJust(CheckBlock(delta, mapFromList(args), retType, ss))),
    ((proc: Procedure) =>
      var Procedure(args, retType, ss) := proc;
      (retType != Type.Unit ==> certainBlock(ss)) &&
      noDuplicates(mapList(fst, args)) &&
      isJust(CheckBlock(delta, mapFromList(args), retType, ss))),
    declaration)
}


