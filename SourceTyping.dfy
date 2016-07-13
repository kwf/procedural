
include "Prelude.dfy"
include "SourceSyntax.dfy"

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
  (AllSmallerThanList(es); AllSmallerThanList(ts);
  And(ZipWith((e, t) requires e < es && t < ts =>
    TypeExpr(delta, gamma, e, t), es, ts)))
}

function method CheckStatement(delta: Delta, gamma: Gamma, rho: Type, s: Statement): Maybe<Gamma>
  decreases s
{
  match s
    case Var(id, t, e) =>
      if id !in gamma && TypeExpr(delta, gamma, e, t)
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
  AllSmallerThanList(ss); Any(x requires x < ss => CertainStatement(x), ss)
}

predicate method CertainStatement(s: Statement)
{
  match s
    case Return(_)             => true
    case IfThenElse(_, s1, s2) => CertainBlock(s1) && CertainBlock(s2)
    case Var(_, _, _)          => false
    case Assign(_, _)          => false
    case While(_, _)           => false
    case Call(_, _, _)         => false
    case Read(_, _)            => false
    case Print(_, _)           => false
}

predicate method PureBlock(delta: Delta, ss: Block)
{
  AllSmallerThanList(ss); All(x requires x < ss => PureStatement(delta, x), ss)
}

predicate method PureStatement(delta: Delta, s: Statement)
{
  match s
    case Print(_, _)           => false
    case Read(_, _)            => false
    case IfThenElse(_, s1, s2) => PureBlock(delta, s1) && PureBlock(delta, s2)
    case While(_, s)           => PureBlock(delta, s)
    case Var(_, _, _)          => true
    case Assign(_, _)          => true
    case Return(_)             => true
    case Call(_, id, _)        =>
      id in delta &&
      (var (_, _, purity) := delta[id];
      purity == Pure)
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

predicate method TypeProgram(delta: Delta, d: TopLevel) {
  0 in delta && delta[0] == (Nil, Type.Unit, Impure) &&  // main is procedure 0, with no arguments and unit return
    forall proc | proc in d ::
    proc in delta &&
    var (ps, body)      := d[proc];
    var (ts, r, purity) := delta[proc];
    Length(ps) == Length(ts) &&
      match purity
        case Pure   => TypeDecl(delta,   Left(Function(Zip(ps, ts), r, body)))
        case Impure => TypeDecl(delta, Right(Procedure(Zip(ps, ts), r, body)))
}
