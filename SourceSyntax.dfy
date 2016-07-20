
include "Prelude.dfy"
include "Common.dfy"

// SYNTAX

datatype Expr = Unit | False | True | Literal(int) | Id(Id)
              | Not(Expr) | Apply(Expr, Op, Expr)
              | IfThenElse(Expr, Expr, Expr)
              | Call(Id, List<Expr>)

type Program = map<Id, Decl>

type Decl = Either<Function, Procedure>

datatype Procedure = Procedure(List<(Id, Type)>, Type, Block)

datatype Function = Function(List<(Id, Type)>, Type, Block)

type Block = List<Statement>

datatype Statement = Var(Id, Type, Expr)
                   | Assign(Id, Expr)
                   | IfThenElse(Expr, Block, Block)
                   | While(Expr, Block)
                   | Return(Expr)
                   | Call(Maybe<Id>, Id, List<Expr>)
                   | Read(Maybe<Id>, Type)
                   | Print(FormatString, List<Expr>)


type TopLevel = map<Id, (List<Id>, Block)>

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
    case Call(_, es)            => AllSmallerThanList(es);
                                   Union(MapList(e' requires e' < e => FV_Gamma_Expr(e'), es))
}

function method FV_Gamma_Statement(s: Statement): set<Id>
{
  match s
    case Var(v, _, e)          => {v} + FV_Gamma_Expr(e)
    case Assign(v, _)          => {v}
    case IfThenElse(e, s1, s2) => FV_Gamma_Expr(e) + FV_Gamma_Block(s1) + FV_Gamma_Block(s2)
    case While(e, s)           => FV_Gamma_Expr(e) + FV_Gamma_Block(s)
    case Return(e)             => FV_Gamma_Expr(e)
    case Call(maybeId, _, es)  =>
      (AllSmallerThanList(es);
      Union(MapList(e' requires e' < es => FV_Gamma_Expr(e'), es))) +
      (match maybeId case Just(v) => {v} case Nothing => {})
    case Read(maybeId, _)      =>
      (match maybeId case Just(v) => {v} case Nothing => {})
    case Print(_, es)          =>
      AllSmallerThanList(es);
      Union(MapList(e' requires e' < es => FV_Gamma_Expr(e'), es))
}

function method FV_Gamma_Block(ss: Block): set<Id>
{
  AllSmallerThanList(ss);
  Union(MapList(e' requires e' < ss => FV_Gamma_Statement(e'), ss))
}
