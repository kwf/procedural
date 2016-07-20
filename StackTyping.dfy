
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
