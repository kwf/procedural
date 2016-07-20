
include "Prelude.dfy"

type Id = int

datatype Type = Unit | Bool | Int

datatype Op = RelOp(RelOp) | BoolOp(BoolOp) | MathOp(MathOp)

datatype RelOp = Eq | NEq | LT | LTE

datatype BoolOp = Or | And

datatype MathOp = Plus | Minus | Times | DividedBy | Mod

type FormatString = List<Either<Type, string>>
