include "Prelude.dfy"
include "Common.dfy"

predicate method BoolOpDenotes(op: BoolOp, b1: bool, b2: bool, result: bool) {
  match op
    case Or  => result == b1 || b2
    case And => result == b1 && b2
}

predicate method RelOpDenotes(op: RelOp, v1: int, v2: int, result: bool) {
  match op
    case Eq  => result == (v1 == v2)
    case NEq => result == (v1 != v2)
    case LT  => result == (v1 < v2)
    case LTE => result == (v1 <= v2)
}

predicate method MathOpDenotes(op: MathOp, v1: int, v2: int, result: int) {
  match op
    case Plus      =>             result == v1 + v2
    case Times     =>             result == v1 * v2
    case Minus     =>             result == v1 - v2
    case DividedBy => v2 != 0 ==> result == v1 / v2  // division by zero is undefined
    case Mod       => v2 != 0 ==> result == v1 % v2  // division by zero is undefined
}
