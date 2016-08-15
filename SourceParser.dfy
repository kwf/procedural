include "SourceSyntax.dfy"

extern "SourceScanner.Read"
method SourceScannerRead() returns (stringTokens: array<string>)
  ensures stringTokens != null

function method IdToString(id: Id): string
{
  if id <= 0 then "0" else
    var d, r := DigitToString(id % 10), id / 10;
    if r == 0 then d else IdToString(r) + d
}
function method StringToId(s: string): Id
{
  if s == "" then 0 else CharToDigit(s[|s|-1]) + 10 * StringToId(s[..|s|-1])
}
function method DigitToString(d: int): string
  requires 0 <= d < 10
{
  if d == 0 then "0"
  else if d == 1 then "1"
  else if d == 2 then "2"
  else if d == 3 then "3"
  else if d == 4 then "4"
  else if d == 5 then "5"
  else if d == 6 then "6"
  else if d == 7 then "7"
  else if d == 8 then "8"
  else "9"
}
function method CharToDigit(ch: char): int
{
  if ch == '0' then 0
  else if ch == '1' then 1
  else if ch == '2' then 2
  else if ch == '3' then 3
  else if ch == '4' then 4
  else if ch == '5' then 5
  else if ch == '6' then 6
  else if ch == '7' then 7
  else if ch == '8' then 8
  else 9
}
function method Reverse(xs: List): List
{
  ReverseAcc(xs, Nil)
}
function method ReverseAcc(xs: List, acc: List): List
{
  match xs
  case Nil => acc
  case Cons(x, tail) => ReverseAcc(tail, Cons(x, acc))
}

class Parser {
  var stringTokens: array<string>
  var p: nat
  predicate Valid()
    reads this
  {
    stringTokens != null &&
    p <= stringTokens.Length
  }
  constructor ()
    modifies this
    ensures Valid()
  {
    stringTokens := SourceScannerRead();
    p := 0;
  }
  function method Next(): string
    requires Valid()
    reads this, stringTokens
  {
    if p < stringTokens.Length then stringTokens[p] else ""
  }
  predicate method NextIsLiteral()  // this predicate does not guarantee the next token is a literal; it only distinguishes a literal from an ID
    requires Valid()
    reads this, stringTokens
  {
    Next() != "" && Next()[0] == '0'
  }
  predicate method NextIsStringLiteral()
    requires Valid()
    reads this, stringTokens
  {
    var s := Next();
    s != "" && 2 <= |s| && s[0] == '"' == s[|s|-1]
  }
  method Get() returns (s: string)
    requires Valid() && p < stringTokens.Length
    modifies this
    ensures Valid() && old(p) < p && stringTokens == old(stringTokens)
  {
    s, p := stringTokens[p], p+1;
  }
  method Expect(s: string) returns (success: bool)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
  {
    if Next() != "" && Next() == s {
      var _ := Get();
      return true;
    } else {
      Error("expected '" + s + "'");
      return false;
    }
  }
  method Error(msg: string) {
    print "Error at token ", p, ": ", msg, "\n";
  }

  method Parse() returns (success: bool, prog: Program)
    requires Valid()
    modifies this
    ensures Valid()
  {
    prog := map[];
    while Next() != ""
      invariant Valid()
      decreases stringTokens.Length - p
    {
      if Next() == "procedure" {
        var _ := Get();
        var id, params, result, block;
        success, id, params, result := ParseSignature();
        if !success { return; }
        success, block := ParseBlock();
        if !success { return; }
        if id in prog {
          Error("duplicate id: " + IdToString(id));
          return false, prog;
        }
        prog := prog[id := Right(Procedure(params, result, block))];
      } else if Next() == "function" {
        var _ := Get();
        var id, params, result, block;
        success, id, params, result := ParseSignature();
        if !success { return; }
        success, block := ParseBlock();
        if !success { return; }
        if id in prog {
          Error("duplicate id: " + IdToString(id));
          return false, prog;
        }
        prog := prog[id := Left(Function(params, result, block))];
      } else {
        Error("expecting procedure or function");
        return false, prog;
      }
    }
    return true, prog;
  }
  // Id "(" [ Id ":" Type { "," Id ":" Type } ] ")" ":" Type
  method ParseSignature() returns (success: bool, id: Id, params: List<(Id, Type)>, result: Type)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
  {
    success, id := ParseId();
    if !success { return; }

    success := Expect("(");
    if !success { return; }
    params := Nil;
    while true
      invariant Valid() && stringTokens == old(stringTokens)
      decreases stringTokens.Length - p
    {
      var paramId, paramType;
      success, paramId := ParseId();
      if !success { return; }

      success := Expect(":");
      if !success { return; }

      success, paramType := ParseType();
      if !success { return; }

      params := Cons((paramId, paramType), params);

      if Next() != "," { break; }
      var _ := Get();
    }
    params := Reverse(params);
    success := Expect(")");
    if !success { return; }

    success := Expect(":");
    if !success { return; }
    success, result := ParseType();
  }
  method ParseId() returns (success: bool, id: Id)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
  {
    if Next() == "" {
      Error("expected Id");
      success := false;
    } else {
      var idString := Get();
      success, id := true, StringToId(idString);
    }
  }
  method ParseType() returns (success: bool, typ: Type)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
  {
    if Next() == "unit" {
      typ := Type.Unit;
    } else if Next() == "bool" {
      typ := Bool;
    } else if Next() == "int" {
      typ := Int;
    } else {
      success := false;
      Error("bad type");
      return;
    }
    var _ := Get();
    return true, typ;
  }
  method ParseBlock() returns (success: bool, block: Block)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
    decreases stringTokens.Length - p
  {
    success := Expect("{");
    if !success { return; }

    block := Nil;
    while Next() != "}"
      invariant Valid() && stringTokens == old(stringTokens)
      decreases stringTokens.Length - p
    {
      var stmt;
      success, stmt := ParseStatement();
      if !success { return; }
      block := Cons(stmt, block);
    }
    var _ := Get();  // read the "}"
    return true, Reverse(block);
  }
  method ParseStatement() returns (success: bool, stmt: Statement)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
    decreases stringTokens.Length - p
  {
    if Next() == "var" {
      // Var(Id, Type, Expr)
      var _ := Get();
      var id, typ, e;
      success, id := ParseId();
      if !success { return; }
      success := Expect(":");
      if !success { return; }
      success, typ := ParseType();
      if !success { return; }
      success := Expect(":=");
      if !success { return; }
      success, e := ParseExpr();
      return success, Var(id, typ, e);
    } else if Next() == "if" {
      // IfThenElse(Expr, Block, Block)
      var _ := Get();
      var e, thn, els;
      success, e := ParseExpr();
      if !success { return; }
      success, thn := ParseBlock();
      if !success { return; }
      if Next() == "else" {
        var _ := Get();
        success, els := ParseBlock();
        if !success { return; }
      } else {
        els := Nil;
      }
      return true, Statement.IfThenElse(e, thn, els);
    } else if Next() == "while" {
      // While(Expr, Block)
      var _ := Get();
      var e, body;
      success, e := ParseExpr();
      if !success { return; }
      success, body := ParseBlock();
      if !success { return; }
      return true, While(e, body);
    } else if Next() == "return" {
      // Return(Expr)
      var _ := Get();
      var e;
      success, e := ParseExpr();
      if !success { return; }
      return true, Return(e);
    } else if Next() == "read" {
      // read(Type)   --Note: the statement "x := read(Type)" is parsed below together with assignment
      // Read(Maybe<Id>, Type)
      var _ := Get();
      var typ;
      success := Expect("(");
      if !success { return; }
      success, typ := ParseType();
      if !success { return; }
      success := Expect(")");
      return success, Read(Nothing, typ);
    } else if Next() == "print" {
      // TODO:  Change to:  Print(List<Either<string, (Expr,Type)>>)
      var _ := Get();
      var args;
      success, args := ParsePrintList();
      // TODO:  stmt := Print(args);
    } else {
      // Call or Assign
      var id;
      success, id := ParseId();
      if !success { return; }
      if Next() == "(" {
        // call with no out-parameter
        var _ := Get();
        var args;
        success, args := ParseExprList(")");
        stmt := Statement.Call(Nothing, id, args);
      } else {
        success := Expect(":=");
        if !success { return; }
        if Next() == "read" {
          var _ := Get();
          var typ;
          success := Expect("(");
          if !success { return; }
          success, typ := ParseType();
          if !success { return; }
          success := Expect(")");
          return success, Read(Just(id), typ);
        } else {
          var e;
          success, e := ParseExpr();
          if !success { return; }
          return true, Assign(id, e);
        }
      }
    }
  }
  method ParseExpr() returns (success: bool, expr: Expr)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
    decreases stringTokens.Length - p, 10
  {
    success, expr := ParseRelExpr();
    if !success { return; }
    if Next() == "&&" {
      while Next() == "&&"
        invariant Valid() 
        invariant old(p) < p && stringTokens == old(stringTokens)
        decreases stringTokens.Length - p
      {
        var _ := Get();
        var e;
        success, e := ParseRelExpr();
        if !success { return; }
        expr := Apply(expr, BoolOp(And), e);
      }
    } else if Next() == "||" {
      while Next() == "||"
        invariant Valid()
        invariant old(p) < p && stringTokens == old(stringTokens)
        decreases stringTokens.Length - p
      {
        var _ := Get();
        var e;
        success, e := ParseRelExpr();
        if !success { return; }
        expr := Apply(expr, BoolOp(Or), e);
      }
    }
  }
  method ParseRelExpr() returns (success: bool, expr: Expr)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
    decreases stringTokens.Length - p, 9
  {
    success, expr := ParseAddExpr();
    if !success { return; }
    if Next() == "==" || Next() == "!=" || Next() == "<" || Next() == "<=" {
      var op := Get();
      var e;
      success, e := ParseAddExpr();
      expr := Apply(expr, RelOp(if op == "==" then Eq else if op == "!=" then NEq else if op == "<" then LT else LTE), e);
    }
  }
  method ParseAddExpr() returns (success: bool, expr: Expr)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
    decreases stringTokens.Length - p, 8
  {
    success, expr := ParseMulExpr();
    if !success { return; }
    while Next() == "+" || Next() == "-"
        invariant Valid()
        invariant old(p) < p && stringTokens == old(stringTokens)
        decreases stringTokens.Length - p
    {
      var op := Get();
      var e;
      success, e := ParseMulExpr();
      if !success { return; }
      expr := Apply(expr, MathOp(if op == "+" then Plus else Minus), e);
    }
  }
  method ParseMulExpr() returns (success: bool, expr: Expr)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
    decreases stringTokens.Length - p, 7
  {
    success, expr := ParseUnaryExpr();
    if !success { return; }
    while Next() == "*" || Next() == "/" || Next() == "%"
        invariant Valid()
        invariant old(p) < p && stringTokens == old(stringTokens)
        decreases stringTokens.Length - p
    {
      var op := Get();
      var e;
      success, e := ParseUnaryExpr();
      if !success { return; }
      expr := Apply(expr, MathOp(if op == "*" then Times else if op == "/" then DividedBy else Mod), e);
    }
  }
  method ParseUnaryExpr() returns (success: bool, expr: Expr)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
    decreases stringTokens.Length - p, 6
  {
    if Next() == "!" {
      var _ := Get();
      success, expr := ParseUnaryExpr();
      expr := Not(expr);
    } else {
      success, expr := ParseAtomExpr();
    }
  }
  method ParseAtomExpr() returns (success: bool, expr: Expr)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
    decreases stringTokens.Length - p, 5
  {
    if Next() == "unit" {
      var _ := Get();
      return true, Expr.Unit;
    } else if Next() == "false" {
      var _ := Get();
      return true, Expr.False;
    } else if Next() == "true" {
      var _ := Get();
      return true, Expr.True;
    }  else if Next() == "if" {
      var _ := Get();
      var e, thn, els;
      success, e := ParseExpr();
      if !success { return; }
      success := Expect("then");
      if !success { return; }
      success, thn := ParseExpr();
      if !success { return; }
      success, els := ParseExpr();
      return success, Expr.IfThenElse(e, thn,els);
    } else if Next() == "(" {
      var _ := Get();
      success, expr := ParseExpr();
      if !success { return; }
      success := Expect(")");
    } else if NextIsLiteral() {
      var id;  // a literal parses like an ID
      success, id := ParseId();
      expr := Literal(id);
    } else {
      var id;
      success, id := ParseId();
      if !success { return; }
      if Next() == "(" {
        // we're looking at a call
        var _ := Get();
        var args;
        success, args := ParseExprList(")");
        expr := Expr.Call(id, args);
      } else {
        return true, Id(id);
      }
    }
  }
  method ParseExprList(stop: string) returns (success: bool, exprs: List<Expr>)
    requires Valid() && stop != ""
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
    decreases stringTokens.Length - p
  {
    success, exprs := true, Nil;
    if Next() == stop {
      var _ := Get();
      return;
    }
    while true
      invariant Valid()
      invariant old(p) <= p && stringTokens == old(stringTokens)
      decreases stringTokens.Length - p
    {
      var expr;
      success, expr := ParseExpr();
      if !success { return; }
      exprs := Cons(expr, exprs);
      if Next() == stop {
        var _ := Get();
        return;
      }
      success := Expect(",");
      if !success { return; }
    }
  }
  method ParsePrintList() returns (success: bool, args: List<Either<string, (Expr,Type)>>)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
    ensures success ==> args != Nil
    decreases stringTokens.Length - p
  {
    success, args := true, Nil;
    while true
      invariant Valid()
      invariant old(p) <= p && stringTokens == old(stringTokens)
      decreases stringTokens.Length - p
    {
      var arg;
      success, arg := ParsePrintArg();
      if !success { return; }
      args := Cons(arg, args);
      if Next() == "," {
        var _ := Get();
      } else {
        return;
      }
    }
  }
  method ParsePrintArg() returns (success: bool, arg: Either<string, (Expr,Type)>)
    requires Valid()
    modifies this
    ensures Valid() && (success ==> old(p) < p && stringTokens == old(stringTokens))
  {
    if NextIsStringLiteral() {
      var s := Get();  // includes the quotes
      return true, Left(s);
    } else {
      var e, typ;
      success, e := ParseExpr();
      if !success { return; }
      success := Expect(":");
      if !success { return; }
      success, typ := ParseType();
      return success, Right((e, typ));
    }
  }
}
