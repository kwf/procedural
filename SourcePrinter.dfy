include "SourceSyntax.dfy"

class SourcePrinter {
  method PrintProgram(prog: Program)
  {
    var ids := set id | id in prog;
    while ids != {}
      decreases ids
    {
      var id :| id in ids;
      ids := ids - {id};
      match prog[id]
      case Left(Function(args, r, body)) =>
        PrintSignature("function", id, args, r, body);
      case Right(p) =>
        match p case Procedure(args, r, body) =>
          PrintSignature("procedure", id, args, r, body);
    }
  }
  method PrintSignature(kind: string, id: Id, args: List<(Id,Type)>, r: Type, body: Block)
  {
    print kind, " ";
    print id, "(";
    var sep := "";
    var a := args;
    while a != Nil
      decreases a
    {
      print sep, a.Head.0, ": ";
      PrintType(a.Head.1);
      a, sep := a.Tail, ", ";
    }
    print "): ";
    PrintType(r);
    print "\n";
    PrintBlock(body, 0);
    print "\n";
  }
  method PrintType(typ: Type)
  {
    match typ
    case Unit => print "unit";
    case Bool => print "bool";
    case Int => print "int";
  }
  method PrintBlock(body: Block, indent: nat)
  {
    print "{\n";
    var stmtList := body;
    while stmtList != Nil
      decreases stmtList
    {
      PrintStatement(stmtList.Head, indent + 2);
      stmtList := stmtList.Tail;
    }
    Indent(indent);
    print "}";
  }
  method Indent(indent: nat) {
    var n := 0;
    while n < indent {
      print " ";
      n := n + 1;
    }
  }
  method PrintStatement(stmt: Statement, indent: nat)
  {
    Indent(indent);
    match stmt {
      case Var(id, typ, e) =>
        print "var ", id, ": ";
        PrintType(typ);
        print " := ";
        PrintExpr(e);
      case Assign(id, e) =>
        print id, " := ";
        PrintExpr(e);
      case IfThenElse(e, thn, els) =>
        print "if ";
        PrintExpr(e);
        print " ";
        PrintBlock(thn, indent + 2);
        if els != Nil {
          print " else {\n";
          PrintBlock(els, indent + 2);
        }
      case While(e, body) =>
        print "while ";
        PrintExpr(e);
        print " ";
        PrintBlock(body, indent + 2);
      case Return(e) =>
        print "return ";
        PrintExpr(e);
      case Call(maybeId, id, args) =>
        if maybeId.Just? {
          print maybeId.FromJust, " := ";
        }
        print id, "(";
        PrintExprList(args);
        print ")";
      case Read(maybeId, typ) =>
        if maybeId.Just? {
          print maybeId.FromJust, " := ";
        }
        print "read(";
        PrintType(typ);
        print ")";
      case Print(_, _) =>
        // TODO
    }
    print "\n";
  }
  method PrintExprList(exprs: List<Expr>) {
    var e, sep := exprs, "";
    while e != Nil
      decreases e
    {
      print sep;
      PrintExpr(e.Head);
      e, sep := e.Tail, ", ";
    }
  }
  method PrintExpr(expr: Expr)
  {
    match expr
    case Unit =>
      print "unit";
    case False =>
      print "false";
    case True =>
      print "true";
    case Literal(x) =>
      print "0", x;
    case Id(id) =>
      print id;
    case Not(e) =>
      print "!(";
      PrintExpr(e);
      print ")";
    case Apply(e0, op, e1) =>
      print "(";
      PrintExpr(e0);
      print " ";
      match op {
        case RelOp(r) =>
          match r {
            case Eq  => print "==";
            case NEq => print "!=";
            case LT  => print "<";
            case LTE => print "<=";
          }
        case BoolOp(r) =>
          match r {
            case Or  => print "||";
            case And => print "&&";
          }
        case MathOp(r) =>
          match r {
            case Plus      => print "+";
            case Minus     => print "-";
            case Times     => print "*";
            case DividedBy => print "/";
            case Mod       => print "%";
          }
      }
      print " ";
      PrintExpr(e1);
      print ")";
    case IfThenElse(e, thn, els) =>
      print "if ";
      PrintExpr(e);
      print " then ";
      PrintExpr(thn);
      print " else ";
      PrintExpr(els);
    case Call(id, args) =>
      print id, "(";
      PrintExprList(args);
      print ")";
  }
}
