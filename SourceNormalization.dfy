
include "Prelude.dfy"
include "SourceSyntax.dfy"
include "SourceTyping.dfy"
include "SourceSemantics.dfy"

// NORMAL FORMS

inductive lemma NormalFormBigStepExpr(d: TopLevel, s: State, e: Expr, r: Expr)
  decreases e
  requires ValidState(s)
  requires EvalExpr(d, s, e, r)
  ensures  SyntacticValue(r)
{
  if e.Call? {
    match e
      case Call(p, es) =>
        var vs :| EvalList(d, s, es, vs) &&
                  EvalCall(d, p, vs, r);
        NormalFormBigStepCall(d, p, vs, r);
  }
}

inductive lemma NormalFormBigStepCall(d: TopLevel, p: Id, vs: List<Expr>, r: Expr)
  requires EvalCall(d, p, vs, r)
  ensures  SyntacticValue(r)
{
  var (params, body) := d[p];
  var s0 := NewState(params, vs);
  if s' :| ValidState(s') && EvalBlock(d, body, s0, s', Just(r)) {
    NormalFormBigStepBlockReturn(d, body, s0, s', r);
  }
}

inductive lemma NormalFormBigStepBlockReturn(d: TopLevel, cs: Block, s: State, s'': State, r: Expr)
  requires ValidState(s)
  requires ValidState(s'')
  requires EvalBlock(d, cs, s, s'', Just(r))
  ensures  SyntacticValue(r)
{
  match cs
    case Nil =>
    case Cons(c, cs') =>
      if EvalStatement(d, c, s, s'', Just(r)) {
        NormalFormBigStepStatementReturn(d, c, s, s'', r);
      } else {
        var s' :| ValidState(s') &&
                  EvalStatement(d, c, s, s', Nothing) &&
                  EvalBlock(d, cs', s', s'', Just(r));
        NormalFormBigStepBlockReturn(d, cs', s', s'', r);
      }
}

inductive lemma NormalFormBigStepStatementReturn(d: TopLevel, c: Statement, s: State, s'': State, r: Expr)
  requires ValidState(s)
  requires ValidState(s'')
  requires EvalStatement(d, c, s, s'', Just(r))
  ensures  SyntacticValue(r)
{
  if c.Return? || c.IfThenElse? || c.While? {
    match c
      case Return(e) =>
        NormalFormBigStepExpr(d, s, e, r);
      case IfThenElse(e, c1, c2) =>
        var b :| EvalIfStatement(d, e, c1, c2, s, s'', Just(r), b);
        if b {
          NormalFormBigStepBlockReturn#[_k - 2](d, c1, s, s'', r);
        } else {
          NormalFormBigStepBlockReturn#[_k - 2](d, c2, s, s'', r);
        }
      case While(e, c) =>
        var s', broken :| EvalWhileLoop(d, e, c, s, s', s'', Just(r), broken);
        if broken {
          NormalFormBigStepBlockReturn#[_k - 2](d, c, s, s', r);
        } else {
          NormalFormBigStepStatementReturn#[_k - 2](d, While(e, c), s', s'', r);
        }
  }
}
