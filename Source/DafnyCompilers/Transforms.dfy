include "Library.dfy"
include "AST.dfy"
include "Predicates.dfy"
include "Rewriters.dfy"

module DafnyCompilerCommon.Transforms {
  module FlipNegatedBinops {
    import Lib
    import opened AST
    import opened Lib.Datatypes
    import opened Rewriters.BottomUp

    import opened Predicates

    function method FlipNegatedBinop1(op: BinaryOps.BinaryOp) : (op': BinaryOps.BinaryOp)
    {
      match op {
        case Eq(NeqCommon) => BinaryOps.Eq(BinaryOps.EqCommon)
        case Sequences(SeqNeq) => BinaryOps.Sequences(BinaryOps.SeqEq)
        case Sequences(NotInSeq) => BinaryOps.Sequences(BinaryOps.InSeq)
        case Sets(SetNeq) => BinaryOps.Sets(BinaryOps.SetEq)
        case Sets(NotInSet) => BinaryOps.Sets(BinaryOps.InSet)
        case Multisets(MultisetNeq) => BinaryOps.Multisets(BinaryOps.MultisetEq)
        case Multisets(NotInMultiset) => BinaryOps.Multisets(BinaryOps.InMultiset)
        case Maps(MapNeq) => BinaryOps.Maps(BinaryOps.MapEq)
        case Maps(NotInMap) => BinaryOps.Maps(BinaryOps.InMap)
        case _ => op
      }
    }

    function method FlipNegatedBinop(op: BinaryOps.BinaryOp) : (op': BinaryOps.BinaryOp)
      ensures !IsNegatedBinop(op')
    {
      FlipNegatedBinop1(op)
    }

    predicate method IsNegatedBinop(op: BinaryOps.BinaryOp) {
      FlipNegatedBinop1(op) != op
    }

    predicate method IsNegatedBinopExpr(e: Exprs.T) {
      match e {
        case Apply(Eager(BinaryOp(op)), _) => IsNegatedBinop(op)
        case _ => false
      }
    }

    predicate NotANegatedBinopExpr(e: Exprs.T) {
      !IsNegatedBinopExpr(e)
    }

    function method EliminateNegatedBinops_Expr1(e: Exprs.T) : (e': Exprs.T)
      ensures NotANegatedBinopExpr(e')
    {
      match e {
        case Apply(Eager(BinaryOp(op)), es) =>
          if IsNegatedBinop(op) then
            var flipped := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(FlipNegatedBinop(op))), es);
            Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.BoolNot)), [flipped])
          else
            e
        case _ => e
      }
    }

    lemma EliminateNegatedBinopsMatchesPrePost()
      ensures TransformerMatchesPrePost(EliminateNegatedBinops_Expr1, NotANegatedBinopExpr)
    {}

    lemma EliminateNegatedBinopsPreservesPre()
      ensures MapChildrenPreservesPre(EliminateNegatedBinops_Expr1, NotANegatedBinopExpr)
    {}

     const EliminateNegatedBinops_Expr : BottomUpTransformer :=
      ( EliminateNegatedBinopsMatchesPrePost();
        EliminateNegatedBinopsPreservesPre();
        TR(EliminateNegatedBinops_Expr1, NotANegatedBinopExpr))

    function method EliminateNegatedBinops_Expr_direct(e: Exprs.T) : (e': Exprs.T)
      requires Deep.All_Expr(e, Exprs.WellFormed)
      ensures Deep.All_Expr(e', NotANegatedBinopExpr)
      ensures Deep.All_Expr(e', Exprs.WellFormed)
    {
      Deep.AllImpliesChildren(e, Exprs.WellFormed);
      match e {
        case Var(_) => e
        case Literal(lit_) => e
        case Abs(vars, body) => Exprs.Abs(vars, EliminateNegatedBinops_Expr_direct(body))
        case Apply(Eager(BinaryOp(bop)), exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Predicates.Map_All_IsMap(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          if IsNegatedBinop(bop) then
            var e'' := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(FlipNegatedBinop(bop))), exprs');
            var e' := Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.BoolNot)), [e'']);
            e'
          else
            Expr.Apply(Exprs.Eager(Exprs.BinaryOp(bop)), exprs')
        case Apply(aop, exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Predicates.Map_All_IsMap(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Expr.Apply(aop, exprs')

        case Block(exprs) =>
          var exprs' := Seq.Map(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Predicates.Map_All_IsMap(e requires e in exprs => EliminateNegatedBinops_Expr_direct(e), exprs);
          Expr.Block(exprs')
        case Bind(vars, vals, body) =>
          var vals' := Seq.Map(e requires e in vals => EliminateNegatedBinops_Expr_direct(e), vals);
          Predicates.Map_All_IsMap(e requires e in vals => EliminateNegatedBinops_Expr_direct(e), vals);
          Exprs.Bind(vars, vals, EliminateNegatedBinops_Expr_direct(body))
        case If(cond, thn, els) =>
          Expr.If(EliminateNegatedBinops_Expr_direct(cond),
                  EliminateNegatedBinops_Expr_direct(thn),
                  EliminateNegatedBinops_Expr_direct(els))
      }
    }

    function method EliminateNegatedBinops(p: Program) : (p': Program)
      requires Deep.All_Program(p, EliminateNegatedBinops_Expr.f.requires)
      ensures Deep.All_Program(p', NotANegatedBinopExpr)
    {
      Map_Program(p, EliminateNegatedBinops_Expr)
    }
  }
}
