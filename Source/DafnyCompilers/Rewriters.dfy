include "CSharpDafnyASTModel.dfy"
include "CSharpInterop.dfy"
include "CSharpDafnyInterop.dfy"
include "CSharpDafnyASTInterop.dfy"
include "Library.dfy"
include "StrTree.dfy"
include "AST.dfy"
include "Translator.dfy"
include "Predicates.dfy"

module DafnyCompilerCommon.Rewriters {
    import Lib
    import opened AST
    import opened StrTree
    import opened Lib.Datatypes
    import opened CSharpInterop

    module Shallow {
      import opened Lib
      import opened AST
      import opened Predicates

      function method {:opaque} Map_Method(m: Method, tr: ExprTransformer) : (m': Method)
        requires Shallow.All_Method(m, tr.f.requires)
        ensures Shallow.All_Method(m', tr.Post) // FIXME Deep
      {
        match m {
          case Method(CompileName, methodBody) =>
            Method(CompileName, tr.f(methodBody))
        }
      }

      function method {:opaque} Map_Program(p: Program, tr: ExprTransformer) : (p': Program)
        requires Shallow.All_Program(p, tr.f.requires)
        ensures Shallow.All_Program(p', tr.Post)
      {
        match p {
          case Program(mainMethod) => Program(Map_Method(mainMethod, tr))
        }
      }
    }

    module BottomUp {
      import opened AST
      import opened Lib
      import opened Predicates
      import Shallow

      predicate MapChildrenPreservesPre(f: Expr --> Expr, post: Expr -> bool) {
        forall e, e' ::
          (&& Exprs.ConstructorsMatch(e, e')
           && f.requires(e)
           && Deep.AllChildren_Expr(e', post)) ==> f.requires(e')
       }

      predicate TransformerMatchesPrePost(f: Expr --> Expr, post: Expr -> bool) {
        forall e: Expr | Deep.AllChildren_Expr(e, post) && f.requires(e) ::
          Deep.All_Expr(f(e), post)
      }

      predicate IsBottomUpTransformer(f: Expr --> Expr, post: Expr -> bool) {
        && TransformerMatchesPrePost(f, post)
        && MapChildrenPreservesPre(f, post)
      }

      const IdentityTransformer: ExprTransformer :=
        TR(d => d, _ => true)

      lemma IdentityMatchesPrePost()
        ensures TransformerMatchesPrePost(IdentityTransformer.f, IdentityTransformer.Post)
      { }

      lemma IdentityPreservesPre()
        ensures MapChildrenPreservesPre(IdentityTransformer.f, IdentityTransformer.Post)
      { }

      type BottomUpTransformer = tr: ExprTransformer | IsBottomUpTransformer(tr.f, tr.Post)
        witness (IdentityMatchesPrePost();
                 IdentityPreservesPre();
                 IdentityTransformer)

      function method {:vcs_split_on_every_assert} MapChildren_Expr(e: Expr, tr: BottomUpTransformer) : (e': Expr)
        decreases e, 0
        requires Deep.All_Expr(e, tr.f.requires)
        ensures Deep.AllChildren_Expr(e', tr.Post)
        ensures Exprs.ConstructorsMatch(e, e')
      {
        Deep.AllImpliesChildren(e, tr.f.requires);

        // Not using datatype updates below to ensure that we get a warning if a
        // type gets new arguments
        match e {
          case Var(_) => e
          case Literal(lit_) => e
          case Abs(vars, body) => Expr.Abs(vars, Map_Expr(body, tr))
          case Apply(aop, exprs) =>
            var exprs' := Seq.Map(e requires e in exprs => Map_Expr(e, tr), exprs);
            Predicates.Map_All_IsMap(e requires e in exprs => Map_Expr(e, tr), exprs);
            var e' := Expr.Apply(aop, exprs');
            assert Exprs.ConstructorsMatch(e, e');
            e'

          // Statements
          case Block(exprs) =>
            var exprs' := Seq.Map(e requires e in exprs => Map_Expr(e, tr), exprs);
            Predicates.Map_All_IsMap(e requires e in exprs => Map_Expr(e, tr), exprs);
            var e' := Expr.Block(exprs');
            assert Exprs.ConstructorsMatch(e, e');
            e'
          case Bind(vars, vals, body) =>
            var vals' := Seq.Map(e requires e in vals => Map_Expr(e, tr), vals);
            Predicates.Map_All_IsMap(e requires e in vals => Map_Expr(e, tr), vals);
            var e' := Expr.Bind(vars, vals', Map_Expr(body, tr));
            assert Exprs.ConstructorsMatch(e, e');
            e'
          case If(cond, thn, els) =>
            var e' := Expr.If(Map_Expr(cond, tr), Map_Expr(thn, tr), Map_Expr(els, tr));
            assert Exprs.ConstructorsMatch(e, e');
            e'
        }
      }

      function method Map_Expr(e: Expr, tr: BottomUpTransformer) : (e': Expr)
        decreases e, 1
        requires Deep.All_Expr(e, tr.f.requires)
        ensures Deep.All_Expr(e', tr.Post)
      {
        Deep.AllImpliesChildren(e, tr.f.requires);
        tr.f(MapChildren_Expr(e, tr))
      }

      function method Map_Expr_Transformer(tr: BottomUpTransformer) : (tr': ExprTransformer)
      {
        TR(e requires Deep.All_Expr(e, tr.f.requires) => Map_Expr(e, tr),
           e' => Deep.All_Expr(e', tr.Post))
      }

      function method {:opaque} Map_Method(m: Method, tr: BottomUpTransformer) : (m': Method)
        requires Deep.All_Method(m, tr.f.requires)
        ensures Deep.All_Method(m', tr.Post)
      {
        Shallow.Map_Method(m, Map_Expr_Transformer(tr))
      }

      function method {:opaque} Map_Program(p: Program, tr: BottomUpTransformer) : (p': Program)
        requires Deep.All_Program(p, tr.f.requires)
        ensures Deep.All_Program(p', tr.Post)
      {
        Shallow.Map_Program(p, Map_Expr_Transformer(tr))
      }
    }
}
