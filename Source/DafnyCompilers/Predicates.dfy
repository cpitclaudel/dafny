include "AST.dfy"

module DafnyCompilerCommon.Predicates {
    import opened AST

    function IsMap<T(!new), T'>(f: T --> T') : T' -> bool {
      y => exists x | f.requires(x) :: y == f(x)
    }

    lemma Map_All_IsMap<A, B>(f: A --> B, xs: seq<A>)
      requires forall a | a in xs :: f.requires(a)
      ensures Seq.All(IsMap(f), Seq.Map(f, xs))
    {}

    lemma Map_All_PC<A, B>(f: A --> B, P: B -> bool, xs: seq<A>)
      requires forall a | a in xs :: f.requires(a)
      requires forall a | a in xs :: P(f(a))
      ensures Seq.All(P, Seq.Map(f, xs))
    {}

    function method {:opaque} MapWithPC<T, Q>(f: T ~> Q, ghost PC: Q -> bool, ts: seq<T>) : (qs: seq<Q>)
      reads f.reads
      requires forall t | t in ts :: f.requires(t)
      requires forall t | t in ts :: PC(f(t))
      ensures |qs| == |ts|
      ensures forall i | 0 <= i < |ts| :: qs[i] == f(ts[i])
      ensures forall q | q in qs :: PC(q)
      ensures Seq.All(PC, qs)
    {
      Seq.Map(f, ts)
    }

    datatype Transformer_<!A(!new), !B> =
      TR(f: A --> B, ghost Post: B -> bool)
    {
      ghost const Valid? := forall a | f.requires(a) :: Post(f(a))
    }

    type Transformer<!A(!new), !B(0)> = tr: Transformer_<A, B> | tr.Valid?
      witness *

    type ExprTransformer = Transformer<Expr, Expr>

    lemma Map_All_TR<A(!new), B(00)>(tr: Transformer<A, B>, ts: seq<A>)
      requires forall x | x in ts :: tr.f.requires(x)
      ensures Seq.All(tr.Post, Seq.Map(tr.f, ts))
    {}

    module Shallow {
      import opened Lib
      import opened AST

      function method All_Method(m: Method, P: Expr -> bool) : bool {
        match m {
          case Method(CompileName_, methodBody) => P(methodBody)
        }
      }

      function method All_Program(p: Program, P: Expr -> bool) : bool {
        match p {
          case Program(mainMethod) => All_Method(mainMethod, P)
        }
      }

      function method All(p: Program, P: Expr -> bool) : bool {
        All_Program(p, P)
      }
    }

    module DeepImpl {
      abstract module Base {
        import opened Lib
        import opened AST
        import Shallow

        function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool
          decreases e.Depth(), 0

        function method All_Expr(e: Expr, P: Expr -> bool)
          : (b: bool)
          decreases e.Depth(), 1

        function method All_Method(m: Method, P: Expr -> bool) : bool {
          Shallow.All_Method(m, e => All_Expr(e, P))
        }

        function method All_Program(p: Program, P: Expr -> bool) : bool {
          Shallow.All_Program(p, e => All_Expr(e, P))
        }

        // This lemma allows callers to force one level of unfolding of All_Expr
        lemma AllImpliesChildren(e: Expr, p: Expr -> bool)
          requires All_Expr(e, p)
          ensures AllChildren_Expr(e, p)

        lemma AllChildren_Expr_weaken(e: Exprs.T, P: Exprs.T -> bool, Q: Exprs.T -> bool)
          requires AllChildren_Expr(e, P)
          requires forall e' :: P(e') ==> Q(e')
          decreases e, 0
          ensures AllChildren_Expr(e, Q)

        lemma All_Expr_weaken(e: Exprs.T, P: Exprs.T -> bool, Q: Exprs.T -> bool)
          requires All_Expr(e, P)
          requires forall e' :: P(e') ==> Q(e')
          decreases e, 1
          ensures All_Expr(e, Q)
      }

      module Rec refines Base { // DISCUSS
        function method All_Expr(e: Expr, P: Expr -> bool) : (b: bool) {
          P(e) &&
          // BUG(https://github.com/dafny-lang/dafny/issues/2107)
          // BUG(https://github.com/dafny-lang/dafny/issues/2109)
          // Duplicated to avoid mutual recursion with AllChildren_Expr
          match e {
            case Var(_) => true
            case Literal(lit) => true
            case Abs(vars, body) => All_Expr(body, P)
            case Apply(_, exprs) =>
              Seq.All(e requires e in exprs => All_Expr(e, P), exprs)
            case Block(exprs) =>
              Seq.All((e requires e in exprs => All_Expr(e, P)), exprs)
            case Bind(vars, vals, body) =>
              Seq.All((e requires e in vals => All_Expr(e, P)), vals + [body])
            case If(cond, thn, els) =>
              All_Expr(cond, P) && All_Expr(thn, P) && All_Expr(els, P)
          }
        }

        function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool {
          match e {
            case Var(_) => true
            case Literal(lit) => true
            case Abs(vars, body) => All_Expr(body, P)
            case Apply(_, exprs) =>
              Seq.All(e requires e in exprs => All_Expr(e, P), exprs)
            case Block(exprs) =>
              Seq.All((e requires e in exprs => All_Expr(e, P)), exprs)
            case Bind(vars, vals, body) =>
              Seq.All((e requires e in vals => All_Expr(e, P)), vals + [body])
            case If(cond, thn, els) =>
              All_Expr(cond, P) && All_Expr(thn, P) && All_Expr(els, P)
          }
        }

        lemma AllExprTrue(e: Expr)
          ensures All_Expr(e, _ => true)
        {}

        lemma AllImpliesChildren ... {}

        lemma All_Expr_weaken ... {
          AllChildren_Expr_weaken(e, P, Q);
        }

        lemma AllChildren_Expr_weaken ... { // NEAT
          forall e' | e' in e.Children() { All_Expr_weaken(e', P, Q); }
        }
      }

      module NonRec refines Base {
        // BUG(https://github.com/dafny-lang/dafny/issues/2107)
        // BUG(https://github.com/dafny-lang/dafny/issues/2109)
        function method All_Expr(e: Expr, P: Expr -> bool) : (b: bool) {
          P(e) && forall e' | e' in e.Children() :: All_Expr(e', P)
        }

        function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool {
          forall e' | e' in e.Children() :: All_Expr(e', P)
        }

        lemma AllImpliesChildren ... {}

        lemma AllChildren_Expr_weaken ... {
          forall e' | e' in e.Children() { All_Expr_weaken(e', P, Q); }
        }

        lemma All_Expr_weaken ... {
          AllChildren_Expr_weaken(e, P, Q);
        }
      }

      module Equiv {
        import Rec
        import NonRec
        import opened AST

        lemma AllChildren_Expr(e: Expr, P: Expr -> bool)
          decreases e.Depth(), 0
          ensures Rec.AllChildren_Expr(e, P) == NonRec.AllChildren_Expr(e, P)
        {
          forall e' | e' in e.Children() { All_Expr(e', P); }
        }

        lemma All_Expr(e: Expr, P: Expr -> bool)
          decreases e.Depth(), 1
          ensures Rec.All_Expr(e, P) == NonRec.All_Expr(e, P)
        {
          AllChildren_Expr(e, P);
        }
      }
    }

    // Both implementations of Deep should work, but NonRec can be somewhat
    // simpler to work with.  If needed, use ``DeepImpl.Equiv.All_Expr`` to
    // switch between implementations.
    module Deep refines DeepImpl.Rec {}
}
