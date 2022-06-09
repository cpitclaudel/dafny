include "CompilerCommon.dfy"
include "Library.dfy"
include "Values.dfy"

module Interp {
  import Lib.Math
  import Lib.Debug
  import Lib.Seq

  import V = Values
  import DafnyCompilerCommon.AST.Types
  import DafnyCompilerCommon.AST.Exprs

  import opened Lib.Datatypes
  import opened DafnyCompilerCommon.Predicates

  // FIXME move
  predicate method Pure1(e: Exprs.T) {
    match e {
      case Var(_) => true
      case Literal(lit) => true
      case Abs(vars, body) => true
      case Apply(Lazy(op), args) =>
        true
      case Apply(Eager(op), args) =>
        match op {
          case UnaryOp(uop) => true
          case BinaryOp(bop) => true
          case TernaryOp(top) => true
          case Builtin(Display(_)) => true
          case Builtin(Print) => false
          case FunctionCall() => true
          case DataConstructor(name, typeArgs) => true
        }
      case Bind(vars, vals, body) => true
      case Block(stmts) => true
      case If(cond, thn, els) => true
    }
  }

  predicate method Pure(e: Exprs.T) {
    Predicates.Deep.All_Expr(e, Pure1)
  }

  predicate method SupportsInterp1(e: Exprs.T) {
    AST.Exprs.WellFormed(e) &&
    match e {
      case Var(_) => true
      case Literal(lit) => true
      case Abs(vars, body) => true
      case Apply(Lazy(op), args) =>
        true
      case Apply(Eager(op), args) =>
        match op {
          case UnaryOp(uop) => !uop.MemberSelect?
          case BinaryOp(bop) => !bop.BV? && !bop.Datatypes?
          case TernaryOp(top) => true
          case Builtin(Display(_)) => true
          case Builtin(Print()) => false
          case FunctionCall() => true
          case DataConstructor(name, typeArgs) => Debug.TODO(false)
        }
      case Bind(vars, vals, body) => true
      case Block(stmts) => Debug.TODO(false)
      case If(cond, thn, els) => true
    }
  }

  predicate method SupportsInterp(e: Exprs.T) {
    Predicates.Deep.All_Expr(e, SupportsInterp1)
  }

  lemma SupportsInterp_Pure(e: Exprs.T)
    requires SupportsInterp1(e)
    ensures Pure1(e)
  {}

  predicate method WellFormedValue1(v: V.T)  {
    && v.Closure? ==> SupportsInterp(v.body)
    && v.WellFormed1()
  }

  predicate method WellFormedValue(v: V.T) {
    v.All(WellFormedValue1)
  }

  predicate method WellFormedContext(ctx: V.Context) {
    forall v' | v' in ctx.Values :: WellFormedValue(v')
  }

  type Type = Types.T
  type Context = c: V.Context | WellFormedContext(c)
  type Value = v: V.T | WellFormedValue(v) witness V.Bool(false)
  type Expr = e: Exprs.T | SupportsInterp(e) witness Exprs.Literal(Exprs.LitInt(0))

  datatype State =
    State(locals: Context := map[])
  {
    static const Empty := State(map[]) // BUG(https://github.com/dafny-lang/dafny/issues/2120)
  }

  datatype Environment =
    Environment(fuel: nat, globals: Context := map[])

  datatype InterpReturn<+A> =
    | Return(ret: A, ctx: State)

  // FIXME many "Invalid" below should really be type errors

  datatype InterpError =
    | OutOfFuel(fn: Value)
    | TypeError(e: Expr, value: Value, expected: Type) // TODO rule out type errors through Wf predicate?
    | Invalid(e: Expr) // TODO rule out in Wf predicate?
    | OutOfIntBounds(x: int, low: Option<int>, high: Option<int>)
    | OutOfSeqBounds(collection: Value, idx: Value)
    | OutOfMapDomain(collection: Value, idx: Value)
    | UnboundVariable(v: string)
    | SignatureMismatch(vars: seq<string>, argvs: seq<Value>)
    | DivisionByZero
  {
    function method ToString() : string {
      match this // TODO include values in messages
        case OutOfFuel(fn) => "Too many function evaluations"
        case TypeError(e, value, expected) => "Type mismatch"
        case Invalid(e) => "Invalid expression"
        case OutOfIntBounds(x, low, high) => "Out-of-bounds value"
        case OutOfSeqBounds(v, i) => "Index out of sequence bounds"
        case OutOfMapDomain(v, i) => "Missing key in map"
        case UnboundVariable(v) => "Unbound variable '" + v + "'"
        case SignatureMismatch(vars, argvs) => "Wrong number of arguments in function call"
        case DivisionByZero() => "Division by zero"
    }
  }

  type InterpResult<+A> =
    Result<InterpReturn<A>, InterpError>

  type PureInterpResult<+A> =
    Result<A, InterpError>

  function method LiftPureResult<A>(ctx: State, r: PureInterpResult<A>)
    : InterpResult<A>
  {
    var v :- r;
    Success(Return(v, ctx))
  }

  function method Eval(e: Expr, env: Environment, ctx: State)
    : InterpResult<Value>
  {
    InterpExpr(e, env, ctx)
  }

  function method InterpExpr(e: Expr, env: Environment, ctx: State)
    : InterpResult<Value>
    decreases env.fuel, e, 1
  {
    Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
    match e {
      case Var(v) =>
        LiftPureResult(ctx, InterpVar(v, ctx, env))
      case Abs(vars, body) =>
        Success(Return(V.Closure(ctx.locals, vars, body), ctx))
      case Literal(lit) =>
        Success(Return(InterpLiteral(lit), ctx))
      case Apply(Lazy(op), args: seq<Expr>) =>
        InterpLazy(e, env, ctx)
      case Apply(Eager(op), args: seq<Expr>) =>
        var Return(argvs, ctx) :- InterpExprs(args, env, ctx);
        LiftPureResult(ctx, match op {
            case UnaryOp(op: UnaryOp) =>
              InterpUnaryOp(e, op, argvs[0])
            case BinaryOp(bop: BinaryOp) =>
              assert !bop.BV? && !bop.Datatypes?;
              InterpBinaryOp(e, bop, argvs[0], argvs[1])
            case TernaryOp(top: TernaryOp) =>
              InterpTernaryOp(e, top, argvs[0], argvs[1], argvs[2])
            case Builtin(Display(ty)) =>
              InterpDisplay(e, ty.kind, argvs)
            case FunctionCall() =>
              InterpFunctionCall(e, env, argvs[0], argvs[1..])
          })
      case Bind(vars, exprs, body) =>
        var Return(vals, ctx) :- InterpExprs(exprs, env, ctx);
        InterpBind(e, env, ctx, vars, vals, body)
      case If(cond, thn, els) =>
        var Return(condv, ctx) :- InterpExprWithType(cond, Type.Bool, env, ctx);
        if condv.b then InterpExpr(thn, env, ctx) else InterpExpr(els, env, ctx)
    }
  }

  function method InterpVar(v: string, ctx: State, env: Environment)
    : PureInterpResult<Value>
  {
    match TryGetVariable(ctx.locals, v, UnboundVariable(v))
      case Success(val) => Success(val)
      case Failure(err) => TryGetVariable(env.globals, v, err)
  }

  function method {:opaque} TryGetVariable(ctx: Context, k: string, err: InterpError)
    : (r: PureInterpResult<Value>)
    ensures r.Success? ==> k in ctx && r.value == ctx[k]
    ensures r.Failure? ==> k !in ctx && r.error == err
  {
    TryGet(ctx, k, err)
  }

  function method {:opaque} TryGet<K, V>(m: map<K, V>, k: K, err: InterpError)
    : (r: PureInterpResult<V>)
    ensures r.Success? ==> k in m && r.value == m[k]
    ensures r.Failure? ==> k !in m && r.error == err
  {
    if k in m then Success(m[k]) else Failure(err)
  }

  function method TryGetPair<K, V>(m: map<K, V>, k: K, err: InterpError)
    : (r: PureInterpResult<(K, V)>)
    ensures r.Success? ==> k in m && r.value == (k, m[k])
    ensures r.Failure? ==> k !in m && r.error == err
  {
    if k in m then Success((k, m[k])) else Failure(err)
  }

  function method MapOfPairs<K, V>(pairs: seq<(K, V)>)
    : (m: map<K, V>)
    ensures forall k | k in m :: (k, m[k]) in pairs
  {
    if pairs == [] then map[]
    else
      var lastidx := |pairs| - 1;
      MapOfPairs(pairs[..lastidx])[pairs[lastidx].0 := pairs[lastidx].1]
  }

  function method InterpExprWithType(e: Expr, ty: Type, env: Environment, ctx: State)
    : (r: InterpResult<Value>)
    decreases env.fuel, e, 2
    ensures r.Success? ==> r.value.ret.HasType(ty)
  {
    var Return(val, ctx) :- InterpExpr(e, env, ctx);
    :- Need(val.HasType(ty), TypeError(e, val, ty));
    Success(Return(val, ctx))
  }

  function method NeedType(e: Expr, val: Value, ty: Type)
    : (r: Outcome<InterpError>)
    ensures r.Pass? ==> val.HasType(ty)
  {
    Need(val.HasType(ty), TypeError(e, val, ty))
  }

  function method NeedTypes(es: seq<Expr>, vs: seq<Value>, ty: Type)
    : (r: Outcome<InterpError>)
    requires |es| == |vs|
    decreases |es|
    // DISCUSS: Replacing this with <==> doesn't verify
    ensures r.Pass? ==> forall v | v in vs :: v.HasType(ty)
    ensures r.Pass? <== forall v | v in vs :: v.HasType(ty)
  {
    if es == [] then
      assert vs == []; Pass
    else
      // DISCUSS: No `:-` for outcomes?
      // DISCUSS: should match accept multiple discriminands? (with lazy evaluation?)
      match NeedType(es[0], vs[0], ty)
        case Pass =>
          assert vs[0].HasType(ty);
          match NeedTypes(es[1..], vs[1..], ty) { // TODO check that compiler does this efficiently
            case Pass => assert forall v | v in vs[1..] :: v.HasType(ty); Pass
            case fail => fail
          }
        case fail => fail
  }

  function method InterpExprs(es: seq<Expr>, env: Environment, ctx: State)
    : (r: InterpResult<seq<Value>>)
    decreases env.fuel, es
    ensures r.Success? ==> |r.value.ret| == |es|
  { // TODO generalize into a FoldResult function
    if es == [] then Success(Return([], ctx))
    else
      var Return(v, ctx) :- InterpExpr(es[0], env, ctx);
      var Return(vs, ctx) :- InterpExprs(es[1..], env, ctx);
      Success(Return([v] + vs, ctx))
  }

  function method InterpLiteral(a: AST.Exprs.Literal)
    : Value
  {
    match a
      case LitBool(b: bool) => V.Bool(b)
      case LitInt(i: int) => V.Int(i)
      case LitReal(r: real) => V.Real(r)
      case LitChar(c: char) => V.Char(c)
      case LitString(s: string, verbatim: bool) =>
        var chars := seq(|s|, i requires 0 <= i < |s| => V.Char(s[i]));
        assert forall c | c in chars :: WellFormedValue(c);
        V.Seq(chars)
  }

  function method InterpLazy(e: Expr, env: Environment, ctx: State)
    : InterpResult<Value>
    requires e.Apply? && e.aop.Lazy?
    decreases env.fuel, e, 0
  {
    Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
    var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
    var Return(v0, ctx0) :- InterpExprWithType(e0, Type.Bool, env, ctx);
    match (op, v0)
      case (And, Bool(false)) => Success(Return(V.Bool(false), ctx0))
      case (Or,  Bool(true))  => Success(Return(V.Bool(true), ctx0))
      case (Imp, Bool(false)) => Success(Return(V.Bool(true), ctx0))
      case (_,   Bool(b)) =>
        assert op in {Exprs.And, Exprs.Or, Exprs.Imp};
        InterpExprWithType(e1, Type.Bool, env, ctx0)
  }

  // Alternate implementation of ``InterpLazy``: less efficient but more closely
  // matching intuition (may not terminate).
  function method InterpLazy_Eagerly(e: Expr, env: Environment, ctx: State)
    : InterpResult<Value>
    requires e.Apply? && e.aop.Lazy?
    decreases env.fuel, e, 0
  {
    Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
    var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
    var Return(v0, ctx0) :- InterpExprWithType(e0, Type.Bool, env, ctx);
    var Return(v1, ctx1) :- InterpExprWithType(e1, Type.Bool, env, ctx0);
    match (op, v0, v1)
      case (And, Bool(b0), Bool(b1)) =>
        Success(Return(V.Bool(b0 && b1), if b0 then ctx1 else ctx0))
      case (Or,  Bool(b0), Bool(b1)) =>
        Success(Return(V.Bool(b0 || b1), if b0 then ctx0 else ctx1))
      case (Imp, Bool(b0), Bool(b1)) =>
        Success(Return(V.Bool(b0 ==> b1), if b0 then ctx1 else ctx0))
  }

  lemma InterpLazy_Complete(e: Expr, env: Environment, ctx: State)
    requires e.Apply? && e.aop.Lazy?
    requires InterpLazy(e, env, ctx).Failure?
    ensures InterpLazy_Eagerly(e, env, ctx) == InterpLazy(e, env, ctx)
  {}

  lemma InterpLazy_Eagerly_Sound(e: Expr, env: Environment, ctx: State)
    requires e.Apply? && e.aop.Lazy?
    requires InterpLazy_Eagerly(e, env, ctx).Success?
    ensures InterpLazy_Eagerly(e, env, ctx) == InterpLazy(e, env, ctx)
  {}

  function method InterpUnaryOp(expr: Expr, op: AST.UnaryOp, v0: Value)
    : PureInterpResult<Value>
    requires !op.MemberSelect?
  {
    match op
      case BVNot => :- Need(v0.BitVector?, Invalid(expr));
        Success(V.BitVector(v0.width, Math.IntPow(2, v0.width) - 1 - v0.value))
      case BoolNot => :- Need(v0.Bool?, Invalid(expr));
        Success(V.Bool(!v0.b))
      case SeqLength => :- Need(v0.Seq?, Invalid(expr));
        Success(V.Int(|v0.sq|))
      case SetCard => :- Need(v0.Set?, Invalid(expr));
        Success(V.Int(|v0.st|))
      case MultisetCard => :- Need(v0.Multiset?, Invalid(expr));
        Success(V.Int(|v0.ms|))
      case MapCard => :- Need(v0.Map?, Invalid(expr));
        Success(V.Int(|v0.m|))
  }

  function method InterpBinaryOp(expr: Expr, bop: AST.BinaryOp, v0: Value, v1: Value)
    : PureInterpResult<Value>
    requires !bop.BV? && !bop.Datatypes?
  {
    match bop
      case Numeric(op) => InterpBinaryNumeric(expr, op, v0, v1)
      case Logical(op) => InterpBinaryLogical(expr, op, v0, v1)
      case Eq(op) => match op { // FIXME which types is this Eq applicable to (vs. the type-specific ones?)
        case EqCommon() => Success(V.Bool(v0 == v1))
        case NeqCommon() => Success(V.Bool(v0 != v1))
      }
      // case BV(op) =>
      case Char(op) => InterpBinaryChar(expr, op, v0, v1)
      case Sets(op) => InterpBinarySets(expr, op, v0, v1)
      case Multisets(op) => InterpBinaryMultisets(expr, op, v0, v1)
      case Sequences(op) => InterpBinarySequences(expr, op, v0, v1)
      case Maps(op) => InterpBinaryMaps(expr, op, v0, v1)
      // case Datatypes(op) =>
  }

  function method InterpBinaryNumeric(expr: Expr, op: Exprs.BinaryOps.Numeric, v0: Value, v1: Value)
    : PureInterpResult<Value>
  {
    match (v0, v1) {
      // Separate functions to more easily check exhaustiveness
      case (Int(x1), Int(x2)) => InterpBinaryInt(expr, op, x1, x2)
      case (Char(x1), Char(x2)) => InterpBinaryNumericChar(expr, op, x1, x2)
      case (Real(x1), Real(x2)) => InterpBinaryReal(expr, op, x1, x2)
      case _ => Failure(Invalid(expr)) // FIXME: Wf
    }
  }

  function method CheckDivisionByZero(b: bool) : Outcome<InterpError> {
    if b then Fail(DivisionByZero) else Pass
  }

  function method InterpBinaryInt(expr: Expr, bop: AST.BinaryOps.Numeric, x1: int, x2: int)
    : PureInterpResult<Value>
  {
    match bop {
      case Lt() => Success(V.Bool(x1 < x2))
      case Le() => Success(V.Bool(x1 <= x2))
      case Ge() => Success(V.Bool(x1 >= x2))
      case Gt() => Success(V.Bool(x1 > x2))
      case Add() => Success(V.Int(x1 + x2))
      case Sub() => Success(V.Int(x1 - x2))
      case Mul() => Success(V.Int(x1 * x2))
      case Div() => :- CheckDivisionByZero(x2 == 0); Success(V.Int(x1 / x2))
      case Mod() => :- CheckDivisionByZero(x2 == 0); Success(V.Int(x1 % x2))
    }
  }

  function method NeedIntBounds(x: int, low: int, high: int) : PureInterpResult<int> {
    :- Need(low <= x < high, OutOfIntBounds(x, Some(low), Some(high)));
    Success(x)
  }

  function method InterpBinaryNumericChar(expr: Expr, bop: AST.BinaryOps.Numeric, x1: char, x2: char)
    : PureInterpResult<Value>
  {
    match bop { // FIXME: These first four cases are not used (see InterpBinaryChar instead)
      case Lt() => Success(V.Bool(x1 < x2))
      case Le() => Success(V.Bool(x1 <= x2))
      case Ge() => Success(V.Bool(x1 >= x2))
      case Gt() => Success(V.Bool(x1 > x2))
      case Add() => var x :- NeedIntBounds(x1 as int + x2 as int, 0, 256); Success(V.Char(x as char))
      case Sub() => var x :- NeedIntBounds(x1 as int - x2 as int, 0, 256); Success(V.Char(x as char))
      case Mul() => Failure(Invalid(expr))
      case Div() => Failure(Invalid(expr))
      case Mod() => Failure(Invalid(expr))
    }
  }

  function method InterpBinaryReal(expr: Expr, bop: AST.BinaryOps.Numeric, x1: real, x2: real)
    : PureInterpResult<Value>
  {
    match bop {
      case Lt() => Success(V.Bool(x1 < x2))
      case Le() => Success(V.Bool(x1 <= x2))
      case Ge() => Success(V.Bool(x1 >= x2))
      case Gt() => Success(V.Bool(x1 > x2))
      case Add() => Success(V.Real(x1 + x2))
      case Sub() => Success(V.Real(x1 - x2))
      case Mul() => Success(V.Real(x1 * x2))
      case Div() => :- CheckDivisionByZero(x2 == 0 as real); Success(V.Real(x1 / x2))
      case Mod() => Failure(Invalid(expr))
    }
  }

  function method InterpBinaryLogical(expr: Expr, op: Exprs.BinaryOps.Logical, v0: Value, v1: Value)
    : PureInterpResult<Value>
  {
    :- Need(v0.Bool? && v1.Bool?, Invalid(expr));
    match op
      case Iff() =>
        Success(V.Bool(v0.b <==> v1.b))
  }

  function method InterpBinaryChar(expr: Expr, op: AST.BinaryOps.Char, v0: Value, v1: Value)
    : PureInterpResult<Value>
  { // FIXME eliminate distinction between GtChar and GT?
    :- Need(v0.Char? && v1.Char?, Invalid(expr));
    match op
      case LtChar() =>
        Success(V.Bool(v0.c < v1.c))
      case LeChar() =>
        Success(V.Bool(v0.c <= v1.c))
      case GeChar() =>
        Success(V.Bool(v0.c >= v1.c))
      case GtChar() =>
        Success(V.Bool(v0.c > v1.c))
  }

  function method InterpBinarySets(expr: Expr, op: Exprs.BinaryOps.Sets, v0: Value, v1: Value)
    : PureInterpResult<Value>
  {
    match op
      case SetEq() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st == v1.st))
      case SetNeq() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st != v1.st))
      case Subset() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st <= v1.st))
      case Superset() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st >= v1.st))
      case ProperSubset() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st < v1.st))
      case ProperSuperset() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st > v1.st))
      case Disjoint() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st !! v1.st))
      case Union() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Set(v0.st + v1.st))
      case Intersection() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Set(v0.st * v1.st))
      case SetDifference() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Set(v0.st - v1.st))
      case InSet() => :- Need(v1.Set?, Invalid(expr));
        Success(V.Bool(v0 in v1.st))
      case NotInSet() => :- Need(v1.Set?, Invalid(expr));
        Success(V.Bool(v0 !in v1.st))
  }

  function method InterpBinaryMultisets(expr: Expr, op: Exprs.BinaryOps.Multisets, v0: Value, v1: Value)
    : PureInterpResult<Value>
  {
    match op // DISCUSS
      case MultisetEq() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms == v1.ms))
      case MultisetNeq() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms != v1.ms))
      case MultiSubset() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms <= v1.ms))
      case MultiSuperset() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms >= v1.ms))
      case ProperMultiSubset() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms < v1.ms))
      case ProperMultiSuperset() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms > v1.ms))
      case MultisetDisjoint() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms !! v1.ms))
      case MultisetUnion() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Multiset(v0.ms + v1.ms))
      case MultisetIntersection() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Multiset(v0.ms * v1.ms))
      case MultisetDifference() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Multiset(v0.ms - v1.ms))
      case InMultiset() => :- Need(v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0 in v1.ms))
      case NotInMultiset() => :- Need(v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0 !in v1.ms))
      case MultisetSelect() => :- Need(v0.Multiset?, Invalid(expr));
        Success(V.Int(v0.ms[v1]))
  }

  function method InterpBinarySequences(expr: Expr, op: Exprs.BinaryOps.Sequences, v0: Value, v1: Value)
    : PureInterpResult<Value>
  {
    match op
      case SeqEq() => :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        Success(V.Bool(v0.sq == v1.sq))
      case SeqNeq() => :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        Success(V.Bool(v0.sq != v1.sq))
      case Prefix() => :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        Success(V.Bool(v0.sq <= v1.sq))
      case ProperPrefix() => :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        Success(V.Bool(v0.sq < v1.sq))
      case Concat() => :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        Success(V.Seq(v0.sq + v1.sq))
      case InSeq() => :- Need(v1.Seq?, Invalid(expr));
        Success(V.Bool(v0 in v1.sq))
      case NotInSeq() => :- Need(v1.Seq?, Invalid(expr));
        Success(V.Bool(v0 !in v1.sq))
      case SeqDrop() => :- NeedValidEndpoint(expr, v0, v1);
        Success(V.Seq(v0.sq[v1.i..]))
      case SeqTake() => :- NeedValidEndpoint(expr, v0, v1);
        Success(V.Seq(v0.sq[..v1.i]))
      case SeqSelect() => :- NeedValidIndex(expr, v0, v1);
        Success(v0.sq[v1.i])
  }

  function method InterpBinaryMaps(expr: Expr, op: Exprs.BinaryOps.Maps, v0: Value, v1: Value)
    : PureInterpResult<Value>
  {
    match op
      case MapEq() => :- Need(v0.Map? && v1.Map?, Invalid(expr));
        Success(V.Bool(v0.m == v1.m))
      case MapNeq() => :- Need(v0.Map? && v1.Map?, Invalid(expr));
        Success(V.Bool(v0.m != v1.m))
      case MapMerge() => :- Need(v0.Map? && v1.Map?, Invalid(expr));
        Success(V.Map(v0.m + v1.m))
      case MapSubtraction() => :- Need(v0.Map? && v1.Set?, Invalid(expr));
        Success(V.Map(v0.m - v1.st))
      case InMap() => :- Need(v1.Map?, Invalid(expr));
        Success(V.Bool(v0 in v1.m))
      case NotInMap() => :- Need(v1.Map?, Invalid(expr));
        Success(V.Bool(v0 !in v1.m))
      case MapSelect() =>
        :- Need(v0.Map?, Invalid(expr));
        :- Need(v1 in v0.m, OutOfMapDomain(v0, v1));
        Success(v0.m[v1])
  }

  function method InterpTernaryOp(expr: Expr, top: AST.TernaryOp, v0: Value, v1: Value, v2: Value)
    : PureInterpResult<Value>
  {
    match top
      case Sequences(op) =>
        InterpTernarySequences(expr, op, v0, v1, v2)
      case Multisets(op) =>
        InterpTernaryMultisets(expr, op, v0, v1, v2)
      case Maps(op) =>
        InterpTernaryMaps(expr, op, v0, v1, v2)
  }

  function method NeedValidIndex(expr: Expr, vs: Value, vidx: Value)
    : Outcome<InterpError>
  { // FIXME no monadic operator for combining outcomes?
    match Need(vidx.Int? && vs.Seq?, Invalid(expr))
      case Pass() => Need(0 <= vidx.i < |vs.sq|, OutOfSeqBounds(vs, vidx))
      case fail => fail
  }

  function method NeedValidEndpoint(expr: Expr, vs: Value, vidx: Value)
    : Outcome<InterpError>
  {
    match Need(vidx.Int? && vs.Seq?, Invalid(expr))
      case Pass() => Need(0 <= vidx.i <= |vs.sq|, OutOfSeqBounds(vs, vidx))
      case fail => fail
  }

  function method InterpTernarySequences(expr: Expr, op: AST.TernaryOps.Sequences, v0: Value, v1: Value, v2: Value)
    : PureInterpResult<Value>
  {
    match op
      case SeqUpdate() => :- NeedValidIndex(expr, v0, v1);
        Success(V.Seq(v0.sq[v1.i := v2]))
      case SeqSubseq() =>
        :- NeedValidEndpoint(expr, v0, v2);
        :- Need(v1.Int?, Invalid(expr));
        :- Need(0 <= v1.i <= v2.i, OutOfIntBounds(v1.i, Some(0), Some(v2.i)));
        Success(V.Seq(v0.sq[v1.i..v2.i]))
  }

  function method InterpTernaryMultisets(expr: Expr, op: AST.TernaryOps.Multisets, v0: Value, v1: Value, v2: Value)
    : PureInterpResult<Value>
  {
    match op
      case MultisetUpdate() =>
        :- Need(v0.Multiset?, Invalid(expr));
        :- Need(v2.Int? && v2.i >= 0, Invalid(expr));
        Success(V.Multiset(v0.ms[v1 := v2.i]))
  }

  function method InterpTernaryMaps(expr: Expr, op: AST.TernaryOps.Maps, v0: Value, v1: Value, v2: Value)
    : PureInterpResult<Value>
  {
    match op
      case MapUpdate() => :- Need(v0.Map?, Invalid(expr));
        Success(V.Map(v0.m[v1 := v2]))
  }

  function method InterpDisplay(e: Expr, kind: Types.CollectionKind, argvs: seq<Value>)
    : PureInterpResult<Value>
  {
    match kind
      case Map(_) => var m :- InterpMapDisplay(e, argvs); Success(V.Map(m))
      case Multiset() => Success(V.Multiset(multiset(argvs)))
      case Seq() => Success(V.Seq(argvs))
      case Set() => Success(V.Set(set s | s in argvs))
  }

  function method InterpMapDisplay(e: Expr, argvs: seq<Value>)
    : PureInterpResult<map<Value, Value>>
  {
    var pairs :- Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e, argv));
    Success(MapOfPairs(pairs))
  }

  function method PairOfMapDisplaySeq(e: Expr, argv: Value)
    : PureInterpResult<(Value, Value)>
  {
    :- Need(argv.Seq? && |argv.sq| == 2, Invalid(e));
    Success((argv.sq[0], argv.sq[1]))
  }

  function method AugmentContext(base: Context, vars: seq<string>, vals: seq<Value>)
    : Context
    requires |vars| == |vals|
  {
    base + MapOfPairs(Seq.Zip(vars, vals))
  }

  function method InterpFunctionCall(e: Expr, env: Environment, fn: Value, argvs: seq<Value>)
    : PureInterpResult<Value>
    decreases env.fuel, e, 0
  {
    :- Need(env.fuel > 0, OutOfFuel(fn));
    :- Need(fn.Closure?, Invalid(e));
    Predicates.Deep.AllImpliesChildren(fn.body, SupportsInterp1);
    :- Need(|fn.vars| == |argvs|, SignatureMismatch(fn.vars, argvs));
    var ctx := State(locals := AugmentContext(fn.ctx, fn.vars, argvs));
    var Return(val, ctx) :- InterpExpr(fn.body, env.(fuel := env.fuel - 1), ctx);
    Success(val)
  }

  function method InterpBind(e: Expr, env: Environment, ctx: State, vars: seq<string>, vals: seq<Value>, body: Expr)
    : InterpResult<Value>
    requires body < e
    requires |vars| == |vals|
    decreases env.fuel, e, 0
  {
    var bodyCtx := ctx.(locals := AugmentContext(ctx.locals, vars, vals));
    var Return(val, bodyCtx) :- InterpExpr(body, env, bodyCtx);
    var ctx := ctx.(locals := ctx.locals + (bodyCtx.locals - set v | v in vars)); // Preserve mutation
    Success(Return(val, ctx))
  }
}
