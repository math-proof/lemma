from util import *


@apply
def apply(le, is_positive, w=None):
    x0, x1 = le.of(LessEqual)
    fx, (x_, S[2]) = is_positive.of(Derivative > 0)

    if w is None:
        w = Symbol(domain=Interval(0, 1))
    else:
        assert 0 <= w <= 1
    domain = x_.domain
    assert domain.left_open and domain.right_open

    return GreaterEqual(w * fx._subs(x_, x0) + (1 - w) * fx._subs(x_, x1), fx._subs(x_, w * x0 + (1 - w) * x1))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Set, Logic

    a, b = Symbol(real=True, given=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    x = Symbol(domain=domain)
    f = Function(real=True)
    x0, x1 = Symbol(domain=domain, given=True)
    w = Symbol(domain=Interval(0, 1), given=True)
    Eq << apply(x0 <= x1, Derivative(f(x), (x, 2)) > 0, w=w)

    (w, fx0), (_w, fx1) = Eq[-1].lhs.of(Mul + Mul)
    x0 = fx0.arg
    x1 = fx1.arg
    Eq << Calculus.IsDifferentiable.of.Gt_0.within.apply(Eq[1], x0, x1)

    Eq << Calculus.IsContinuous.of.IsDifferentiable.apply(Eq[-1])

    Eq << Calculus.Any.Eq.of.Le.IsContinuous.IsDifferentiable.mean_value_theorem.Lagrange.close.apply(Eq[0], Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr * w

    Eq.is_nonpositive = Eq[0] - x1

    Eq <<= Algebra.LeMul.of.Le.apply(Eq.is_nonpositive, w) + x1, Algebra.GeMul.of.Ge.apply(Eq[0].reversed, 1 - w) + w * x0

    Eq << Eq[-2].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS, simplify=None)

    Eq.ge = Eq[-2].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS, simplify=None)

    Eq.le = Eq[-1].this.lhs.apply(Algebra.Add.collect, factor=x1)

    Eq.all_is_positive = Logic.All.of.Cond.apply(Eq[1], x)

    Eq.x0_contains, Eq.x1_contains = Element(x0, domain, plausible=True), Element(x1, domain, plausible=True)

    Eq.x_mean_contains = Set.In.Icc.of.In.In.apply(Eq.x0_contains, Eq.x1_contains, w)

    Eq <<= Calculus.IsDifferentiable.of.In.In.All_Gt_0.apply(Eq.x0_contains, Eq.x_mean_contains, Eq.all_is_positive), Calculus.IsDifferentiable.of.In.In.All_Gt_0.apply(Eq.x_mean_contains, Eq.x1_contains, Eq.all_is_positive)

    x_ = Symbol("x'", real=True)
    Eq << Eq[-2].limits_subs(Eq[-2].variable, x_)

    x__ = Symbol("x''", real=True)
    Eq << Eq[-1].limits_subs(Eq[-1].variable, x__)

    Eq <<= Calculus.IsContinuous.of.IsDifferentiable.apply(Eq[-2]), Calculus.IsContinuous.of.IsDifferentiable.apply(Eq[-1])

    Eq <<= Calculus.Any.Eq.of.Le.IsContinuous.IsDifferentiable.mean_value_theorem.Lagrange.close.apply(Eq.ge.reversed, Eq[-2], Eq[-4]), Calculus.Any.Eq.of.Le.IsContinuous.IsDifferentiable.mean_value_theorem.Lagrange.close.apply(Eq.le, Eq[-1], Eq[-3])

    Eq <<= Eq[-2].this.expr.rhs.args[0].apply(Algebra.Add.collect), Eq[-1].this.expr.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq <<= Eq[-2].this.expr.rhs.args[0].apply(Algebra.Add.collect, factor=1 - w), Eq[-1].this.expr.rhs.find(Add[Mul]).apply(Algebra.Add.eq.Mul)

    Eq <<= Eq[-2].this.expr * w, Eq[-1].this.expr * (1 - w)

    Eq << Algebra.Any.And.of.Any.Any.apply(Eq[-2], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.EqSub.of.Eq.Eq, swap=True)


    Eq << Eq[-1].this.expr.lhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)
    Eq << Eq[-1].this.expr.lhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)
    Eq << Eq[-1].this.expr.lhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)
    Eq << Eq[-1].this.expr.lhs.apply(Algebra.Add.collect, factor=f(x1))
    Eq.any = Eq[-1].this.expr.rhs.apply(Algebra.Add.collect, factor=w * (1 - w) * (x1 - x0))
    Eq.suffice = Eq.any.limits_cond.this.apply(Set.Le.of.In.In)
    Eq <<= Set.Subset.Icc.of.In.In.apply(Eq.x0_contains, Eq.x_mean_contains), Set.Subset.Icc.of.In.In.apply(Eq.x_mean_contains, Eq.x1_contains)
    Eq <<= Logic.Imp.of.Cond.apply(Eq[-2], cond=Eq.suffice.lhs.args[0]), Logic.Imp.of.Cond.apply(Eq[-1], cond=Eq.suffice.lhs.args[1])
    Eq <<= Logic.Imp_And.of.ImpAnd.apply(Eq[-2]), Logic.Imp_And.of.ImpAnd.apply(Eq[-1])
    Eq <<= Eq[-2].this.rhs.apply(Set.In.of.In.Subset), Eq[-1].this.rhs.apply(Set.In.of.In.Subset)
    Eq << Logic.ImpAndS.of.Imp.Imp.apply(Eq[-2], Eq[-1])
    Eq << Logic.Imp.of.Cond.apply(Eq.all_is_positive, cond=Eq[-1].lhs)
    Eq <<= Eq[-1] & Eq[-2] & Eq.suffice
    Eq << Eq[-1].this.rhs.apply(Calculus.In.of.Le.In.In.All_gt_0)
    Eq.is_nonnegative = Eq[-1].this.rhs.apply(Algebra.Ge_0.of.Le)
    Eq << GreaterEqual(w * (1 - w), 0, plausible=True)
    Eq << Algebra.Ge_0.of.Ge_0.Ge_0.apply(Eq[-1], -Eq.is_nonpositive)
    Eq << Logic.Imp.of.Cond.apply(Eq[-1], cond=Eq[-3].lhs)
    Eq <<= Eq[-1] & Eq.is_nonnegative
    Eq <<= Eq[-1].this.rhs.apply(Algebra.Ge_0.of.Ge_0.Ge_0)
    Eq << Logic.All.of.Imp.apply(Eq[-1], wrt=(x_, x__))
    Eq << Logic.Any_And.of.Any.All.All_Imp.apply(Eq[-1], Eq.any)
    Eq << Eq[-1].this.expr.apply(Algebra.Ge.of.Ge.Eq)
    Eq << Logic.And_And.of.And.apply(Eq[-1])
    Eq << Eq[-1] + Eq[2].rhs




if __name__ == '__main__':
    run()
# created on 2020-05-11
# updated on 2023-05-18
