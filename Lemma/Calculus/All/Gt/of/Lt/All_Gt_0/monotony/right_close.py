from util import *


@apply
def apply(lt, given):
    a, b = lt.of(Less)
    (fx, (x, S[1])), (S[x], domain) = given.of(All[Derivative > 0])
    S[a], S[b] = domain.of(Interval)
    assert domain.is_closed

    return All[x:Interval(a, b, left_open=True)](Greater(fx, fx._subs(x, a)))


@prove(proved=False)
def prove(Eq):
    from Lemma import Set, Calculus, Algebra

    a, b = Symbol(real=True, given=True)
    domain = Interval(a, b)
    x, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a < b, All[x:domain](Derivative[x](f(x)) > 0))

    Eq << Eq[1].this.expr.apply(Set.IsReal.of.Gt_0)

    Eq.is_continuous = Calculus.IsContinuous.of.IsDifferentiable.apply(Eq[-1])

    Eq.is_differentiable = Set.AllIn_SDiff.of.All.apply(Eq[-1], Interval(a, b, left_open=True, right_open=True))

    Eq.le = Element(t, Interval(a, b, left_open=True)).this.apply(Set.Le.of.In_Icc)

    Eq <<= Logic.Imp_And.of.Cond.Imp.apply(Eq.is_continuous, Eq.le), Logic.Imp_And.of.Cond.Imp.apply(Eq.is_differentiable, Eq.le)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.All.of.Le.All.limits.restrict), Eq[-1].this.rhs.apply(Algebra.All.of.Le.All.limits.restrict)

    Eq <<= Element(t, Interval(a, b, left_open=True)).this.apply(Set.Lt.of.In_Icc) & Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Calculus.Any.Eq.of.Lt.IsContinuous.IsDifferentiable.mean_value_theorem.Lagrange)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.And.of.Any.limits.Cond, simplify=None)

    Eq << Eq[-1].this.rhs.find(Element).apply(Set.Ne_Empty.of.In, simplify=None)

    Eq.any = Eq[-1].this.rhs.find(Unequal).apply(Set.Sub.gt.Zero.of.Ioc.ne.Empty, simplify=None)

    Eq << Logic.Imp_And.of.Cond.Imp.apply(Eq[1], Eq.le)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.of.Le.All.limits.restrict)

    Eq << Eq[-1].this.find(All).apply(Set.AllIn_SDiff.of.All, Interval(a, t, left_open=True, right_open=True))

    Eq <<= Eq.any & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Logic.Any_And.of.Any.All.All_Imp)

    Eq << Eq[-1].this.rhs.apply(Logic.AnySetOf.of.Any_And, index=1)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Gt_0.of.Gt_0.Gt_0)

    Eq << Eq[-1].this.rhs.apply(Logic.Any_And.of.AnySetOf_AnySetOf)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Gt.of.Gt.Eq)

    Eq << Logic.Imp.of.Imp_And.apply(Eq[-1], 1)

    Eq << Logic.All.of.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Algebra.Gt.of.Sub.gt.Zero)




if __name__ == '__main__':
    run()
# created on 2020-04-22
# updated on 2023-04-16
