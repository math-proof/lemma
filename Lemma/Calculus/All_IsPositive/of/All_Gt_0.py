from util import *


@apply
def apply(all_is_positive):
    (fx, (x, d)), (S[x], domain) = all_is_positive.of(All[Derivative > 0])

    assert domain.left_open and domain.right_open

    return All[x:domain](Element(Derivative(fx, (x, d)), Interval.open(0, oo)))


@prove(proved=False)
def prove(Eq):
    from Lemma import Set, Algebra, Calculus

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(extended_real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(All[x:domain](Derivative[x](f(x)) > 0))

    Eq << Eq[0].this.expr.apply(Set.IsExtendedPositive.of.Gt_0)

    Eq << ~Eq[1]

    Eq << Bool.Any_And.of.Any.All.All_Imp.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.lhs.apply(Calculus.Grad.eq.Limit)

    Eq << Eq[-1].this.expr.apply(Calculus.And.Eq_Limit.of.Eq_Limit)

    Eq << Eq[-1].this.expr.args[0].apply(Calculus.LtLimit.of.Limit_Eq_Infty)

    Eq << Eq[-1].this.expr.args[1].apply(Calculus.GtLimit.of.Limit_Eq_Infty)




if __name__ == '__main__':
    run()
# created on 2020-04-28
# updated on 2023-04-16
