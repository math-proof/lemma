from util import *


@apply
def apply(lt, n):
    x = lt.of(Abs[Expr] < 1)
    return Equal(Limit[n:oo](x ** n), Zeros(*x.shape))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Calculus, Bool

    n = Symbol(integer=True, positive=True)
    γ = Symbol(real=True, given=True)
    Eq << apply(Abs(γ) < 1, n)

    Eq.gt_zero, Eq.le_zero = Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=γ > 0)

    Eq.lt_zero, Eq.is_zero = Bool.Imp.given.And.Imp.split.apply(Eq.le_zero, cond=γ < 0)

    Eq << Bool.Imp.given.ImpEq.apply(Eq.is_zero)

    Eq << Bool.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq.gt_zero)

    Eq << Eq[-1].this.find(And[~Less]).apply(Algebra.Lt.of.LtAbs)

    Eq << Eq[-1].this.lhs.apply(Set.In.Icc.of.Lt.Gt)

    Eq << Eq[-1].this.lhs.apply(Calculus.Eq_0.Limit.of.In_Icc.geometric_series.positive, n)

    Eq << Bool.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq.lt_zero)

    Eq << Eq[-1].this.find(Abs < 1).apply(Algebra.Gt.of.LtAbs)

    Eq << Eq[-1].this.lhs.apply(Set.In.Icc.of.Lt.Gt)

    Eq << Eq[-1].this.lhs.apply(Calculus.Eq_0.Limit.of.In_Icc.geometric_series.negative, n)





if __name__ == '__main__':
    run()
# created on 2023-04-15
# updated on 2023-05-20
