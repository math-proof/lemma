from util import *


@apply
def apply(le):
    (fx, *limits), M = le.of(Sup <= Expr)
    return All(fx <= M, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    m, M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:Interval(m, M, left_open=True, right_open=True)](f(x)) <= M)

    Eq << Eq[0].this.lhs.apply(Algebra.Sup.eq.ReducedMin)

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedMin.eq.Minima)

    Eq << Algebra.Any.Le.of.LeMinima.apply(Eq[-1])

    Eq << Logic.Any_And.of.AnySetOf_AnySetOf.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Algebra.All.And.of.Cond.All, simplify=None)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Le.of.Le.Le)


if __name__ == '__main__':
    run()
# created on 2018-12-27
# updated on 2021-09-30
