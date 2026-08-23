from util import *


@apply
def apply(le):
    (fx, *limits), M = le.of(Sup <= Expr)
    return All(fx <= M, *limits)


@prove
def prove(Eq):
    from Lemma import Bool, Nat, Real, Tensor

    m, M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:Interval(m, M, left_open=True, right_open=True)](f(x)) <= M)

    Eq << Eq[0].this.lhs.apply(Real.Sup.eq.ReducedMin)

    Eq << Eq[-1].this.lhs.apply(Tensor.ReducedMin.eq.Minima)

    Eq << Real.Any.Le.of.LeMinima.apply(Eq[-1])

    Eq << Bool.Any_And.of.AnySetOf_AnySetOf.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Bool.All.And.of.Cond.All, simplify=None)

    Eq << Eq[-1].this.expr.expr.apply(Nat.Le.of.Le.Le)


if __name__ == '__main__':
    run()
# created on 2018-12-27
# updated on 2021-09-30
