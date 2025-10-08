from util import *


@apply
def apply(le):
    (fx, *limits), M = le.of(Inf > Expr)
    return All(fx > M, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    y, m, M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:Interval(m, M, left_open=True, right_open=True)](f(x)) > y)

    z = Symbol(real=True)
    Eq << Algebra.Any.All.Gt.of.GtInf.apply(Eq[0], z)

    Eq << Bool.Any_And.of.AnySetOf_AnySetOf.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[0].simplify()

    Eq << Eq[-1].this.expr.apply(Algebra.All.And.of.Cond.All, simplify=None)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Gt.of.Gt.Gt)


if __name__ == '__main__':
    run()
# created on 2019-08-03
