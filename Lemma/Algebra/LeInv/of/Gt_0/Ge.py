from util import *


@apply
def apply(is_positive, ge):
    a = is_positive.of(Expr > 0)
    x, a = ge.of(GreaterEqual)

    return LessEqual(1 / x, 1 / a)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, a = Symbol(real=True, given=True)
    Eq << apply(a > 0, x >= a)

    Eq << ~Eq[-1]

    Eq << Algebra.Ne.of.Gt.apply(Eq[0])

    Eq << Logic.Cond.of.Or_Not.Cond.apply(Eq[-1], Eq[-2])

    Eq.x_is_positive = Algebra.Gt.of.Gt.Ge.apply(Eq[0], Eq[1])

    Eq << Algebra.Ne.of.Gt.apply(Eq.x_is_positive)

    Eq << Logic.Cond.of.Or_Not.Cond.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Gt_0.of.Gt_0.Gt_0.apply(Eq[0], Eq.x_is_positive)

    Eq << ~Algebra.GtMul.of.Gt_0.Gt.apply(Eq[-1], Eq[-2]).reversed




if __name__ == '__main__':
    run()
# created on 2019-08-09
# updated on 2025-04-20
