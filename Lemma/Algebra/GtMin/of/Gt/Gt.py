from util import *


@apply
def apply(gt_0, gt_1):
    x, a = gt_0.of(Greater)
    y, b = gt_1.of(Greater)
    return Greater(Min(x, y), Min(a, b))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, b, x, y = Symbol(real=True, given=True)
    Eq << apply(x > a, y > b)

    Eq << Eq[-1].this.lhs.apply(Algebra.Min.eq.IteLe)

    Eq << Logic.BFn_Ite.given.OrAndS.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Algebra.Ge_Min.apply(a, b)

    Eq << Algebra.Gt.of.Ge.Gt.apply(Eq[0], Eq[-1])

    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq[-1], Eq[-3], invert=True)

    Eq << Algebra.Ge_Min.apply(b, a)

    Eq << Algebra.Gt.of.Gt.Ge.apply(Eq[1], Eq[-1])

    Eq << Logic.BFn.of.BFnIte.Cond.apply(Eq[-1], Eq[-3], invert=True)





if __name__ == '__main__':
    run()
# created on 2019-07-18
# updated on 2023-04-29
