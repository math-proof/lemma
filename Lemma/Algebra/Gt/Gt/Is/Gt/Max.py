from util import *


@apply
def apply(gt_a, gt_b):
    x, a = gt_a.of(Greater)
    S[x], b = gt_b.of(Greater)
    return x > Max(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x > y, x > b)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.GtMax.of.Gt.Gt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt.Gt.given.Gt.Max)


if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-21
