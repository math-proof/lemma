from util import *


@apply
def apply(lt, gt):
    x, a = lt.of(Less)
    y, b = gt.of(Greater)

    return Less((x - a) * (y - b), 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, a, b = Symbol(real=True)
    Eq << apply(x < a, y > b)

    Eq << Eq[1].reversed

    Eq << Algebra.Gt_0.of.Lt.Lt.apply(Eq[0], Eq[-1])

    Eq << -Eq[-1]

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[2].this.lhs.expand()


if __name__ == '__main__':
    run()
# created on 2019-07-04
