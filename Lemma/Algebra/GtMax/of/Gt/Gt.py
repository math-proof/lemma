from util import *


@apply
def apply(gt_a, gt_b):
    x, a = gt_a.of(Greater)
    y, b = gt_b.of(Greater)
    return Max(x, y) > Max(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, a, b = Symbol(real=True, given=True)
    Eq << apply(x > a, y > b)

    Eq << Algebra.LtMax.of.Lt.Lt.apply(Eq[0].reversed, Eq[1].reversed)

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2019-03-09
# updated on 2023-04-23

