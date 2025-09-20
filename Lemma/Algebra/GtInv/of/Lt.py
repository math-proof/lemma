from util import *


@apply
def apply(ge):
    x, a = ge.of(Less)
    assert x > 0

    return Greater(1 / x, 1 / a)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True, positive=True)
    a = Symbol(real=True)
    Eq << apply(x < a)

    Eq << Algebra.Gt_0.of.Lt.trans.apply(Eq[0])

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.LtMul.of.Gt_0.Lt.apply(Eq[-1], Eq[0])

    Eq << Eq[1] * x

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-12-29
