from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    assert x >= 0
    return Greater(1 / x, 0, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    a = Symbol(nonnegative=True)
    Eq << apply(Unequal(a, 0))

    Eq << Algebra.Gt_0.of.Ne_0.apply(Eq[0])

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-22
