from util import *


@apply
def apply(given):
    x, y = given.of(Less)
    return Equal(abs(x - y), -x + y)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x < y)

    Eq << Algebra.Lt_0.of.Lt.apply(Eq[0])

    Eq << Algebra.EqAbs.of.Lt_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-12-20
