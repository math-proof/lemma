from util import *


@apply
def apply(given):
    x, y = given.of(LessEqual)
    return Equal(abs(x - y), -x + y)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x <= y)

    Eq << Algebra.Le_0.of.Le.apply(Eq[0])

    Eq << Algebra.EqAbs.of.Le_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-10-30
