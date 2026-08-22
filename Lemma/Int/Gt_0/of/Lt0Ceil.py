from util import *


@apply
def apply(given):
    x = given.of(Ceil > 0)
    return Greater(x, 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Greater(Ceil(x), 0))

    Eq << ~Eq[-1]

    Eq << Algebra.Ceil.le.Zero.of.Le_0.apply(Eq[-1])
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-10-30
