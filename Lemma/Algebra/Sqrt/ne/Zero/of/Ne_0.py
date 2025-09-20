from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    return Unequal(sqrt(x), 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, 0))

    Eq << ~Eq[-1]

    Eq << Algebra.EqPowS.of.Eq.apply(Eq[-1], exp=2)
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-07-16
