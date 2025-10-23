from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    return Unequal(abs(x), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Complex

    a = Symbol(complex=True, given=True)
    Eq << apply(Unequal(a, 0))

    Eq << ~Eq[1]

    Eq << Complex.Eq_0.of.EqNorm_0.apply(Eq[-1])
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-03-17
