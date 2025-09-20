from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    a = Symbol(complex=True, given=True)
    Eq << apply(Unequal(a, 0))

    Eq << ~Eq[0]

    Eq << Algebra.EqAbs.of.Eq.apply(Eq[-1])
    Eq << Eq[1].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-02-13
