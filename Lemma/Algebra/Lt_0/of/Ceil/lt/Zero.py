from util import *


@apply
def apply(given):
    x = given.of(Ceil < 0)
    return Less(x, 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Less(Ceil(x), 0))

    Eq << ~Eq[-1]

    Eq << Algebra.Ge_0.Ceil.of.Ge_0.apply(Eq[-1])


    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-03-11
