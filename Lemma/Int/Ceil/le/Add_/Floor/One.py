from util import *


@apply
def apply(x):
    return LessEqual(Ceil(x), floor(x) + 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Rat

    x = Symbol(real=True, given=True)
    Eq << apply(x)

    Eq << Rat.Ceil.lt.Add_1.apply(x)

    Eq << Algebra.LeFloor.of.Lt.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-10-02
