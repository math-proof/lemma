from util import *


@apply
def apply(x):
    return Less(x, Floor(x) + 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Rat
    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Rat.Floor.gt.Sub_1.apply(x)

    Eq << Eq[-1] + 1

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2018-06-17
