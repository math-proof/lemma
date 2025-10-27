from util import *


@apply
def apply(x, evaluate=False):
    return GreaterEqual(x, Floor(x), evaluate=evaluate)

@prove
def prove(Eq):
    from Lemma import Algebra, Rat

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Rat.LeFloor.apply(x)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2019-09-19
