from util import *


@apply
def apply(given):
    x, y = given.of(Less)
    return Less(floor(x), y)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat, Rat
    x, y = Symbol(real=True, given=True)

    Eq << apply(Less(x, y))

    Eq << Rat.LeFloor.apply(x)

    Eq << Nat.Lt.of.Le.Lt.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-05-18
