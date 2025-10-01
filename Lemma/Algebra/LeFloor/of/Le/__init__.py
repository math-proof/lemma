from util import *


@apply
def apply(given):
    x, y = given.of(LessEqual)
    return LessEqual(Floor(x), Floor(y))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << ~Eq[1]

    Eq << Algebra.Ge_Add_1.of.Gt.apply(Eq[-1])

    Eq << Algebra.LeFloor.apply(x)

    Eq << Algebra.Ge.of.Ge.Ge.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Lt_Add_.Floor.One.apply(y)

    Eq << Algebra.Gt.of.Ge.Lt.apply(Eq[-2], Eq[-1])

    Eq <<= Eq[-1] & Eq[0]




if __name__ == '__main__':
    run()
# created on 2021-12-27


# updated on 2025-04-10
from . import integer
