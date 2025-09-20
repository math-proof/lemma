from util import *


@apply
def apply(given):
    x = given.of(Expr < 0)

    return Less(Floor(x), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    x = Symbol(real=True, given=True)
    Eq << apply(x < 0)

    Eq << Algebra.Le.of.Lt.apply(Eq[0])

    Eq << Algebra.Floor.le.Zero.of.Le_0.apply(Eq[-1])

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Set.In.of.Floor.eq.Zero.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]




if __name__ == '__main__':
    run()
# created on 2020-01-20
# updated on 2025-04-10
