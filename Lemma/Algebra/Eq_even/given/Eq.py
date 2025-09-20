from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 0])
    return Equal((-1) ** n, 1)


@prove
def prove(Eq):
    from Lemma import Algebra
#     n = q * d + r
    n = Symbol(integer=True, given=True)

    Eq << apply(Equal(n % 2, 0))

    Eq << ~Eq[0]

    Eq << Algebra.Eq_odd.of.Ne_0.apply(Eq[-1])

    Eq << Algebra.EqPow.of.Eq_odd.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()
# created on 2019-10-10
