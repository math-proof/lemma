from util import *


@apply
def apply(cond, suffice):
    S[cond], rhs = suffice.of(Imply)
    return rhs


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True, nonnegative=True, given=True)
    f, g = Symbol(integer=True, shape=(oo,), given=True)
    Eq << apply(LessEqual(f[0], g[0]), Imply(LessEqual(f[0], g[0]), LessEqual(f[n], g[n])))

    Eq << Eq[1].apply(Bool.Or.of.ImpNot)

    Eq <<= Eq[-1] & Eq[0]

    Eq << ~Eq[2]

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()
# created on 2018-01-02

