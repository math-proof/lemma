from util import *


@apply
def apply(eq_ab, eq_xy):
    a, b = eq_ab.of(Iff)
    x, y = eq_xy.of(Iff)
    return Iff(a & x, b & y)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, b, x, y = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Iff(a > 0, b > 0), Iff(x > 0, y > 0))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Logic.Imp.of.Iff.apply(Eq[0])

    Eq << Logic.Imp.of.Iff.apply(Eq[1])

    Eq << Logic.ImpAndS.of.Imp.Imp.apply(Eq[-2], Eq[-1])

    Eq << Logic.Imp.of.Iff.apply(Eq[0], reverse=True)

    Eq << Logic.Imp.of.Iff.apply(Eq[1], reverse=True)

    Eq << Logic.Imp_And.of.Imp.Imp.apply(Eq[-2], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-03-28
# updated on 2025-04-12
