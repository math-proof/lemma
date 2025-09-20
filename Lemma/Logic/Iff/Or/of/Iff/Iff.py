from util import *


@apply
def apply(eq_ab, eq_xy):
    a, b = eq_ab.of(Iff)
    x, y = eq_xy.of(Iff)
    return Iff(a | x, b | y)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, b, x, y = Symbol(integer=True)
    Eq << apply(Iff(a > 0, b > 0), Iff(x > 0, y > 0))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[-1])

    Eq << Logic.Imp.of.Iff.apply(Eq[0])

    Eq << Logic.Imp.of.Iff.apply(Eq[1])

    Eq << Logic.ImpOrS.of.Imp.Imp.apply(Eq[-2], Eq[-1])

    Eq << Logic.Imp.of.Iff.apply(Eq[0], reverse=True)

    Eq << Logic.Imp.of.Iff.apply(Eq[1], reverse=True)

    Eq << Algebra.Given.Or.of.Given.Given.apply(Eq[-2], Eq[-1]).reversed





if __name__ == '__main__':
    run()
# created on 2019-02-09
# updated on 2025-04-12
