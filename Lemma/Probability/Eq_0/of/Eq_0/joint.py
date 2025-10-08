from util import *


@apply
def apply(given, x):
    cond = given.of(Equal[Pr, 0])
    cond &= Equal(x, x.var)
    return Equal(Pr(cond), 0)


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Bool

    x, y = Symbol(real=True, random=True)
    Eq << apply(Equal(Pr(x), 0), y)

    Eq << Eq[1].invert().this.apply(Probability.Ne_0.of.Ne_0.delete)

    Eq << Eq[-1].this.apply(Bool.Imp.Is.ImpNotS)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-03-21
