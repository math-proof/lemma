from util import *


@apply
def apply(self, *, cond=None):
    p, q = self.of(boolalg.Iff)
    return boolalg.Iff(p | cond, q | cond)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    p, q, r = Symbol(bool=True)
    Eq << apply(boolalg.Iff(p, q), cond=r)

    Eq << Logic.Imp.of.Iff.apply(Eq[0])

    Eq << Logic.Imp.Or.of.Imp.apply(Eq[-1], cond=r)

    Eq << Logic.Imp.of.Iff.apply(Eq[0], reverse=True)

    Eq << Algebra.Given.Or.of.Given.apply(Eq[-1], cond=r).reversed

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2022-01-27
# updated on 2025-04-12

del Iff
from . import Iff
