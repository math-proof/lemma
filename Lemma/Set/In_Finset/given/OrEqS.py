from util import *


@apply
def apply(given):
    e, finiteset = given.of(Element[FiniteSet])

    return Or(*(Equal(e, s) for s in finiteset))


@prove
def prove(Eq):
    from Lemma import Set

    e, a, b, c = Symbol(integer=True, given=True)
    Eq << apply(Element(e, {a, b, c}))

    Eq << Set.In.Finset.of.Or_Eq.apply(Eq[1])












if __name__ == '__main__':
    run()
# created on 2018-11-18
