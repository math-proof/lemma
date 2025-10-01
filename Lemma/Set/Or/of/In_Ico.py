from util import *


@apply
def apply(given):
    e, interval = given.of(Element)
    a, b = interval.of(Range)
    size = b - a
    assert size > 0
    finiteset = {a + i for i in range(size)}

    return Or(*(Equal(e, s) for s in finiteset))


@prove
def prove(Eq):
    from Lemma import Set

    e, a = Symbol(integer=True, given=True)
    Eq << apply(Element(e, Range(a, a + 4)))

    Eq << Eq[0].this.rhs.apply(Set.Ico.eq.Finset)

    Eq << Set.Or.Eq.of.In_Finset.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-04-26
