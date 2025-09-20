from util import *


@apply
def apply(equal, contains):
    if contains.is_Equal:
        contains, equal = equal, contains

    a, A = contains.of(Element)

    S[A] = equal.of(Equal[Card, 1])
    return Equal(A - a.set, a.emptySet)


@prove
def prove(Eq):
    from Lemma import Set

    A = Symbol(etype=dtype.integer, given=True)
    a = Symbol(integer=True, given=True)
    Eq << apply(Equal(Card(A), 1), Element(a, A))

    Eq << Set.EqFinset.of.Eq.In.apply(Eq[0], Eq[1])

    Eq << Set.EqSDiff.of.Eq.apply(Eq[-1], a.set)


if __name__ == '__main__':
    run()
# created on 2021-03-16
