from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    return Equal(Card(S | {e}), Card(S) + 1)


@prove
def prove(Eq):
    from Lemma import Set, Finset

    S = Symbol(etype=dtype.integer)
    e = Symbol(integer=True)
    Eq << apply(NotElement(e, S))

    Eq << Set.Inter_Finset.eq.Empty.of.NotIn.apply(Eq[0])

    Eq << Finset.CardUnion.eq.AddCardS.of.Inter.eq.Empty.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-17
