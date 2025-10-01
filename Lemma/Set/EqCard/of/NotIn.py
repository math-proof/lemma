from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    return Equal(Card(S | {e}), Card(S) + 1)


@prove
def prove(Eq):
    from Lemma import Set

    S = Symbol(etype=dtype.integer)
    e = Symbol(integer=True)
    Eq << apply(NotElement(e, S))

    Eq << Set.Eq_Empty.Inter.of.NotIn.apply(Eq[0])

    Eq << Set.Eq.of.Inter.eq.Empty.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-17
