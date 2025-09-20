from util import *


@apply
def apply(given):
    x, X = given.of(Element)

    return Equal(Card(X - {x}), Card(X) - 1)


@prove
def prove(Eq):
    from Lemma import Set

    e = Symbol(integer=True)
    s = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, s))

    Eq << Set.SubsetSingleton.of.In.apply(Eq[0], simplify=False)

    Eq << Set.EqUnion.of.Subset.apply(Eq[-1])

    Eq << Set.EqCard.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Set.Card.eq.Add)


    Eq << Eq[-1] - 1




if __name__ == '__main__':
    run()
# created on 2021-03-07
# updated on 2023-06-01
