from util import *


@apply
def apply(A, B):
    return LessEqual(Card(Union(A, B)), Card(A) + Card(B))


@prove
def prove(Eq):
    from Lemma import Set
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(A, B)

    Eq << Set.CardUnion.eq.Sub_.AddCards.CardInter.principle.inclusion_exclusion.apply(A, B).reversed

    Eq << Eq[-1] + Eq[-2]


if __name__ == '__main__':
    run()

# created on 2020-07-06
