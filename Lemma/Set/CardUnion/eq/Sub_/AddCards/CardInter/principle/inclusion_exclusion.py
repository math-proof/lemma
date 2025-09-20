from util import *


@apply
def apply(A, B):
    return Equal(Card(A | B), Card(A) + Card(B) - Card(A & B))


@prove
def prove(Eq):
    from Lemma import Set

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(A, B)

    Eq << Eq[-1].this.lhs.apply(Set.Card.eq.Add, slice(1, None))

    Eq << Eq[-1].this.rhs.find(Card).apply(Set.Card.eq.Add.split, A)





if __name__ == '__main__':
    run()

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml
# created on 2020-07-06
# updated on 2023-06-01
