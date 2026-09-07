from util import *


@apply
def apply(equal, subset):
    A, B = subset.of(Subset)

    A_abs, B_abs = Card(A), Card(B)

    _A_abs, _B_abs = equal.of(Equal)
    if A_abs == _A_abs:
        assert _B_abs == B_abs
    else:
        assert _B_abs == A_abs

    return Equal(A, B)


@prove
def prove(Eq):
    from Lemma import Set, Finset

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(Card(A), Card(B)), Subset(A, B))

    Eq << Set.EqUnion.of.Subset.apply(Eq[1])

    Eq << Eq[-1].apply(Finset.Card.of.Eq)

    Eq << Eq[-1].this.lhs.apply(Finset.CardUnion.eq.Add_CardSDiff, slice(1, None))

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].simplify()

    Eq << Set.Eq_Empty.of.Eq_0.apply(Eq[-1])
    Eq << Set.Subset.of.SDiff.eq.Empty.apply(Eq[-1])
    Eq <<= Eq[1] & Eq[-1]




if __name__ == '__main__':
    run()

# created on 2020-07-20
# updated on 2023-06-01
