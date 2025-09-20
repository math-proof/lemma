from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    assert lhs.is_Intersection and rhs.is_Union or lhs.is_Union and rhs.is_Intersection
    A, B = lhs.args
    S[A], S[B] = rhs.args
    return Equal(A, B)


@prove
def prove(Eq):
    from Lemma import Set
    A, B = Symbol(etype=dtype.integer)

    Eq << apply(Equal(A & B, A | B))

    Eq << Subset(A, A | B, plausible=True).subs(Eq[0].reversed)
    Eq << Subset(A & B, B, plausible=True)

    Eq.subset = Set.Subset.of.Subset.Subset.apply(Eq[-2], Eq[-1])

    Eq << Subset(B, A | B, plausible=True).subs(Eq[0].reversed)
    Eq << Subset(A & B, A, plausible=True)

    Eq <<= Set.Subset.of.Subset.Subset.apply(Eq[-2], Eq[-1])

    Eq <<= Eq[-1] & Eq.subset

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-04-03
