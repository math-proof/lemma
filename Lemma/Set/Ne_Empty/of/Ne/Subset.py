from util import *


@apply
def apply(ne, subset, evaluate=False):
    A, B = subset.of(Subset)
    S[A] = ne.of(Unequal[B])
    return Unequal(B - A, A.etype.emptySet, evaluate=evaluate)


@prove
def prove(Eq):
    from Lemma import Set
    A, B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Unequal(A, B), Subset(A, B, evaluate=False))

    Eq << ~Eq[-1]

    Eq << Set.EqUnionS.of.Eq.apply(Eq[-1], A)

    Eq << Subset(B, A | B, plausible=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq <<= Eq[-1] & Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2021-06-04
