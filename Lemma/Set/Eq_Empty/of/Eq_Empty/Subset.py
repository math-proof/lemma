from util import *


@apply
def apply(is_empty, subset):
    _B, C = is_empty.of(Equal[Intersection, EmptySet])
    A, B = subset.of(Subset)
    if B != _B:
        assert B == C
        C = _B

    return Equal(C & A, A.etype.emptySet)


@prove
def prove(Eq):
    from Lemma import Set
    A, B, C = Symbol(etype=dtype.integer)

    Eq << apply(Equal(B & C, C.etype.emptySet, evaluate=False), Subset(A, B, evaluate=False))

    Eq << Set.SubsetInterS.of.Subset.apply(Eq[1], C)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Supset(*Eq[-1].args, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

# created on 2021-05-14
