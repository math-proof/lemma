from util import *


@apply
def apply(given):
    A, B = given.of(Subset)

    return Equal(A & B, A)


@prove
def prove(Eq):
    from Lemma import Set

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, B))

    Eq << Set.SubsetInterS.of.Subset.apply(Eq[0], A)

    Eq << Supset(*Eq[-1].args, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2018-09-14
