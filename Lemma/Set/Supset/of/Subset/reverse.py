from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    return Supset(B, A)


@prove
def prove(Eq):
    from Lemma import Set

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, B))

    Eq << Set.Supset.given.All_In.apply(Eq[1])

    Eq << Set.All_In.of.Subset.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-06-28
