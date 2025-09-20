from util import *


@apply
def apply(given, index=0):
    union, rhs = given.of(Subset)
    union = union.of(Union)

    return Subset(union[index], rhs)


@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(integer=True, positive=True)
    A, B, S = Symbol(etype=dtype.complex[n])

    Eq << apply(Subset(A | B, S))

    Eq << Subset(A, A | B, plausible=True)

    Eq << Set.Subset.of.Subset.Subset.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-07-28
