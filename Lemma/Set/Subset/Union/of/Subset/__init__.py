from util import *


@apply
def apply(given, S):
    lhs, rhs = given.of(subset.Subset)
    return subset.Subset(lhs | S, rhs | S)

@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(integer=True, positive=True)
    A, B, S = Symbol(etype=dtype.complex[n])

    Eq << apply(subset.Subset(A, B), S)

    Eq << Set.Subset.Union.of.Subset.rhs.apply(Eq[0], S)

    Eq << subset.Subset(S, B | S, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]

if __name__ == '__main__':
    run()


# created on 2020-07-19

del Subset
from . import Subset
from . import rhs
