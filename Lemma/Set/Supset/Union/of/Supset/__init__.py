from util import *



@apply
def apply(given, S):
    lhs, rhs = given.of(subset.Supset)
    return subset.Supset(lhs | S, rhs | S)

@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(integer=True, positive=True)
    A, B, S = Symbol(etype=dtype.complex[n])

    Eq << apply(subset.Supset(A, B), S)

    Eq << Eq[0].reversed

    Eq << Set.Subset.Union.of.Subset.apply(Eq[-1], S)

    Eq << Eq[-1].reversed

if __name__ == '__main__':
    run()


# created on 2021-07-05

del Supset
from . import Supset
