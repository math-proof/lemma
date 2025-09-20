from util import *


@apply
def apply(given):
    A, B = given.of(Supset)
    return GreaterEqual(Card(A), Card(B))


@prove
def prove(Eq):
    from Lemma import Set

    A = Symbol(etype=dtype.integer, finiteset=True)
    B = Symbol(etype=dtype.integer)
    Eq << apply(Supset(A, B))

    Eq << Eq[0].reversed

    Eq << Set.Le.of.Subset.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-07-03
