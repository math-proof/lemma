from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    assert B.is_finiteset
    return LessEqual(Card(A), Card(B))


@prove
def prove(Eq):
    from Lemma import Set

    A = Symbol(etype=dtype.integer, given=True)
    B = Symbol(etype=dtype.integer, given=True, finiteset=True)
    Eq << apply(Subset(A, B))

    Eq << Set.EqSDiff.of.Subset.apply(Eq[0])

    Eq << ~Eq[1]

    Eq << Eq[-1] + Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2021-06-27
