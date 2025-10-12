from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    return Greater(Card(A), 0)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Nat
    A = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << Set.Ne_0.of.Ne_Empty.apply(Eq[0])

    Eq << Nat.Gt_0.of.Ne_0.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-12
