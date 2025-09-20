from util import *

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply
def apply(a):
    U = a.universalSet
    return Unequal(U - a.set, a.emptySet)


@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(complex=True, shape=(n,), given=True)

    Eq << apply(x)

    Eq << ~Eq[-1]

    Eq << Set.Subset.SDiff.of.Eq_Empty.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-04-24
