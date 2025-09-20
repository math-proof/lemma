from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    return Supset(B, A)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, B))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])
    Eq << Eq[-2].this.lhs.apply(Set.Supset.of.Subset.reverse)
    Eq << Eq[-1].this.rhs.apply(Set.Subset.given.Supset.reverse)


if __name__ == '__main__':
    run()
# created on 2021-06-30
