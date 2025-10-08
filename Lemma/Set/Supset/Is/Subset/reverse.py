from util import *


@apply
def apply(given):
    A, B = given.of(Supset)
    return Subset(B, A)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Supset(A, B))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.Subset.of.Supset.reverse)
    Eq << Eq[-1].this.rhs.apply(Set.Supset.given.Subset.reverse)


if __name__ == '__main__':
    run()
# created on 2021-07-09
