from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    return Equal(A - B, A.etype.emptySet)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Subset(A, B))

    Eq << ~Eq[-1]

    Eq << Set.Any_In.of.Ne_Empty.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.expr.apply(Set.In.NotIn.of.In_SDiff, simplify=None)

    Eq << Set.Any.of.Any_And.single_variable.limits_absorb.apply(Eq[-1], index=0, simplify=None)

    Eq << Set.Any.of.Any.limits.swap.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Set.In.of.In.Subset, Eq[0])

    Eq << Bool.Any_And.of.AnySetOf.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-05-04
