from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])

    return GreaterEqual(Card(A), 1)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    A = Symbol(etype=dtype.integer)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << Set.Gt_0.of.Ne_Empty.apply(Eq[0])

    Eq << ~Eq[1]

    Eq << GreaterEqual(Card(A), 0, plausible=True)

    Eq << Bool.Any_And.of.Any.All.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.apply(Set.In.Ico.of.Lt.Ge)


    Eq << Algebra.Any.of.Any_Eq.Cond.subst.apply(Eq[-1], Eq[2])




if __name__ == '__main__':
    run()

# created on 2020-07-12
# updated on 2023-05-26
