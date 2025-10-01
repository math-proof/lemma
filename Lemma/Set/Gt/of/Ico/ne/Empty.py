from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return Greater(b, a)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << Set.Any_In.of.Ne_Empty.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(Set.Ge.Le_Sub_1.of.In_Ico)

    Eq << Eq[-1].this.expr.apply(Algebra.Gt.of.Ge.Lt)


if __name__ == '__main__':
    run()
# created on 2018-10-18
