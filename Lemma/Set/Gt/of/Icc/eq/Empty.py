from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Interval)
    assert not A.left_open and not A.right_open
    return Greater(a, b)


@prove
def prove(Eq):
    from Lemma import Set

    a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(Interval(a, b), a.emptySet))

    Eq << ~Eq[1]

    Eq << Set.Subset.Icc.of.Le.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[0])

    Eq << Set.Eq_Empty.of.Subset.apply(Eq[-1])

    Eq << Set.EqUnionS.of.Eq.Eq.apply(Eq[0], Eq[-1])
    Eq << Eq[-1].this.lhs.apply(Set.Union.eq.Icc)



if __name__ == '__main__':
    run()
# created on 2021-05-05
