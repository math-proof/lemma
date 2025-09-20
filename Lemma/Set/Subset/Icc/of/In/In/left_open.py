from util import *


@apply
def apply(contains1, contains2):
    x, A = contains1.of(Element)
    y, S[A] = contains2.of(Element)
    a, b = A.of(Interval)
    return Subset(Interval(x, y, left_open=True), Interval(a, b, right_open=A.right_open, left_open=True))


@prove
def prove(Eq):
    from Lemma import Set

    a, b, x, y = Symbol(real=True, given=True)
    S = Interval(a, b, right_open=True)
    Eq << apply(Element(x, S), Element(y, S))

    Eq << Set.Subset.Icc.of.In.In.apply(Eq[0], Eq[1])

    Eq << Set.Subset.SDiff.of.Subset.apply(Eq[-1], {x})

    Eq << Set.EqSDiff.of.In.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.subset = Set.Subset.SDiff.of.Subset.apply(Eq[-1], Eq[-1].rhs.args[1])

    Eq << Set.Le.of.In_Icc.apply(Eq[0])

    Eq << Set.Subset.Icc.Infty.of.Le.apply(Eq[-1], left_open=True)

    Eq << Set.SubsetInterS.of.Subset.apply(Eq[-1], Interval.open(-oo, b))

    Eq << Set.Subset.of.Subset.Subset.apply(Eq.subset, Eq[-1])




if __name__ == '__main__':
    run()
# created on 2021-02-27
# updated on 2023-05-04
