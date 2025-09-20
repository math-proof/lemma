from util import *


@apply
def apply(contains1, contains2):
    x, A = contains1.of(Element)
    y, S[A] = contains2.of(Element)
    a, b = A.of(Interval)
    return Subset(Interval(x, y, right_open=True), Interval(a, b, left_open=A.left_open, right_open=True))


@prove
def prove(Eq):
    from Lemma import Set

    a, b, x, y = Symbol(real=True, given=True)
    S = Interval(a, b, left_open=True)
    Eq << apply(Element(x, S), Element(y, S))

    Eq << Set.Subset.Icc.of.In.In.apply(Eq[0], Eq[1])

    Eq << Set.Subset.SDiff.of.Subset.apply(Eq[-1], {y})

    Eq << Set.EqSDiff.of.In.apply(Eq[1])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.subset = Set.Subset.SDiff.of.Subset.apply(Eq[-1], Eq[-1].rhs.args[1])

    Eq << Set.Le.of.In_Icc.apply(Eq[1])

    Eq << Set.Subset.Icc.NegInfty.of.Le.apply(Eq[-1], right_open=True)

    Eq << Set.SubsetInterS.of.Subset.apply(Eq[-1], Interval.open(a, oo))
    Eq << Set.Subset.of.Subset.Subset.apply(Eq.subset, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-11-23
