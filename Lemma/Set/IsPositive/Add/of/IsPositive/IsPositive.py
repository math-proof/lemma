from util import *


@apply
def apply(a_is_positive, b_is_positive):
    a, R = a_is_positive.of(Element)
    positive_R = Interval.open(0, oo)
    assert R in positive_R
    b, R = b_is_positive.of(Element)
    assert R in positive_R
    return Element(a + b, positive_R)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval.open(0, oo)), Element(y, Interval.open(0, oo)))

    Eq << Set.Gt.of.In_Icc.apply(Eq[0])

    Eq << Set.Gt.of.In_Icc.apply(Eq[1])

    Eq << Algebra.GtAdd.of.Gt.Gt.apply(Eq[-1], Eq[-2])

    Eq << Set.IsReal.Add.of.IsReal.IsReal.apply(Eq[0], Eq[1])

    Eq << Set.IsPositive.of.Gt_0.IsComplex.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-03
