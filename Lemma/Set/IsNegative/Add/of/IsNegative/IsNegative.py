from util import *


@apply
def apply(a_is_negative, b_is_negative):
    a, R = a_is_negative.of(Element)
    negative_R = Interval.open(-oo, 0)
    assert R in negative_R
    b, R = b_is_negative.of(Element)
    assert R in negative_R
    return Element(a + b, negative_R)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)), Element(y, Interval.open(-oo, 0)))

    Eq << Set.Lt.of.In_Icc.apply(Eq[0])

    Eq << Set.Lt.of.In_Icc.apply(Eq[1])

    Eq << Algebra.LtAdd.of.Lt.Lt.apply(Eq[-1], Eq[-2])
    Eq << Set.IsReal.Add.of.IsReal.IsReal.apply(Eq[0], Eq[1])
    Eq << Set.IsNegative.of.Lt_0.IsComplex.apply(Eq[-2], Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-05-03
