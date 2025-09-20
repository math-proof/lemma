from util import *


@apply
def apply(a_is_nonpositive, b_is_nonpositive):
    a, R = a_is_nonpositive.of(Element)
    nonpositive_R = Interval(-oo, 0)
    assert R in nonpositive_R
    b, R = b_is_nonpositive.of(Element)
    assert R in nonpositive_R
    return Element(a + b, nonpositive_R)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval(-oo, 0)), Element(y, Interval(-oo, 0)))

    Eq << Set.Le.of.In_Icc.apply(Eq[0])

    Eq << Set.Le.of.In_Icc.apply(Eq[1])

    Eq << Algebra.LeAdd.of.Le.Le.apply(Eq[-1], Eq[-2])

    Eq << Set.IsReal.Add.of.IsReal.IsReal.apply(Eq[0], Eq[1])

    Eq << Set.IsNotPositive.of.Le_0.IsComplex.apply(Eq[-2], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-03
