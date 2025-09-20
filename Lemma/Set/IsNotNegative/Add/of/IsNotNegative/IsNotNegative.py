from util import *


@apply
def apply(a_is_nonnegative, b_is_nonnegative):
    a, R = a_is_nonnegative.of(Element)
    nonnegative_R = Interval(0, oo)
    assert R in nonnegative_R
    b, R = b_is_nonnegative.of(Element)
    assert R in nonnegative_R
    return Element(a + b, nonnegative_R)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval(0, oo)), Element(y, Interval(0, oo)))

    Eq << Set.Ge.of.In_Icc.apply(Eq[0])

    Eq << Set.Ge.of.In_Icc.apply(Eq[1])

    Eq << Algebra.GeAdd.of.Ge.Ge.apply(Eq[-1], Eq[-2])

    Eq << Set.IsReal.Add.of.IsReal.IsReal.apply(Eq[0], Eq[1])

    Eq << Set.IsNotNegative.of.Ge_0.IsComplex.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-03
