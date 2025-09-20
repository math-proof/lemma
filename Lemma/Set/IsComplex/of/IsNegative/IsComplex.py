from util import *


@apply
def apply(is_negative, is_complex):
    a, R = is_negative.of(Element)
    assert R in Interval.open(-oo, 0)
    b, R = is_complex.of(Element)
    assert R in S.Complexes
    return Element(b / a, S.Complexes)


@prove
def prove(Eq):
    from Lemma import Set

    x, y = Symbol(super_complex=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)), Element(y, S.Complexes))

    Eq << Set.Neg.In.IccNegS.of.In_Icc.apply(Eq[0])

    Eq << Set.IsComplex.of.IsPositive.IsComplex.apply(Eq[-1], Eq[1])

    Eq << Set.Neg.In.IccNegS.of.In_Icc.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-03
