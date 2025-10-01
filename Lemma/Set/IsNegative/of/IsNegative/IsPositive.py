from util import *


@apply
def apply(b_is_negative, a_is_positive):
    a, R = a_is_positive.of(Element)
    RR = Interval.open(0, oo)
    assert R in RR
    b, R = b_is_negative.of(Element)
    RR = Interval.open(-oo, 0)
    assert R in RR
    return Element(a * b, RR)


@prove
def prove(Eq):
    from Lemma import Set

    x, y = Symbol(hyper_real=True)
    Eq << apply(Element(y, Interval.open(-oo, 0)), Element(x, Interval.open(0, oo)))

    Eq << Set.Neg.In.Icc.of.In_Icc.apply(Eq[0])

    Eq << Set.IsPositive.of.IsPositive.IsPositive.apply(Eq[-1], Eq[1])

    Eq << Set.Neg.In.Icc.of.In_Icc.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-04-03
