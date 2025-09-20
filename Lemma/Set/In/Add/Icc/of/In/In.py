from util import *


@apply
def apply(contains1, contains2):
    x0, S0 = contains1.of(Element)
    x1, S1 = contains2.of(Element)

    assert S0.is_Interval and S1.is_Interval
    assert S0.left_open == S1.left_open
    assert S0.right_open == S1.right_open

    return Element(x0 + x1, S0 + S1)


@prove
def prove(Eq):
    from Lemma import Set

    x0, x1, a, b, c, d = Symbol(real=True)
    Eq << apply(Element(x0, Interval(a, b, left_open=True)), Element(x1, Interval(c, d, left_open=True)))

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[1])

    Eq <<= Eq[-2] + Eq[-4], Eq[-1] + Eq[-3]

    Eq << Set.In.Icc.of.Gt.Le.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-05-15
