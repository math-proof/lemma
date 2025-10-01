from util import *


@apply
def apply(contains1, contains2):
    x0, S0 = contains1.of(Element)
    x1, S1 = contains2.of(Element)

    assert S0.is_Interval and S1.is_Interval
    assert S0.left_open == S1.right_open
    assert S0.right_open == S1.left_open

    return Element(x0 - x1, S0 + -S1)


@prove
def prove(Eq):
    from Lemma import Set

    x0, x1, a, b, c, d = Symbol(real=True)
    Eq << apply(Element(x0, Interval(a, b, left_open=True)), Element(x1, Interval(c, d, right_open=True)))

    Eq << Set.Neg.In.Icc.of.In_Icc.apply(Eq[1])
    Eq << Set.Add.In.Ioc.of.In.In.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-05-15
