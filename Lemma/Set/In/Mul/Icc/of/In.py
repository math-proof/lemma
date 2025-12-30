from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive

    e, interval = given.of(Element)

    a, b = interval.of(Interval)

    e *= d

    return Element(e, interval.copy(start=a * d, stop=b * d))


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b = Symbol(real=True)
    d = Symbol(real=True, positive=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)), d)

    Eq << Set.Le.Le.of.In_Icc.apply(Eq[0])

    Eq <<= Eq[-2] * d, Eq[-1] * d

    Eq << Set.In.Icc.of.Ge.Lt.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-11-21
