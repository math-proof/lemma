from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d > 0

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

    Eq << Set.In.Mul.Icc.of.In.apply(Eq[1], 1 / d)


if __name__ == '__main__':
    run()
# created on 2019-06-25
