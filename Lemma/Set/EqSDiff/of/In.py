from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    a, b = interval.of(Interval)
    return Equal(interval - {x}, Interval(a, x, left_open=interval.left_open, right_open=True) | Interval(x, b, left_open=True, right_open=interval.right_open))


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)))

    Eq << Set.EqIcc.of.In.split.apply(Eq[0])
    Eq << Set.EqSDiff.of.Eq.apply(Eq[-1], {x})


if __name__ == '__main__':
    run()
# created on 2020-11-22
