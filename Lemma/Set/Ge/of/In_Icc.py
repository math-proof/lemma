from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    a, b = interval.of(Interval)

    if interval.left_open:
        if interval.right_open:
            ...
        else:
            return GreaterEqual(b, x)
    else:
        return GreaterEqual(x, a)


@prove
def prove(Eq):
    from Lemma import Set
    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq << Subset(Eq[0].rhs, Interval(a, oo, right_open=True), plausible=True)

    Eq << Set.In.of.In.Subset.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-04-05
