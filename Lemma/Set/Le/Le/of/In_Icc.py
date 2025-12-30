from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    a, b = interval.of(Interval)
    if interval.left_open:
        if interval.right_open:
            return x > a, x < b
        else:
            return x > a, x <= b
    else:
        if interval.right_open:
            return x >= a, x < b
        else:
            return x >= a, x <= b


@prove
def prove(Eq):
    from Lemma import Set

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(a, b)))



    Eq << Set.Le.of.In_Icc.apply(Eq[0])

    Eq << Set.Ge.of.In_Icc.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-04-05
