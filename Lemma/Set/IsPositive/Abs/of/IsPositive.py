from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    a, b = RR.of(Interval)
    if RR.left_open:
        assert a >= 0
    else:
        assert a > 0
    return Element(abs(x), RR)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(super_complex=True)
    Eq << apply(Element(x, Interval.open(0, oo)))

    Eq << Set.Gt_0.of.IsPositive.apply(Eq[0])

    Eq << Algebra.EqAbs.of.Gt_0.apply(Eq[-1])

    Eq << Eq[1].subs(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2020-04-15
# updated on 2023-05-03
