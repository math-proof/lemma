from util import *


@apply
def apply(is_real, is_positive):
    a, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)
    b, R = is_real.of(Element)
    assert R in Reals
    return Element(b / a, Reals)


@prove
def prove(Eq):
    from Lemma import Set

    x, y = Symbol(super_real=True)
    Eq << apply(Element(y, Interval(-oo, oo)), Element(x, Interval.open(0, oo)))

    Eq << Set.IsReal.of.IsPositive.IsReal.apply(Eq[1], Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-05-03
