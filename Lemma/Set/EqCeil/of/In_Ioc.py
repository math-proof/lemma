from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain.left_open
    a, b = domain.of(Interval)
    assert b == a + 1
    return Equal(Ceil(x), b)


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(real=True)
    a = Symbol(integer=True)
    Eq << apply(Element(x, Interval(a, a + 1, left_open=True)))

    Eq << Set.InSub.of.In_Icc.apply(Eq[0], a + 1)

    Eq << Set.Ceil.eq.Zero.of.In_Ioc.apply(Eq[-1])
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-10-23
