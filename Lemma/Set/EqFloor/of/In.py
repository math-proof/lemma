from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain.right_open
    a, b = domain.of(Interval)
    assert b == a + 1
    return Equal(Floor(x), a)


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(real=True)
    a = Symbol(integer=True)
    Eq << apply(Element(x, Interval(a, a + 1, right_open=True)))

    Eq << Set.InSub.of.In_Icc.apply(Eq[0], a)

    Eq << Set.Floor.eq.Zero.of.In_Ico.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-12-05
