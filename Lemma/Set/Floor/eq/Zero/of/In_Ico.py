from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain in Interval(0, 1, right_open=True)
    return Equal(Floor(x), 0)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, 1, right_open=True)))

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])
    Eq << Algebra.Floor.eq.Zero.of.Ge_0.Lt.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-10-21
