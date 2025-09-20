from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    m, S[0] = interval.of(Interval)
    assert not interval.left_open
    assert not interval.right_open
    return LessEqual(x * x, m * m)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, m = Symbol(real=True)
    Eq << apply(Element(x, Interval(m, 0)))

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq << Algebra.LeSquare.of.Le_0.Ge.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

# created on 2021-03-11
