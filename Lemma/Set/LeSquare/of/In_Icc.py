from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    m, M = interval.of(Interval)
    assert not interval.left_open
    assert not interval.right_open

    return LessEqual(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, m, M = Symbol(real=True)
    Eq << apply(Element(x, Interval(m, M)))

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq << Algebra.LeSquare.of.Le.Ge.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-03-26
