from util import *


@apply
def apply(is_negative, le):
    x, R = is_negative.of(Element)
    assert R in Interval.open(-oo, 0)

    lhs, rhs = le.of(LessEqual)

    return GreaterEqual(lhs * x, rhs * x)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(real=True, given=True)
    g, h = Function(real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)), LessEqual(g(x), h(x)))

    Eq << Set.Lt_0.of.IsNegative.apply(Eq[0])

    Eq << Algebra.GeMul.of.Lt_0.Le.apply(Eq[-1], Eq[1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2023-10-15
