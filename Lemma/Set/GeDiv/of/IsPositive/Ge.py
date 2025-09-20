from util import *


@apply
def apply(is_positive, ge):
    x, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)

    lhs, rhs = ge.of(GreaterEqual)

    return GreaterEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(real=True, given=True)
    g, h = Function(real=True)
    Eq << apply(Element(x, Interval.open(0, oo)), GreaterEqual(g(x), h(x)))

    Eq << Set.Gt_0.of.IsPositive.apply(Eq[0])

    Eq << Algebra.GeDiv.of.Gt_0.Ge.apply(Eq[-1], Eq[1], simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-10-15
