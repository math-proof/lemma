from util import *


@apply
def apply(eq0, eq1, wrt=None):
    lhs, rhs = eq0.of(Equal)
    f = lhs - rhs
    f = f.as_poly(wrt)
    assert f.degree() == 1
    # f = a * x + b
    a, b = f.nth(1), f.nth(0)
    assert a.is_zero == False
    f = -b / a

    lhs, rhs = eq1.of(Equal)
    g = lhs - rhs

    g = g.as_poly(wrt)
    a, b = g.nth(1), g.nth(0)
    assert a.is_zero == False
    g = -b / a

    return Equal(g, f)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, a, b = Symbol(complex=True)
    c, d = Symbol(complex=True, zero=False)
    Eq << apply(Equal(a, c * x), Equal(b, d * x), wrt=x)

    Eq <<= Eq[0] / c, Eq[1] / d

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-03-23
