from util import *


@apply
def apply(given, x):
    lhs, rhs = given.of(Equal)
    fx = lhs - rhs
    assert fx._has(x)
    if x.is_Symbol:
        x_ = x
    else:
        x, x_ = Dummy('x', **x.type.dict), x
        fx = fx._subs(x_, x)

    p = fx.as_poly(x)
    assert p.degree() == 1
    a = p.nth(1)
    assert a.is_nonzero

    b = p.nth(0)
    return Equal(x_, -b / a)

@prove
def prove(Eq):
    x, a, b, d = Symbol(real=True)
    c = Symbol(real=True, positive=True)

    Eq << apply(Equal(a * x + b, (a + c) * x + d), x=x)

    Eq << Eq[-1] * c

    Eq << Eq[-1].reversed + d

    Eq << Eq[0].this.rhs.expand()


if __name__ == '__main__':
    run()
# created on 2020-06-29
