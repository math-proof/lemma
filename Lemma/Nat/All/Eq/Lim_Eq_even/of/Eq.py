from util import *


@apply
def apply(given, wrt):
    assert wrt.is_symbol
    lhs, rhs = given.of(Equal)
    x = given.generate_var(excludes=wrt, **wrt.dtype.dict)
    lhs = lhs._subs(2 * wrt, x)
    assert not lhs._has(wrt)
    rhs = rhs._subs(2 * wrt, x)
    assert not rhs._has(wrt)

    lhs = lhs._subs(x, wrt)
    rhs = rhs._subs(x, wrt)

    return All[wrt:Equal(wrt % 2, 0)](Equal(lhs, rhs))


@prove
def prove(Eq):
    n = Symbol(integer=True)

    f, g = Symbol(shape=(oo,), real=True)

    Eq << apply(Equal(f[2 * n], g[2 * n]), wrt=n)

    Eq << Eq[1].limits_subs(n, 2 * n)

if __name__ == '__main__':
    run()
# created on 2019-03-28
