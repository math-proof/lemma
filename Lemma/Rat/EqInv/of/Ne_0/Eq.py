from util import *


@apply
def apply(is_nonzero, eq):
    if is_nonzero.is_Equal:
        eq, is_nonzero = is_nonzero, eq

    den = is_nonzero.of(Unequal[0])

    lhs, rhs = eq.of(Equal)
    assert den == lhs or den == rhs
    return Equal(1 / lhs, 1 / rhs)


@prove
def prove(Eq):
    x = Symbol(real=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(Unequal(f(x), 0), Equal(f(x), g(x)))

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].subs(Eq[1].reversed)


if __name__ == '__main__':
    run()

# created on 2020-06-18
