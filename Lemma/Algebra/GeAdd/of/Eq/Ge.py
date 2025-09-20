from util import *


@apply
def apply(eq, x_less_than_b):
    if not eq.is_Equal:
        eq, x_less_than_b = x_less_than_b, eq

    a, x = eq.of(Equal)
    b, y = x_less_than_b.of(GreaterEqual)

    return GreaterEqual(a + b, x + y)


@prove
def prove(Eq):
    a, x, b, y = Symbol(real=True)
    Eq << apply(Equal(a, x), y >= b)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] - x


if __name__ == '__main__':
    run()
# created on 2018-09-01
