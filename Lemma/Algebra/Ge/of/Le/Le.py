from util import *


@apply
def apply(a_less_than_x, x_less_than_b):
    a, x = a_less_than_x.of(LessEqual)
    S[x], b = x_less_than_b.of(LessEqual)
    return GreaterEqual(b, a)


@prove
def prove(Eq):
    from Lemma import Algebra
    a, x, b = Symbol(real=True)

    Eq << apply(a <= x, x <= b)

    Eq << Algebra.Le.of.Le.Le.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-11-19

