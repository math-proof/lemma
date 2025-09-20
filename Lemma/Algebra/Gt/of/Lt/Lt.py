from util import *


@apply
def apply(a_less_than_x, x_less_than_b):
    a, x = a_less_than_x.of(Less)
    S[x], b = x_less_than_b.of(Less)
    return Greater(b, a)


@prove
def prove(Eq):
    from Lemma import Algebra
    a, x, b = Symbol(real=True)

    Eq << apply(a < x, x < b)

    Eq << Algebra.Lt.of.Lt.Lt.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2020-01-06

