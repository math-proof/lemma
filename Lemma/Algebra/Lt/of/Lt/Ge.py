from util import *


@apply
def apply(a_less_than_x, b_greater_than_x):
    a, x = a_less_than_x.of(Less)
    b, _x = b_greater_than_x.of(GreaterEqual)
    if x != _x:
        x, a, S[x], b = b, _x, a, x
    return Less(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a, b = Symbol(real=True)
    Eq << apply(a < x, b >= x)

    Eq << Eq[1].reversed

    Eq << Algebra.Lt.of.Lt.Le.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-11-04

