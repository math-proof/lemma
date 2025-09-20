from util import *


@apply
def apply(a_less_than_x, b_greater_than_x):
    a, x = a_less_than_x.of(Less)
    b, _x = b_greater_than_x.of(GreaterEqual)
    if x != _x:
        b, x, a, S[x] = x, a, _x, b
    return Greater(b, a)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, x, b = Symbol(real=True)
    Eq << apply(a < x, b >= x)

    Eq << Eq[1].reversed

    Eq << Algebra.Lt.of.Lt.Le.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2018-10-18
# updated on 2023-04-28

