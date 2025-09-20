from util import *


@apply
def apply(b_greater_than_x, a_less_than_x):
    b, x = b_greater_than_x.of(GreaterEqual)
    a, _x = a_less_than_x.of(LessEqual)
    if x != _x:
        b, x, a, S[x] = _x, a, x, b
    return LessEqual(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra
    a, x, b = Symbol(real=True)

    Eq << apply(b >= x, a <= x)

    Eq << Eq[1].reversed

    Eq << Algebra.Ge.of.Ge.Ge.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-05-06

