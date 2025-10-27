from util import *


@apply
def apply(a_less_than_x, b_greater_than_x):
    a, x = a_less_than_x.of(Less)
    b, _x = b_greater_than_x.of(Greater)
    if x != _x:
        x, a, S[x], b = b, _x, a, x
    return Less(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    a, x, b = Symbol(real=True)

    Eq << apply(a < x, b > x)

    Eq << Eq[1].reversed

    Eq << Nat.Lt.of.Lt.Lt.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-12-20

from . import quadratic
