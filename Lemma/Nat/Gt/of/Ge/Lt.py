from util import *


@apply
def apply(b_greater_than_x, a_less_than_x):
    b, x = b_greater_than_x.of(GreaterEqual)
    a, _x = a_less_than_x.of(Less)
    if x != _x:
        x, b, S[x], a = a, _x, b, x

    return Greater(b, a)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat, Nat

    a, x, b = Symbol(real=True)
    Eq << apply(b >= x, a < x)

    Eq << Eq[1].reversed

    Eq << Nat.Gt.of.Ge.Gt.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-09-03

