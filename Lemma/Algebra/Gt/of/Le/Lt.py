from util import *


@apply
def apply(le, lt):
    a, x = le.of(LessEqual)
    _x, b = lt.of(Less)
    if x != _x:
        a, x, S[x], b = _x, a, b, x
    return Greater(b, a)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, a, b = Symbol(real=True)
    Eq << apply(x <= a, b < x)

    Eq << Nat.Lt.of.Le.Lt.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-11-23

