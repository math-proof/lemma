from util import *


@apply
def apply(ge, lt):
    b, x = ge.of(GreaterEqual)
    a, _x = lt.of(Less)
    if x != _x:
        x, b, S[x], a = a, _x, b, x

    return GreaterEqual(b, a)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    a, x, b = Symbol(real=True)
    Eq << apply(b >= x, a < x)

    Eq << Algebra.Gt.of.Ge.Lt.apply(Eq[0], Eq[1])
    Eq << Nat.Ge.of.Gt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-09-03
