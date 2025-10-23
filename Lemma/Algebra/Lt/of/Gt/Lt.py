from util import *


@apply
def apply(b_greater_than_x, a_less_than_x):
    b, x = b_greater_than_x.of(GreaterEqual)
    a, S[x] = a_less_than_x.of(Less)
    return Less(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    a, x, b = Symbol(real=True)

    Eq << apply(b >= x, a < x)

    Eq << Eq[1].reversed

    Eq << Nat.Gt.of.Ge.Gt.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-08-02

