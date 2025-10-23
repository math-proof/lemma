from util import *


@apply
def apply(lt, le):
    a, b = lt.of(Less)
    x, y = le.of(LessEqual)
    z = b - a
    return LessEqual(z * x,  z * y)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    a, b, x, y = Symbol(real=True)
    Eq << apply(a < b, x <= y)

    Eq << Algebra.Gt_0.of.Lt.apply(Eq[0])

    Eq << Nat.LeMul.of.Gt_0.Le.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-01-05
