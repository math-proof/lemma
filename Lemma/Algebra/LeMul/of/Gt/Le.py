from util import *


@apply
def apply(gt, le):
    a, b = gt.of(Greater)
    x, y = le.of(LessEqual)
    z = a - b
    return LessEqual(z * x,  z * y)


@prove
def prove(Eq):
    from Lemma import Algebra
    a, b, x, y = Symbol(real=True)
    Eq << apply(a > b, x <= y)

    Eq << Algebra.Gt_0.of.Gt.apply(Eq[0])

    Eq << Algebra.LeMul.of.Gt_0.Le.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-08-01
