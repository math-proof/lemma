from util import *


@apply
def apply(gt_zero, given):
    n = gt_zero.of(Expr < 0)
    x = given.of(Expr > 0)
    return Greater(x ** n, 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(n < 0, x > 0)

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[1])

    Eq << Algebra.Gt_0.Pow.of.Gt_0.Gt_0.apply(-Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-15
