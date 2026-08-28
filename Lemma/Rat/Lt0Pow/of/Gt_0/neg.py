from util import *


@apply
def apply(gt_zero, given):
    n = gt_zero.of(Expr < 0)
    x = given.of(Expr > 0)
    return Greater(x ** n, 0)


@prove
def prove(Eq):
    from Lemma import Rat

    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(n < 0, x > 0)

    Eq << Rat.Lt0Div.of.Gt_0.apply(Eq[1])

    Eq << Rat.Lt0Pow.of.Gt_0.pos.apply(-Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-15
