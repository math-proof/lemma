from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)

    return 1 / x > 0


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(real=True)

    Eq << apply(x + y > 0)

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-08-09
