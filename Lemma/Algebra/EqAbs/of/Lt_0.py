from util import *


@apply
def apply(given):
    x = given.of(Expr < 0)
    return Equal(abs(x), -x)


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True)

    Eq << apply(x < 0)

    Eq << -Eq[0]

    Eq << Algebra.EqAbs.of.Gt_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-07-23
