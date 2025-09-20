from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)

    return Greater(x * x, 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    Eq << apply(x > 0)
    Eq << Algebra.Gt_0.of.Gt_0.Gt_0.apply(Eq[0], Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-06-05
