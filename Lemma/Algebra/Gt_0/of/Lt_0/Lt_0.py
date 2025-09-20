from util import *


@apply
def apply(is_negative_x, is_negative_y):
    x = is_negative_x.of(Expr < 0)
    y = is_negative_y.of(Expr < 0)
    return Greater(x * y, 0)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(real=True)

    Eq << apply(x < 0, y < 0)

    Eq << Algebra.Gt_0.of.Gt_0.Gt_0.apply(-Eq[0], -Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-02-05
