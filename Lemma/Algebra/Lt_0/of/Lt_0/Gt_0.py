from util import *


@apply
def apply(is_negative_y, is_positive_x):
    x = is_positive_x.of(Expr > 0)
    y = is_negative_y.of(Expr < 0)
    return Less(x * y, 0)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(real=True)

    Eq << apply(y < 0, x > 0)

    Eq << -Eq[0]

    Eq << Algebra.Gt_0.of.Gt_0.Gt_0.apply(Eq[-1], Eq[1])

    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-12-14
