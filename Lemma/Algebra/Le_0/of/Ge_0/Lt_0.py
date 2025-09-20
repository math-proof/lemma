from util import *


@apply
def apply(is_positive_x, is_negative_y):
    x = is_positive_x.of(Expr >= 0)
    y = is_negative_y.of(Expr < 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(real=True)

    Eq << apply(x >= 0, y < 0)

    Eq << Algebra.Le_0.of.Lt_0.Ge_0.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-07-03
