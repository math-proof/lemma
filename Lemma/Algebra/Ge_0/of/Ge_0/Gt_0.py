from util import *


@apply
def apply(is_nonnegative_x, is_positive_y):
    x = is_nonnegative_x.of(Expr >= 0)
    y = is_positive_y.of(Expr > 0)
    return GreaterEqual(x * y, 0)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(real=True)

    Eq << apply(x >= 0, y > 0)

    Eq << Algebra.Ge_0.of.Gt_0.Ge_0.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-07-18
