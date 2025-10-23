from util import *


@apply
def apply(is_nonpositive_x, is_negative_y):
    x = is_nonpositive_x.of(Expr <= 0)
    y = is_negative_y.of(Expr < 0)
    return GreaterEqual(x * y, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Int
    x, y = Symbol(real=True)

    Eq << apply(x <= 0, y < 0)

    Eq << Int.Ge_0.of.Lt_0.Le_0.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-12-10
