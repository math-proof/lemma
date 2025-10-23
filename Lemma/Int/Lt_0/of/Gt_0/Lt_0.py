from util import *


@apply
def apply(is_positive_x, is_negative_y):
    x = is_positive_x.of(Expr > 0)
    y = is_negative_y.of(Expr < 0)
    return Less(x * y, 0)


@prove
def prove(Eq):
    x, y = Symbol(real=True)

    Eq << apply(x > 0, y < 0)

    Eq << -Eq[1] * Eq[0]

    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-02-07
