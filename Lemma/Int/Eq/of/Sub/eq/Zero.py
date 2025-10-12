from util import *


@apply
def apply(given, reverse=False):
    (x, y), zero = given.of(Equal[Expr - Expr])
    assert not zero
    if reverse:
        x, y = y, x

    return Equal(x, y)


@prove
def prove(Eq):
    a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(0, a - b))

    Eq << Eq[0] + b

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2018-01-28
# updated on 2022-01-01

