from util import *


@apply
def apply(given, divisor=None):
    lhs, rhs = given.of(Equal)
    # assert divisor.is_nonzero
    return Equal(lhs / divisor, rhs / divisor)


@prove
def prove(Eq):
    x, y, d = Symbol(real=True)
    Eq << apply(Equal(x, y), d)

    Eq << Eq[-1] * d


if __name__ == '__main__':
    run()
# created on 2018-08-21
