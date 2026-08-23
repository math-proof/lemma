from util import *


@apply
def apply(given, factor=None):
    lhs, rhs = given.of(Equal)
    assert factor.is_nonzero
    return Equal(lhs * factor, rhs * factor)


@prove
def prove(Eq):
    x, y = Symbol(real=True)
    c = Symbol(real=True, zero=False)
    Eq << apply(Equal(x, y), c)

    Eq << Eq[-1] / c

    


if __name__ == '__main__':
    run()
# created on 2023-11-06
