from util import *


@apply
def apply(given, step=-1):
    lhs, rhs = given.of(Less)
    assert lhs.is_extended_integer and rhs.is_extended_integer
    if step > 0:
        lhs += 1
    else:
        rhs -= 1
    return LessEqual(lhs, rhs)


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    Eq << apply(x < y)

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]




if __name__ == '__main__':
    run()
# created on 2018-05-05
# updated on 2023-11-05

from . import plus
