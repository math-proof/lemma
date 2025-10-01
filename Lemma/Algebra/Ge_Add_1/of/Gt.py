from util import *


@apply
def apply(given, step=1):
    lhs, rhs = given.of(Greater)

    assert lhs.is_extended_integer and rhs.is_extended_integer
    if step > 0:
        rhs += 1
    else:
        lhs -= 1

    return GreaterEqual(lhs, rhs)


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    Eq << apply(x > y)

    Eq << ~Eq[-1]

    Eq <<= Eq[0] & Eq[-1]




if __name__ == '__main__':
    run()
# created on 2018-05-12
# updated on 2023-11-05
