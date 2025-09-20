from util import *


@apply(simplify=None)
def apply(given):
    lhs, rhs = given.of(Greater)
    return lhs >= rhs, Unequal(lhs, rhs)


@prove
def prove(Eq):
    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Greater(x, y))

    Eq <<= Eq[1] & Eq[2]




if __name__ == '__main__':
    run()
# created on 2023-11-12



from . import scale
from . import strengthen
