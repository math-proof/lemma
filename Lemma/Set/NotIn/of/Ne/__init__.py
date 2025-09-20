from util import *
# given: x != y
# x not in {y}


@apply(simplify=None)
def apply(given):
    x, y = given.of(Unequal)
    return NotElement(x, y.set)


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    Eq << apply(Unequal(x, y))

    Eq << ~Eq[-1]

    Eq << Eq[-1].simplify()

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2018-03-08

del Ne
from . import Ne
from . import NotIn
