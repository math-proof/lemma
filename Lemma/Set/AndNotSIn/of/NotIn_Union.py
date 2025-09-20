from util import *


@apply
def apply(given, index=-1):
    e, args = given.of(NotElement[Union])

    first = Union(*args[:index])
    second = Union(*args[index:])
    return NotElement(e, first), NotElement(e, second)


@prove
def prove(Eq):
    x = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(NotElement(x, A | B))

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

# created on 2018-01-10
