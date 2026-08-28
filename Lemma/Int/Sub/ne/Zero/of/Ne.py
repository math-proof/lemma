from util import *


@apply(simplify=None)
def apply(ne):
    lhs, rhs = ne.of(Unequal)
    return Unequal(lhs - rhs, 0)


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    Eq << apply(Unequal(x, y))

    Eq << Eq[0] - y


if __name__ == '__main__':
    run()
# created on 2018-11-12
