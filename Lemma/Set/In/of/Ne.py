from util import *
# given: x != y
# x not in {y}


@apply
def apply(given):
    x, y = given.of(Unequal)
    return Element(x, y.universalSet - {y})


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    Eq << apply(Unequal(x, y))

    Eq << ~Eq[-1]

    Eq << Eq[-1].simplify()

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2021-09-11
