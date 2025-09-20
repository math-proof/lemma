from util import *


@apply
def apply(given):
    x, R = given.of(Element)

    assert NotElement(0, R)
    return Unequal(x, 0)


@prove
def prove(Eq):
    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2020-05-13
