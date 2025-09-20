from util import *


@apply
def apply(given, S):
    e, s = given.of(Element)

    return NotElement(e, S - s)


@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    s, S = Symbol(etype=dtype.integer, given=True)


    Eq << apply(Element(e, s, evaluate=False), S)

    Eq << ~Eq[-1]

    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2021-08-19
