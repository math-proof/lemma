from util import *


@apply
def apply(given):
    e, domain = given.of(Element)
    S, s = domain.of(Complement)

    return NotElement(e, s)


@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    s, S = Symbol(etype=dtype.integer, given=True)


    Eq << apply(Element(e, S - s, evaluate=False))

    Eq << ~Eq[-1]

    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2018-01-13

