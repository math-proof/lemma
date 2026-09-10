from util import *


@apply
def apply(given):
    e, domain = given.of(Element)
    A, B = domain.of(Complement)

    return Element(e, A), NotElement(e, B)


@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A - B))

    Eq <<= Eq[-2] & Eq[-1]

    


if __name__ == '__main__':
    run()

# created on 2020-11-17
# updated on 2023-04-24
