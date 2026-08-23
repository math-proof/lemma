from util import *


@apply
def apply(given):
    x, b = given.of(LessEqual)
    domain = x.domain
    b, a = domain.of(Range)

    return Equal(x, b)


@prove
def prove(Eq):
    a = Symbol(integer=True)
    b = Symbol(integer=True, given=True)
    x = Symbol(domain=Range(b, a), given=True)

    Eq << apply(x <= b)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2021-08-28
