from util import *


@apply
def apply(given):
    A, B = given.of(Subset)

    return Equal(A | B, B)


@prove
def prove(Eq):
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, B))

    Eq << Subset(B, B, plausible=True)

    Eq <<= Eq[-1] & Eq[0]

    Eq << Supset(*Eq[-1].args, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

# created on 2018-01-11
