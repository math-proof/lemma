from util import *


@apply
def apply(given):
    A, B = given.of(Subset)

    return Equal(A & B, A)


@prove
def prove(Eq):
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, B))

    Eq << Subset(A & B, B, plausible=True)
    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-11-20
