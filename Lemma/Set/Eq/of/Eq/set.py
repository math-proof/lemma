from util import *


@apply
def apply(given):
    A, B = given.of(Equal)
    return Equal(FiniteSet(A), FiniteSet(B))


@prove
def prove(Eq):
    A, B = Symbol(etype=dtype.integer)

    Eq << apply(Equal(A, B))

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-07-23
