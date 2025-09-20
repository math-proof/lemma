from util import *


@apply
def apply(eq, S):
    # given : A & B = A | B => A = B
    A, B = eq.of(Equal)
    return Equal(A & S, B & S)


@prove
def prove(Eq):
    A, B, S = Symbol(etype=dtype.integer)


    Eq << apply(Equal(A, B), S)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2019-02-01

del Eq
from . import Eq
