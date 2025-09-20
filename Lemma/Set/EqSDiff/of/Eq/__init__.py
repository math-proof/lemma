from util import *
# given : A & B = A | B => A = B


@apply
def apply(given, S):
    A, B = given.of(Equal)
    return Equal(Complement(A, S), Complement(B, S))


@prove
def prove(Eq):
    A, B, S = Symbol(etype=dtype.integer)


    Eq << apply(Equal(A, B), S)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-09-04

del Eq
from . import Eq
