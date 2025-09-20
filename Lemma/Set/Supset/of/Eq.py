from util import *


@apply
def apply(given):
    A, B = given.of(Equal)
    return Supset(A, B)


@prove
def prove(Eq):
    A, B = Symbol(etype=dtype.integer, given=True)

    equality = Equal(A, B)

    Eq << apply(equality)

    Eq << ~Eq[-1]

    Eq << Eq[-1].subs(equality)


if __name__ == '__main__':
    run()

# created on 2020-08-10
