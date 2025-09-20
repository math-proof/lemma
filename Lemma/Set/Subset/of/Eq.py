from util import *


@apply
def apply(given):
    A, B = given.of(Equal)
    return Subset(A, B)


@prove
def prove(Eq):
    A, B = Symbol(etype=dtype.integer, given=True)

    equality = Equal(A, B, evaluate=False)

    Eq << apply(equality)

    Eq << ~Eq[-1]

    Eq << Eq[-1].subs(equality)


if __name__ == '__main__':
    run()

# created on 2020-10-24
