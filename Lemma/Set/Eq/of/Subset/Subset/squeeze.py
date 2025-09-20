from util import *


@apply
def apply(a_less_than_x, x_less_than_b):
    A, B = a_less_than_x.of(Subset)
    S[B], S[A] = x_less_than_b.of(Subset)

    return Equal(A, B)


@prove
def prove(Eq):
    A, B = Symbol(etype=dtype.complex)

    Eq << apply(Subset(A, B), Subset(B, A))

    Eq <<= Eq[0] & Eq[1]



if __name__ == '__main__':
    run()
# created on 2020-09-06
