from util import *


@apply
def apply(n, d, index):
    Q, K, V = Symbol(shape=(n, d), real=True)

    z = Symbol(softmax(Q @ K.T / sqrt(d)) @ V)

    return Equal(z[index], softmax(Q[index] @ K.T / sqrt(d)) @ V)


@prove
def prove(Eq):
    n = Symbol(integer=True)
    d = Symbol("d_z", integer=True)
#     i = Symbol(integer=True)
    h = Symbol(domain=Range(n + 1))
    Eq << apply(n, d, slice(0, h))

    M = Symbol(Eq[0].rhs.args[0].arg)
    Eq << M.this.definition

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Eq[-1][:h]

    Eq << Eq[2][:h]

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-08-25
