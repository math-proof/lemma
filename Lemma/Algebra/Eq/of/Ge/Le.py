from util import *


@apply
def apply(greater_than, less_than):
    a, b = greater_than.of(GreaterEqual)
    S[a], S[b] = less_than.of(LessEqual)

    return Equal(a, b)


@prove
def prove(Eq):
    a, b = Symbol(real=True)

    Eq << apply(a >= b, a <= b)

    Eq <<= Eq[0] & Eq[1]




if __name__ == '__main__':
    run()
# created on 2018-05-16
