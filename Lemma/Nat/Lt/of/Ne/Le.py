from util import *


@apply
def apply(ne, le):
    x, a = ne.of(Unequal)
    S[x], S[a] = le.of(LessEqual)
    return x < a


@prove
def prove(Eq):
    a, x = Symbol(real=True)
    Eq << apply(Unequal(x, a), x <= a)

    Eq <<= Eq[1] & Eq[0]

    


if __name__ == '__main__':
    run()
# created on 2023-04-13
