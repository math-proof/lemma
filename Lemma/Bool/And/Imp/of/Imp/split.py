from util import *


@apply
def apply(given, *, cond=None):
    p, q = given.of(Imply)

    return Imply(p & cond, q), Imply(p & cond.invert(), q)


@prove
def prove(Eq):
    f, g = Function(integer=True)
    x, y = Symbol(integer=True)
    Eq << apply(Imply(Equal(f(x), f(y)), Equal(g(x), g(y))), cond=x > 0)
    
    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()
# created on 2023-04-25
