from util import *


@apply
def apply(given, reverse=False):
    p, q = given.of(Iff)
    if reverse:
        return Imply(q, p)
    return Imply(p, q)


@prove
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Iff(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Given(*Eq[1].args, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]

    


if __name__ == '__main__':
    run()
# created on 2018-01-25
# updated on 2025-04-12
