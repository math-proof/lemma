from util import *


@apply
def apply(given):
    fn, fn1 = given.of(Iff)
    return Imply(fn, fn1), Imply(fn1, fn)


@prove
def prove(Eq):
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Iff(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-01-23
