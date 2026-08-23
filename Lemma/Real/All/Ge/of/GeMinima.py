from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(GreaterEqual[Minima])
    return All(fx >= M, *limits)


@prove(provable=False)
def prove(Eq):
    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Minima[x:a:b](f(x)) >= M)


if __name__ == '__main__':
    run()
# created on 2019-01-03
