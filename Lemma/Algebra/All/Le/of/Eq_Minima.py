from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Equal[Minima])
    return All(M <= fx, *limits)


@prove(provable=False)
def prove(Eq):
    M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(M, Minima[x:0:oo](f(x))))


if __name__ == '__main__':
    run()
# created on 2019-01-16
