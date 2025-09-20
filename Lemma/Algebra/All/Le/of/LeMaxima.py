from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(LessEqual[Maxima])
    return All(fx <= M, *limits)


@prove(provable=False)
def prove(Eq):
    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Maxima[x:a:b](f(x)) <= M)


if __name__ == '__main__':
    run()
# created on 2021-08-22
