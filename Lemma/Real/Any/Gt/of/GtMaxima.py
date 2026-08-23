from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Greater[Maxima])
    return Any(fx > M, *limits)


@prove(provable=False)
def prove(Eq):
    M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Maxima[x:a:b](f(x)) > M)








if __name__ == '__main__':
    run()
# created on 2018-12-31
