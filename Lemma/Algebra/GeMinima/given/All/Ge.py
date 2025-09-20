from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(GreaterEqual[Minima])
    return All(fx >= M, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Minima[x:a:b](f(x)) >= M)
    Eq << Algebra.GeMinima.of.All_Ge.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-06-08
