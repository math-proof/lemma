from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(LessEqual[Maxima])
    return All(fx <= M, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Maxima[x:a:b](f(x)) <= M)

    Eq << Algebra.LeMaxima.of.All_Le.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-01-01
