from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(LessEqual[Minima])
    return Any(fx <= M, *limits)


@prove(provable=False)
def prove(Eq):
    from Lemma import Algebra

    M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Minima[x:a:b](f(x)) <= M)

    return
    Eq << ~Eq[-1]

    Eq << Algebra.All_gt.then.minima_gt.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]

    


if __name__ == '__main__':
    run()
# created on 2019-12-01
# updated on 2023-11-12
