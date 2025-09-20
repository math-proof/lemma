from util import *


@apply
def apply(all_le):
    (fx, M), *limits = all_le.of(All[GreaterEqual])
    return Minima(fx, *limits) >= M


@prove
def prove(Eq):
    from Lemma import Algebra

    M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    S = Symbol(etype=dtype.real, given=True)
    Eq << apply(All[x:S](f(x) >= M))

    Eq << ~Eq[-1]

    Eq << Algebra.Any.Lt.of.LtMinima.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-01-02
