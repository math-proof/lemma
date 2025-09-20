from util import *


@apply
def apply(given):
    (fx, M), *limits = given.of(All[Less])
    return Sup(fx, *limits) <= M


@prove
def prove(Eq):
    from Lemma import Algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:a:b](f(x) < M))

    Eq << Eq[0].this.expr.reversed
    Eq << Algebra.LeSup.of.All_Gt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-01-28
