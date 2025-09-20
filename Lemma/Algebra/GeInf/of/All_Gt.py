from util import *


@apply
def apply(given):
    (fx, M), *limits = given.of(All[Greater])
    return Inf(fx, *limits) >= M


@prove
def prove(Eq):
    from Lemma import Algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:a:b](f(x) > M))

    Eq << Eq[0].this.expr.apply(Algebra.Ge.of.Gt.relax)
    Eq << Algebra.GeInf.of.All_Ge.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-01-19
