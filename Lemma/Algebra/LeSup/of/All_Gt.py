from util import *


@apply
def apply(given):
    (M, fx), *limits = given.of(All[Greater])
    return Sup(fx, *limits) <= M


@prove
def prove(Eq):
    from Lemma import Algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:a:b](M > f(x)))

    Eq << Eq[0].this.expr.apply(Algebra.Ge.of.Gt.relax)

    Eq << Algebra.LeSup.of.All_Ge.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-01-23
