from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Equal[Sup])
    return All(fx <= M, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(M, Sup[x:a:b](f(x))))

    Eq << Algebra.All.Ge.of.Eq_Sup.apply(Eq[0])

    Eq << Eq[-1].this.expr.reversed


if __name__ == '__main__':
    run()
# created on 2018-12-28
