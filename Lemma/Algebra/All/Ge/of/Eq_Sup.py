from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Equal[Sup])
    return All(M >= fx, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(M, Sup[x:a:b](f(x))))

    Eq << Nat.Ge.of.Eq.apply(Eq[0]).reversed

    Eq << Algebra.All.Le.of.LeSup.apply(Eq[-1])
    Eq << Eq[-1].this.expr.reversed


if __name__ == '__main__':
    run()
# created on 2018-12-27
