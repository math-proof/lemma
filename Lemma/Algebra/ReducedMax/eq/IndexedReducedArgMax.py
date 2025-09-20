from util import *


@apply
def apply(self):
    return Equal(ReducedMax(self), self[ReducedArgMax(self)])


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(x[:n])

    k = Symbol(Eq[0].find(ReducedArgMax))
    Eq << k.this.defun()

    Eq << Eq[0].subs(Eq[1].reversed)

    Eq << Eq[-1].this.lhs.apply(Algebra.ReducedMax.eq.Maxima)

    Eq << Algebra.All_Le_Maxima.apply(Eq[-1].lhs)

    i = Eq[-1].variable
    Eq.le = Algebra.Cond.of.All.subst.apply(Eq[-1], i, k)

    Eq << Algebra.All.Ge.of.Eq_ReducedArgMax.apply(Eq[1])

    Eq << Eq[-1].this.expr.reversed

    Eq << Algebra.LeMaxima.of.All_Le.apply(Eq[-1])


    Eq <<= Eq[-1] & Eq.le


if __name__ == '__main__':
    run()
# created on 2023-11-12
# updated on 2023-11-13
