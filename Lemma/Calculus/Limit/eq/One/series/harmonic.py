from util import *


@apply
def apply(n):
    k = Symbol(integer=True)
    return Equal(Limit[n:oo](Sum[k:1:n](1 / k) / log(n + 1)), 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Set, Logic

    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    x = Symbol(real=True)
    x0 = Symbol(real=True, positive=True)
    Eq.is_continuous = Equal(Limit[x:x0](1 / x), 1 / x0, plausible=True)

    Eq << Eq.is_continuous.this.lhs.doit()

    k, *ab = Eq[-1].lhs.args[0].args[-1].limits[0]
    k = k.copy(domain=Range(*ab))
    Eq << Eq.is_continuous.apply(Logic.AllIn.of.All, (x0, Interval(k, k + 1)))

    Eq.mean_value_theorem = Calculus.Any.Eq.of.IsContinuous.mean_value_theorem.apply(Eq[-1])

    Eq << Algebra.All.limits_assert.apply(Eq[-1].limits)

    Eq << Eq[-1].this.expr.apply(Set.In.Inv.Icc.of.In)

    Eq << Eq[-1].this.expr.apply(Set.Ge.Le.of.In_Icc)

    Eq << Logic.All.All.of.All_And.apply(Eq[-1])

    Eq <<= Logic.Any_And.of.Any.All.All_Imp.apply(Eq[-2], Eq.mean_value_theorem), Logic.Any_And.of.Any.All.All_Imp.apply(Eq[-1], Eq.mean_value_theorem)

    Eq <<= Eq[-2].this.expr.apply(Logic.Cond.of.Eq.Cond.subst, reverse=True), \
    Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subst, reverse=True)

    Eq <<= Eq[-2].apply(Logic.AllIn.of.All, (k, 1, n)), Eq[-1].apply(Logic.AllIn.of.All, (k, 1, n - 1))

    Eq <<= Algebra.LeSum.of.All_Le.apply(Eq[-2]), Algebra.GeSum.of.All_Ge.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.doit(), Eq[-1].this.lhs.doit().reversed

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.subst.offset, -1) + 1

    Eq <<= Eq[-3] / Eq[-3].lhs, Eq[-1] / Eq[-3].lhs

    Eq <<= Calculus.LeLimit.of.Le.apply(Eq[-2], (n, oo)), Calculus.LeLimit.of.Le.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.rhs.doit()

    Eq <<= Eq[-1] & Eq[-3]


if __name__ == '__main__':
    run()

# created on 2020-06-25
