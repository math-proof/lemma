from util import *


@apply
def apply(Any_All_et_ge):
    (((M, an1), (an1, an)), (n, S[0], S[oo])), (S[M],) = Any_All_et_ge.of(Any[All[LessEqual & LessEqual]])
    S[an1] = an._subs(n, n + 1)
    return Equal(Limit[n:oo](an), Inf[n:oo](an))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Bool

    a = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True)
    M = Symbol(real=True)
    Eq << apply(Exists[M](ForAll[n:oo]((M <= a[n + 1]) & (a[n + 1] <= a[n]))))

    Eq << Eq[0].this.find(And).apply(Algebra.Le.of.Le.Le, ret=1)

    Eq << Eq[-1].this.expr.apply(Bool.All.All.of.All_And)

    Eq << Bool.And_And.of.And.apply(Eq[-1])

    Eq << Eq[-2].this.expr.expr.reversed

    Eq << Calculus.Limit.eq.Inf.of.Le.Any_All_Ge.monotone_convergence_theorem.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2024-06-27
