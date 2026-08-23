from util import *


@apply
def apply(le, Any_All_Ge):

    ((an, M), (n, S[0], S[oo])), (S[M],) = Any_All_Ge.of(Any[All[GreaterEqual]])
    S[an._subs(n, n + 1)], S[an] = le.of(LessEqual)
    return Equal(Limit[n:oo](an), Inf[n:oo](an))


@prove
def prove(Eq):
    from Lemma import Set, Real, Bool, Nat, Int

    a = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True)
    M = Symbol(real=True)
    Eq << apply(a[n + 1] <= a[n], Exists[M](ForAll[n:oo](a[n] >= M)))

    N = Symbol(integer=True, nonnegative=True)
    epsilon = Symbol(real=True, positive=True)
    Eq.any_lt = Exists[N](a[N] < Eq[2].find(Inf) + epsilon, plausible=True)

    Eq << ~Eq.any_lt

    Eq << Eq[-1].this.expr.apply(Real.GeInf.of.All_Ge)

    Eq.any_ge = Eq[-1].this.find(Inf).limits_subs(N, n)

    Eq << Eq[1].this.expr.apply(Real.GeInf.of.All_Ge)

    Eq << Eq[-1].this.expr.apply(Int.LtSub_1.of.Le, lower=-oo)

    Eq.le_inf = Real.All_LeInf.apply(Eq[-1].lhs)

    Eq << Nat.Lt_Add_1.of.Le.apply(Eq.le_inf, upper=oo)

    Eq.inf_is_real = Set.In_Ioo.of.Lt.Lt.apply(Eq[-2], Eq[-1], simplify=None)

    Eq << Bool.Any_And.of.Any.All.apply(Eq.inf_is_real, Eq.any_ge, simplify=None)

    Eq << Eq[-1].this.expr.apply(Set.GeSub.of.Ge.In)

    Eq << Eq.any_lt.this.expr - epsilon

    Eq << Eq[-1].this.expr.reversed

    Eq << -Eq[-1].this.expr

    Eq.any_gt = Eq[-1].this.expr + a[N]

    Eq << Nat.All.Le.of.Le.monotone.apply(Eq[0], n, N)

    Eq << Set.AllIn_SDiff.of.All.apply(Eq[-1], domain=Range(N + 1, oo))

    Eq << Bool.All.And.of.Cond.All.apply(Eq.inf_is_real, Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Set.LeSub.of.Le.In)

    Eq << Bool.Any.All.And.of.All.Any.apply(Eq[-1], Eq.any_gt)

    Eq << Eq[-1].this.expr.expr.apply(Nat.Lt.of.Lt.Le)

    Eq << Int.EqAbs.of.Le.apply(Eq.le_inf)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Abs).apply(Int.Abs.Neg)

    Eq << Real.Eq.of.Any_All.limit_definition.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-24
