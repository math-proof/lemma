from util import *


@apply
def apply(ge, Any_All_Le):
    ((an, M), (n, S[0], S[oo])), (S[M],) = Any_All_Le.of(Any[All[LessEqual]])
    S[an._subs(n, n + 1)], S[an] = ge.of(GreaterEqual)
    return Equal(Limit[n:oo](an), Sup[n:oo](an))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Calculus, Logic

    a = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True)
    M = Symbol(real=True)
    Eq << apply(a[n + 1] >= a[n], Exists[M](ForAll[n:oo](a[n] <= M)))

    N = Symbol(integer=True, nonnegative=True)
    epsilon = Symbol(real=True, positive=True)
    Eq.any_gt = Exists[N](a[N] > Eq[2].find(Sup) - epsilon, plausible=True)

    Eq << ~Eq.any_gt

    Eq << Eq[-1].this.expr.apply(Algebra.LeSup.of.All_Le)

    Eq.any_le = Eq[-1].this.find(Sup).limits_subs(N, n)

    Eq << Eq[1].this.expr.apply(Algebra.LeSup.of.All_Le)

    Eq << Eq[-1].this.expr.apply(Algebra.Lt.of.Le.relax, upper=oo)

    Eq.ge_sup = Algebra.All_GeSup.apply(Eq[-1].lhs)

    Eq << Algebra.Gt.of.Ge.relax.apply(Eq.ge_sup, lower=-oo)

    Eq.sup_is_real = Set.In.Icc.of.Lt.Gt.apply(Eq[-2], Eq[-1], simplify=None)

    Eq << Logic.Any_And.of.Any.All.apply(Eq.sup_is_real, Eq.any_le, simplify=None)

    Eq << Eq[-1].this.expr.apply(Set.LeSub.of.Le.In)

    Eq << Eq.any_gt.this.expr + epsilon

    Eq << Eq[-1].this.expr.reversed

    Eq.any_lt = Eq[-1].this.expr - a[N]

    Eq << Algebra.All.Ge.of.Ge.monotone.apply(Eq[0], n, N)

    Eq << Set.AllIn_SDiff.of.All.apply(Eq[-1], domain=Range(N + 1, oo))

    Eq << -Eq[-1].this.expr

    Eq << Algebra.All.And.of.Cond.All.apply(Eq.sup_is_real, Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Set.LeAdd.of.Le.In)

    Eq << Algebra.Any.All.And.of.All.Any.apply(Eq[-1], Eq.any_lt)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.of.Lt.Le)

    Eq << Algebra.EqAbs.of.Ge.apply(Eq.ge_sup)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Abs).apply(Algebra.Abs.Neg)

    Eq << Calculus.Eq.of.Any_All.limit_definition.apply(Eq[-1])

    # https://en.wikipedia.org/wiki/Least-upper-bound_property
    # https://en.wikipedia.org/wiki/Monotone_convergence_theorem




if __name__ == '__main__':
    run()
# created on 2020-05-20
# updated on 2023-11-11
