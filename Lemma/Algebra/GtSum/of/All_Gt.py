from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Greater])
    for limit in limits:
        x, domain = limit.coerce_setlimit()
        assert domain.is_finiteset
    return Greater(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Set

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(All[i:n](Greater(f(i), g(i))))

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << Bool.ImpAndS.of.Imp.apply(Eq[2], cond=f(n) > g(n))

    Eq << Eq[-1].this.lhs.apply(Set.AllIn_Ico.Cond.given.AllIn_Icc.Le)

    Eq << Eq[-1].this.rhs.apply(Algebra.GtAdd.of.Gt.Gt)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Sub.push)

    Eq << Eq[-1].this.find(Add[~Sum]).apply(Algebra.Sum.eq.Sub.push)

    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.All_Imp.apply(Eq[-1], n=n, start=1)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq[2])





if __name__ == '__main__':
    run()

# created on 2019-01-22
# updated on 2023-04-23
