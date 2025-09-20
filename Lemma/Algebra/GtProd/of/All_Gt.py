from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Greater])
    for limit in limits:
        x, domain = limit.coerce_setlimit()
        assert domain.is_finiteset

    assert rhs.is_positive

    return Greater(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Logic, Set

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True, positive=True)
    Eq << apply(All[i:n](f(i) > g(i)))

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << Eq.induct.this.find(Product).apply(Algebra.Prod.eq.Mul.pop)

    Eq << Eq[-1].this.find(Greater[~Product]).apply(Algebra.Prod.eq.Mul.pop)

    Eq << Logic.ImpAndS.of.Imp.apply(Eq[2], cond=f(n) > g(n))

    Eq << Eq[-1].this.lhs.apply(Set.AllIn_Ico.Cond.given.AllIn_Icc.Le)

    Eq << Eq[-1].this.rhs.apply(Algebra.GtMul.of.Gt.Gt)

    Eq << Imply(Eq[2], Eq.induct, plausible=True)
    Eq << Logic.Cond.of.All_Imp.apply(Eq[-1], n=n, start=1)
    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq[2])




if __name__ == '__main__':
    run()

# created on 2019-01-20
# updated on 2023-04-23
