from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[GreaterEqual])
    assert rhs.is_nonnegative

    return GreaterEqual(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Set

    n = Symbol(integer=True, positive=True, given=False)
    i = Symbol(integer=True)
    g = Function(shape=(), real=True, nonnegative=True)
    f = Function(shape=(), real=True)
    Eq << apply(All[i:n](f(i) >= g(i)))

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << Eq.induct.this.find(Product).apply(Algebra.Prod.eq.Mul.pop)

    Eq << Eq[-1].this.find(GreaterEqual[~Product]).apply(Algebra.Prod.eq.Mul.pop)

    Eq << Bool.ImpAndS.of.Imp.apply(Eq[2], cond=f(n) >= g(n))

    Eq << Eq[-1].this.lhs.apply(Set.AllIn_Ico.Cond.given.AllIn_Icc.Le)

    Eq << Eq[-1].this.rhs.apply(Algebra.GeMul.of.Ge.Ge)

    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.All_Imp.apply(Eq[-1], n=n, start=1)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq[2])





if __name__ == '__main__':
    run()

# created on 2019-01-12
# updated on 2023-04-23
