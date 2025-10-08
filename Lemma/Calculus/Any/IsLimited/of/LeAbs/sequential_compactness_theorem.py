from util import *


@apply
def apply(given, a=None):
    (x, n), M = given.of(Abs[Indexed] <= Expr)
    if a is None:
        a = given.generate_var(integer=True, shape=(oo,), var='a')

    return Any[a:All[n:1:oo](a[n - 1] < a[n])](Element(Limit[n:oo](x[a[n]]), Reals))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Bool

    x = Symbol(real=True, shape=(oo,))
    M = Symbol(real=True, positive=True)
    n, m = Symbol(integer=True)
    Eq << apply(Abs(x[n]) <= M)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[1], cond=Card({n: All[m:n + 1:oo](x[m] <= x[n])}) < oo)

    Eq << Bool.Imp.given.And.Imp.invert.apply(Eq[-2], cond=Eq[0])

    Eq << Bool.Or.given.Cond.apply(Eq[-1], 0)

    a = Eq[1].variable
    Eq << Eq[-2].this.lhs.apply(Calculus.Any.IsLimited.of.LeAbs.Le_Infty.sequential_compactness_theorem, a)

    Eq << Eq[3].this.lhs.apply(Algebra.Eq.of.Ge.squeeze)

    Eq << Bool.Imp.given.And.Imp.invert.apply(Eq[-1], cond=Eq[0])

    Eq << Bool.Or.given.Cond.apply(Eq[-1], 1)

    Eq << Eq[-2].this.lhs.apply(Calculus.Any.IsLimited.of.LeAbs.Eq_Infty.sequential_compactness_theorem, a)

    # https://en.wikipedia.org/wiki/Bolzano%E2%80%93Weierstrass_theorem



if __name__ == '__main__':
    run()
# created on 2023-11-11
# updated on 2023-11-15
