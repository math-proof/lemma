from util import *


@apply
def apply(all_historic, y=None):
    (xi, xj), (j, S[0], i), (S[i], S[0], n) = all_historic.of(All[Unequal])
    if xi._has(j):
        xi, xj = xj, xi

    assert xi._subs(i, j) == xj
    if y is None:
        y = all_historic.generate_var(**xi.dtype.dict, shape=(oo,))
    return Any[y[:n]:All[i:1:n](y[i - 1] < y[i])](Equal(Cup[i:n]({y[i]}), Cup[i:n]({xi})))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    x, y = Symbol(shape=(oo,), real=True)
    Eq << apply(All[j:i, i:n](Unequal(x[i], x[j])), y)

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.expr.simplify()

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Set.Any.And.Cup.Finset.of.All_Ne)

    a = Eq[-1].lhs.variable
    Eq << Algebra.Cond.of.Cond.subst.apply(Eq[2], x[:n], a[:n])

    Eq << Bool.Imp.given.And.Imp.invert.apply(Eq[-2], cond=Eq[-1])

    Eq << Bool.Or.given.Cond.apply(Eq[-1], index=0)

    Eq << Eq[-2].this.lhs.apply(Bool.Any_And.of.Any.All)

    Eq << Eq[-1].this.find(And).args[1:].apply(Bool.Cond.of.Imp.Cond)

    Eq << Any[y[n]](Equal(y[n], a[n]), plausible=True)

    Eq << Eq[-1].simplify()

    Eq << Bool.Imp.given.And.Imp.invert.apply(Eq[-2], cond=Eq[-1])

    Eq << Bool.Or.given.Cond.apply(Eq[-1], index=0)

    Eq << Eq[-2].this.lhs.apply(Bool.Any_And.of.Any.All)

    Eq << Eq[-1].this.find(And).args[:2].apply(Bool.Any_And.of.Any.All, simplify=None)

    Eq << Eq[-1].this.find(Equal & Greater).apply(Algebra.Gt.of.Eq.Gt, ret=0)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Any.And.of.Any.Any, simplify=0)

    Eq << Eq[-1].this.find(Equal[Cup]).apply(Set.EqReducedMax.of.Eq_Cup, ret=0, simplify=None)

    Eq << Eq[-1].this.find(And).args[1::2].apply(Algebra.Gt.of.Eq.Gt, simplify=None)

    Eq << Eq[-1].this.find(Equal).apply(Set.Eq.of.Eq.set, simplify=None)

    Eq << Eq[-1].this.find(And).args[:2].apply(Set.EqCupSIn_Icc.of.EqCupSIn_Ico.Eq.Le, simplify=None)

    Eq << Eq[-1].this.lhs.apply(Bool.Any_And.of.AnySetOf_AnySetOf, -1)

    Eq << Eq[-1].this.find(And).args[:2].apply(Bool.Eq.of.Eq.Eq, -1)

    Eq << Eq[-1].this.lhs.apply(Bool.Any_And.of.AnySetOf_AnySetOf)

    Eq << Eq[-1].this.find(ReducedMax).apply(Algebra.ReducedMax.eq.Maxima)

    Eq << Eq[-1].this.find(Greater).reversed

    Eq << Eq[-1].this.find(Less).apply(Algebra.All.Lt.of.LtMaxima)

    Eq << Eq[-1].this.find(All).apply(Algebra.Cond.of.All.subst, i, n - 1)

    Eq << Eq[-1].this.find(And).args[1:].apply(Algebra.All.of.Cond.All.push)

    Eq << Eq[-1].this.lhs.apply(Bool.AnySetOf.of.Any_And, 1)

    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], start=1, n=n)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0], Eq[2])


if __name__ == '__main__':
    run()
# created on 2023-11-12
