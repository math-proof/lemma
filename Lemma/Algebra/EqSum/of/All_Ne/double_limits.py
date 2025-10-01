from util import *


@apply
def apply(all_ne, sgm):
    (ai, aj), (j, S[0], i), (S[i], S[0], n) = all_ne.of(All[Unequal])
    if ai._has(j):
        ai, xj = aj, ai

    assert ai._subs(i, j) == aj

    fx, (x, X) = sgm.of(Sum)

    _ai, (_i, S[0], n) = X.of(Cup[FiniteSet])
    assert _ai._subs(_i, i) == ai

    return Equal(sgm, Sum[i:n](fx._subs(x, ai)))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    X = Symbol(etype=dtype.real)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    s = a[:n].cup_finiteset()
    Eq << apply(All[j:i, i:n](Unequal(a[i], a[j])), Sum[x:s](f(x)))

    Eq.hypothesis = Imply(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Algebra.All.Is.And.split, cond={n})

    Eq << Eq[-1].this.find(All).apply(Algebra.EqSum.of.All_Ne, Eq.hypothesis.rhs.lhs)

    Eq << Eq[-1].this.lhs.find(Equal).apply(Algebra.EqAdd.Is.Eq_Sub, rhs=0)

    Eq << Eq[-1].this.lhs.find(Equal).reversed

    Eq << Logic.ImpAndS.of.Imp.apply(Eq.hypothesis, cond=Eq[-1].lhs.find(Equal))

    Eq << Eq[-1].this.rhs.apply(Algebra.EqAdd.of.Eq.Eq)

    Eq << Eq[-1].this.rhs.rhs.apply(Algebra.Add.eq.Sum.limits.push)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Logic.Cond.of.All_Imp.apply(Eq[-1], n=n, start=1)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq[0], Eq.hypothesis)





if __name__ == '__main__':
    run()
# created on 2019-02-05
# updated on 2023-05-21
