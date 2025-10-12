from util import *


@apply
def apply(eq, forall):
    wi, i_limit = eq.of(Equal[Sum, 1])
    (S[wi], (xi, domain)), S[i_limit] = forall.of(All[And[Expr >= 0, Element]])
    i, S[0], n = i_limit

    return Element(Sum[i:n](wi * xi), domain)

@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Finset

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    a, b = Symbol(real=True)
    w, x = Symbol(real=True, shape=(oo,))
    Eq << apply(Equal(Sum[i:n](w[i]), 1), All[i:n]((w[i] >= 0) & Element(x[i], Interval(a, b))))

    Eq.hypothesis = Imply(Eq[0] & Eq[1], Eq[2], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq << Bool.Imp_And.given.Imp.And.subst.apply(Eq.initial, index=0)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.find(All).apply(Bool.All.All.of.All_And)

    Eq << Eq[-1].this.find(Element[~Sum]).apply(Algebra.Sum.eq.Add.pop)

    Eq.lt, Eq.ge = Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=w[n] < 1)

    Eq << Eq.ge.this.rhs.apply(Bool.Imp.fold, 2, swap=True)

    Eq << Eq[-1].this.apply(Bool.Imp.flatten)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqAll_Eq_0.of.Eq_Sum.Ge.All_Ge_0.squeeze)

    Eq << Eq[-1].this.find(All[Element]).apply(Algebra.Cond.of.All.subst, i, n)

    Eq << Bool.Imp_And.given.Imp.And.subst.apply(Eq[-1])

    Eq << Eq[-1].this.find(All).apply(Algebra.Sum.eq.Zero.Mul.of.All_Eq_0, x)

    Eq << Bool.Imp_And.given.Imp.And.subst.apply(Eq[-1], index=1)

    Eq << Eq.lt.this.rhs.apply(Bool.Imp.fold)

    Eq << Eq[-1].this.apply(Bool.Imp.flatten)

    Eq << Eq[-1].this.find(Equal[~Sum]).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.find(Equal) - w[n]

    Eq << Eq[-1].this.lhs.apply(Algebra.EqDiv.of.Eq.Lt, ret=1)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.find(All).apply(Algebra.All.Is.And.split, cond={n})

    Eq << Eq[-1].this.find(All[2]).apply(Algebra.All.Is.And.split, cond={n})

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.fold, 2)

    Eq << Eq[-1].this.apply(Bool.Imp.flatten)

    Eq << Eq[-1].this.apply(Bool.Imp.fold, slice(1, None))

    Eq << Eq[-1].this.lhs.apply(Algebra.All.And.of.Cond.All, simplify=None)

    Eq << Eq[-1].this.lhs.find(And).apply(Algebra.GeDiv.of.Lt.Ge, ret=0)

    Eq << Eq[-1].this.apply(Bool.Imp.swap)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.flatten)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.fold, slice(0, 2), swap=True)

    Eq << Eq[-1].this.rhs.rhs.lhs.apply(Set.In.Icc.of.Lt.Ge)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.fold, 0, swap=True)

    Eq << Eq[-1].this.find(All & All).apply(Bool.All_And.of.All.All)

    Eq << Eq[-1].this.apply(Bool.Imp.flatten)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp.flatten)

    w_ = Symbol('w', Stack[i:n](w[i] / (1 - w[n])))
    Eq << (w_[i].this.definition * (1 - w[n])).reversed

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Cond.of.Cond.subst.apply(Eq.hypothesis, w[:n], w_)

    Eq << Bool.Imp.of.Cond.apply(Eq[-1], cond=Eq[-2].rhs.lhs)

    Eq << Eq[-1].this.apply(Bool.Imp.swap)

    Eq << Eq[-1].this.rhs.apply(Bool.Imp_And.of.ImpAnd)

    Eq << Eq[-1].this.rhs.rhs.apply(Set.In.Icc.of.In.In.In)

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1].this.rhs.find(Sum).simplify()

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Bool.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=1)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq[0] & Eq[1], Eq.hypothesis)





if __name__ == '__main__':
    run()
# created on 2020-05-31
# updated on 2023-05-21
