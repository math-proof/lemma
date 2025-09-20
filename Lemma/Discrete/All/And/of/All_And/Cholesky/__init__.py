from util import *


@apply
def apply(All_And):
    (((L, t, i), (((A, S[t], S[i]), (S[L[t, :i]], S[~L[i, :i]])), S[L[i, i]])), (S[L[i, i]], S[Interval.open(0, oo)]), (((S[L], S[i], j), S[S.Complexes]), (S[j], S[0], S[i]))), (S[i], S[0], t) = \
    All_And.of(All[Equal[Indexed, (Indexed - MatMul) / Expr] & Element & All[Element[Indexed]]])
    return All[j:t](Element(L[t, j], S.Complexes) & Equal(A[t, j], L[t, :j + 1] @ ~L[j, :j + 1]))

@prove
def prove(Eq):
    from Lemma import Algebra, Set, Discrete, Logic, Tensor

    n, t = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), complex=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(
        All[i:t](Equal(L[t, i],  (A[t, i] - L[t, :i] @ ~L[i, :i]) / L[i, i]) & Element(L[i, i], Interval.open(0, oo)) & All[j:i](Element(L[i, j], S.Complexes))))

    Eq << Logic.All_And.given.All.All.apply(Eq[1])

    Eq[-1], Eq.Lij_is_complex = Logic.All.All.of.All_And.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(Set.EqMul.of.IsPositive.Eq, ret=1)

    Eq.Ati_def, Eq.Lii_is_positive = Logic.All.All.of.All_And.apply(Eq[-1])

    k = Symbol(domain=Range(t), given=False)
    # apply the second mathematical induction
    Eq.hypothesis = All[j:k](Element(L[t, j], S.Complexes), plausible=True)

    Eq.induct = Eq.hypothesis.subs(k, k + 1)

    Eq << Algebra.All.given.And.All.split.apply(Eq.induct, cond=Equal(j, k))

    Eq.Lij_conj_is_complex = Eq.Lij_is_complex.this.expr.apply(Set.IsComplex.Conj.of.IsComplex)

    Eq << Algebra.Cond.of.All.subst.apply(Eq.Lij_conj_is_complex, i, k)

    Eq <<= Eq.hypothesis & Eq[-1]

    Eq << Eq[-1].this.expr.apply(Set.IsComplex.of.IsComplex.IsComplex)

    Eq << Set.IsComplex.Sum.of.All_IsComplex.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Tensor.Sum.eq.Dot)

    Eq << Element(A[t, k], S.Complexes, plausible=True)

    Eq << Set.IsComplex.Sub.of.IsComplex.IsComplex.apply(Eq[-1], Eq[-2])

    Eq.Lkk_is_positive = Algebra.Cond.of.All.subst.apply(Eq.Lii_is_positive, i, k)

    Eq << Set.IsComplex.of.IsComplex.IsPositive.apply(Eq[-1], Eq.Lkk_is_positive)

    Eq << Algebra.Cond.of.All.subst.apply(Eq.Ati_def, i, k)

    Eq <<= Eq[-2].subs(Eq[-1].reversed)

    Eq << Logic.Cond.of.And.apply(Eq[-1], -1)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Logic.Cond.of.All_Imp.apply(Eq[-1], k, 0)

    Eq << Logic.Cond.of.Imp.Cond.apply(Eq.hypothesis, Eq[-1])

    Eq << Eq.induct.subs(k, t - 1)

    Eq << Eq.Ati_def.this.find(MatMul).apply(Tensor.Dot.eq.Sum)

    Eq << Logic.All_And.of.All.All.apply(Eq.Lij_conj_is_complex, Eq[3])

    Eq << Eq[-1].this.apply(Algebra.All.limits.separate, simplify=None)

    Eq << Eq[-1].this().find(Min).simplify()

    Eq << Eq[-1].this.expr.apply(Set.IsComplex.of.IsComplex.IsComplex)

    Eq << Eq[-1].this.apply(Algebra.All.limits.separate, simplify=None)

    Eq << Eq[-1].this.expr.apply(Set.IsComplex.Sum.of.All_IsComplex)

    Eq << Eq[-1].this.find(Sum).apply(Tensor.Sum.eq.Dot)

    Eq << Logic.All_And.of.All.All.apply(Eq.Ati_def, Eq[-1])

    Eq << Eq[-1].this.expr.apply(Set.EqAdd.of.IsComplex.Eq)

    Eq << Eq[-1].this.expr.reversed

    Eq << Eq.Lii_is_positive.this.expr.apply(Set.EqConj.of.IsReal, reverse=True)

    Eq << Logic.All_And.of.All.All.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.apply(Logic.UFn.of.UFn.Eq, swap=True)

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.Sub.push)

    Eq << Eq[-1].limits_subs(i, j)




if __name__ == '__main__':
    run()
# created on 2023-06-05
# updated on 2023-06-27
from . import real
