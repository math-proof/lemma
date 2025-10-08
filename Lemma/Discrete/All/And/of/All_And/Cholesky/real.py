from util import *


@apply
def apply(All_And):
    (((L, t, i), (((A, S[t], S[i]), (S[L[t, :i]], S[L[i, :i]])), S[L[i, i]])), (S[L[i, i]], S[Interval.open(0, oo)]), (((S[L], S[i], j), S[Reals]), (S[j], S[0], S[i]))), (S[i], S[0], t) = \
    All_And.of(All[Equal[Indexed, (Indexed - MatMul) / Expr] & Element & All[Element[Indexed]]])
    return All[j:t](Element(L[t, j], Reals) & Equal(A[t, j], L[t, :j + 1] @ L[j, :j + 1]))

@prove
def prove(Eq):
    from Lemma import Algebra, Set, Discrete, Bool, Tensor

    n, t = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), real=True)
    L = Symbol(shape=(n, n), super_real=True)
    i, j = Symbol(integer=True)
    Eq << apply(
        All[i:t](Equal(L[t, i],  (A[t, i] - L[t, :i] @ L[i, :i]) / L[i, i]) & Element(L[i, i], Interval.open(0, oo)) & All[j:i](Element(L[i, j], Reals))))

    Eq << Bool.All_And.given.All.All.apply(Eq[1])

    Eq[-1], Eq.Lij_is_real = Bool.All.All.of.All_And.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(Set.EqMul.of.IsPositive.Eq, ret=1)

    Eq.Ati_def, Eq.Lii_is_positive = Bool.All.All.of.All_And.apply(Eq[-1])

    k = Symbol(domain=Range(t), given=False)
    # apply the second mathematical induction
    Eq.hypothesis = All[j:k](Element(L[t, j], Reals), plausible=True)

    Eq.induct = Eq.hypothesis.subs(k, k + 1)

    Eq << Algebra.All.given.And.All.split.apply(Eq.induct, cond=Equal(j, k))

    Eq << Algebra.Cond.of.All.subst.apply(Eq.Lij_is_real, i, k)

    Eq <<= Eq.hypothesis & Eq[-1]

    Eq << Eq[-1].this.expr.apply(Set.IsReal.of.IsReal.IsReal)

    Eq << Set.IsReal.Sum.of.All_IsReal.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Tensor.Sum.eq.Dot)

    Eq << Element(A[t, k], Reals, plausible=True)

    Eq << Set.IsReal.Sub.of.IsReal.IsReal.apply(Eq[-1], Eq[-2])

    Eq.Lkk_is_positive = Algebra.Cond.of.All.subst.apply(Eq.Lii_is_positive, i, k)

    Eq << Set.IsReal.of.IsReal.IsPositive.apply(Eq[-1], Eq.Lkk_is_positive)

    Eq << Algebra.Cond.of.All.subst.apply(Eq.Ati_def, i, k).this.find(MatMul).T

    Eq <<= Eq[-2].subs(Eq[-1].reversed)

    Eq << Bool.Cond.of.And.apply(Eq[-1], -1)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Bool.Cond.of.All_Imp.apply(Eq[-1], k, 0)

    Eq << Bool.Cond.of.Imp.Cond.apply(Eq.hypothesis, Eq[-1])

    Eq << Eq.induct.subs(k, t - 1)

    Eq << Eq.Ati_def.this.find(MatMul).apply(Tensor.Dot.eq.Sub.push)

    Eq << Eq[-1].limits_subs(i, j)

    Eq << Eq[-1].this.expr.reversed




if __name__ == '__main__':
    run()
# created on 2023-06-29
