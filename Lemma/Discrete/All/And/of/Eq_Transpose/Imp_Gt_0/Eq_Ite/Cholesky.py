from util import *


def extract(eq, infer, eq_piece):
    A, S[A] = eq.of(Equal[Transpose])
    x, S[x @ A @ x] = infer.of(Imply[Unequal[0], Expr > 0])
    (L, i, j), (((sub, S[L[j, j]]), S[j < i]), (sub1, S[Equal(j, i)]), (S[0], S[True])) = \
    eq_piece.of(Equal[
        Indexed,
        Piecewise[
            ExprCondPair[Expr / Expr],
            ExprCondPair[Expr ** S.Half],
        ]
    ])

    S[A[i, j]], (S[L[i, :j]], S[L[j, :j]]) = sub.of(Expr - Expr @ Expr)
    S[A[i, i]], S[L[i, :i]] = sub1.of(Expr - Norm ** 2)
    return A, L, x, i, j

@apply
def apply(eq, infer, eq_piece, t):
    A, L, x, i, j = extract(eq, infer, eq_piece)
    return All[i:t](And(
        Element(L[i, i], Interval.open(0, oo)),
        Equal(A[i, i], Norm(L[i,:i + 1]) ** 2),
        All[j:i](And(
            Element(L[i, j], Reals),
            Equal(A[i, j], L[i,:j + 1] @ L[j,:j + 1])))))

@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Set, Logic

    n = Symbol(domain=Range(10, oo))
    A = Symbol(shape=(n, n), real=True)
    x = Symbol(shape=(n,), real=True)
    L = Symbol(shape=(n, n), super_real=True)
    i, j = Symbol(integer=True)
    t = Symbol(domain=Range(3, n), given=False)
    *Eq[-3:], Eq.hypothesis = apply(Equal(A.T, A),
               Imply(Unequal(x, Zeros(n)), x @ A @ x > 0),
               Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ L[j, :j]) / L[j, j], j < i), (sqrt(A[i, i] - Norm(L[i, :i]) ** 2), Equal(j, i)), (0, True))), t)

    Eq << Logic.Imp.of.Cond_Ite.apply(Eq[2])

    Eq.gt_zero, Eq.Atj_def_and_Ltj_is_real = Discrete.And.of.Eq_Transpose.Imp_Gt_0.Imp_Eq.All_And.Cholesky.apply(Eq[0], Eq[1], Eq[-1], Eq.hypothesis)

    Eq << Logic.All.of.All_And.apply(Eq.Atj_def_and_Ltj_is_real, 1)

    Eq << Eq[-1].this.expr.apply(Set.IsNotNegative.Square.of.IsReal)

    Eq << Set.IsReal.Sum.of.All_IsReal.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Square.Norm, simplify=None)

    Eq << Element(A[t, t], S.Complexes, plausible=True)

    Eq << Set.IsComplex.Sub.of.IsComplex.IsComplex.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Gt_0.of.Gt.apply(Eq.gt_zero)

    Eq << Set.IsPositive.of.Gt_0.IsComplex.apply(Eq[-1], Eq[-2])

    Eq << Set.IsPositive.Sqrt.of.IsPositive.apply(Eq[-1])

    Eq << Eq[2].subs(i, t).subs(j, t).reversed

    Eq <<= Eq[-2].subs(Eq[-1]), Eq[-1] ** 2

    Eq <<= Set.Eq.Square.Abs.of.IsReal.apply(Eq[-2], reverse=True), Eq[-1] - Add(*Eq[-1].lhs.args[1:])

    Eq << Eq[-1].subs(Eq[-2]).this.find(Norm ** 2).apply(Algebra.Square.Norm.eq.Sub.push)

    Eq.induct = Eq.hypothesis.subs(t, t + 1)

    Eq << Algebra.All.given.And.All.split.apply(Eq.induct, cond=Equal(i, t))

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Logic.Cond.of.All_Imp.apply(Eq[-1], t, 0)





if __name__ == '__main__':
    run()
# created on 2023-06-28
# updated on 2023-06-29
