from util import *


@apply
def apply(eq, infer, eq_piece):
    from Lemma.Discrete.All.And.of.Eq_Adjoint.Imp_Gt_0.Eq_Ite.Cholesky import extract
    A, L, *_ = extract(eq, infer, eq_piece)
    return Element(L, CartesianSpace(S.Complexes, *A.shape)), Equal(A, L @ ~L.T)

@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Set, Bool, Tensor

    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Equal(~A.T, A),
               Imply(Unequal(x, Zeros(n)), ~x @ A @ x > 0),
               Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ ~L[j, :j]) / L[j, j], j < i), (sqrt(A[i, i] - Norm(L[i, :i]) ** 2), Equal(j, i)), (0, True))))

    t = Symbol(positive=True, integer=True)
    Eq << Discrete.All.And.of.Eq_Adjoint.Imp_Gt_0.Eq_Ite.Cholesky.apply(*Eq[:3], t)

    Eq << Eq[-1].subs(t, n)

    Eq << Eq[-1].simplify()

    Eq.A_diagonal, *Eq[-2:] = Bool.And_And.of.And.apply(Eq[-1], None)

    Eq.eq_conj = Set.EqConj.of.IsReal.apply(Eq[-2])

    Eq <<= Bool.All.All.of.All_And.apply(Eq[-1]), Set.In_Union.of.In.apply(Eq[-2], S.Complexes)

    Eq.A_lower = Bool.Imp.of.AllSetOf.apply(Eq[-3])

    Eq.L_lower = Algebra.All.of.Cond.All.push.apply(Eq[-1], Eq[-2])

    Eq << Algebra.All.of.All.limits.domain_defined.apply(Eq[-3])

    Eq.L_is_zero = Bool.Imp.of.Cond_Ite.apply(Eq[2], -1)

    Eq << Eq.L_is_zero.this.rhs.apply(Set.In.Finset.of.Eq)

    Eq << Eq[-1].this.rhs.apply(Set.In_Union.of.In, S.Complexes)

    Eq << Bool.All.of.Imp.apply(Eq[-1], j)

    Eq << Bool.AllOr.of.All.All.apply(Eq[-1], Eq.L_lower)

    Eq << Eq[-1].this(i).find(Union).simplify()

    Eq << Set.In.CartesianSpace.of.In.apply(Eq[-1], (j, 0, n), (i, 0, n), simplify=None)

    Eq << Eq[4].rhs.this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS, var=i)

    Eq << Eq[-1].this.find(Sum).apply(Tensor.Sum.eq.Dot, simplify=1)

    Eq << Algebra.EqConj.of.Eq.apply(Eq[0][i, j])

    k = Symbol(integer=True)
    Eq << Eq.A_lower.subs(i, k).subs(j, i).subs(k, j)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.rhs.apply(Algebra.EqConj.of.Eq)

    Eq << Bool.All.of.Imp.apply(Eq[-1])

    Eq << Algebra.All.of.All.limits.domain_defined.apply(Eq[-1])

    Eq.A_ij = Equal(A[i, j], Piecewise(
        (Eq.A_lower.rhs.rhs, j < i),
        (Eq[-1].expr.rhs, j > i),
        (Eq.A_diagonal.rhs, True)), plausible=True)

    Eq.lt_infer, Eq.gt_infer, Eq.eq_infer = Bool.Cond_Ite.given.And.Imp.apply(Eq.A_ij)

    Eq << Bool.Imp.given.All.apply(Eq.lt_infer)

    Eq << Bool.Imp.given.All.apply(Eq.gt_infer, i)

    Eq << Bool.Imp.given.ImpEq.apply(Eq.eq_infer)

    Eq << Bool.Imp.given.Cond.apply(Eq[-1])

    Eq <<= Algebra.All.given.All.limits.domain_defined.apply(Eq[-3]), Algebra.All.given.All.limits.domain_defined.apply(Eq[-2])

    Eq << Eq.A_ij.this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not, 0)

    Eq << Imply(Equal(j, i), Equal(Eq[-1].rhs.args[1].expr, Eq[-1].rhs.args[2].expr), plausible=True)

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.lhs.apply(Tensor.Square.Norm.eq.Dot.Conj, swap=True)

    Eq << Bool.EqIteS.of.Imp_Eq.apply(Eq[-2], Eq[-3].rhs)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-4], Eq[-1])

    Eq << Eq[-1].this.find(Conjugate @ Sliced).T

    Eq << Bool.Imp.of.Cond_Ite.apply(Eq[-1], 1)

    Eq <<= Bool.Imp.And.of.Imp.apply(Eq.lt_infer), Bool.Imp.And.of.Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.find(Less).apply(Algebra.EqMin.of.Lt, reverse=True), Eq[-1].this.rhs.find(GreaterEqual).apply(Algebra.EqMin.of.Ge, reverse=True)

    Eq <<= Eq[-2].this.rhs.args[0] + 1, Eq[-1].this.rhs.args[0] + 1

    Eq <<= Eq[-2].this.rhs.apply(Bool.UFn.of.UFn.Eq, swap=True), Eq[-1].this.rhs.apply(Bool.UFn.of.UFn.Eq, swap=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Tensor.EqDot.of.Imp_Eq_0.apply(Eq.L_is_zero)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, 0, n), (i, 0, n))





if __name__ == '__main__':
    run()
# created on 2023-05-01
# updated on 2023-06-28
