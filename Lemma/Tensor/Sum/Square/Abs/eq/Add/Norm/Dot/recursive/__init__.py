from util import *


@apply
def apply(self):
    (ξ, (k, t)), (L, (S[k], S[t + 1]), (S[0], S[k])) = self.of(Norm[BlockMatrix[Sliced, One] @ Conjugate[Sliced]] ** 2)

    return Equal(self, abs(ξ[k]) ** 2 * Norm(L[k, :k]) ** 2 + Norm(BlockMatrix(ξ[k + 1:t],1) @ ~L[k + 1:t + 1, :k]) ** 2 + 2 * Re((BlockMatrix(ξ[k + 1:t],1) @ ~L[k + 1:t + 1, :k] @ L[k, :k]) * ~ξ[k]))

@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Tensor

    t, k = Symbol(integer=True, positive=True)
    L = Symbol(shape=(oo, oo), super_complex=True)
    ξ = Symbol(r'{\color{red} {ξ}}', complex=True, shape=(oo,))
    Eq << apply(Norm(BlockMatrix(ξ[k:t],1) @ ~L[k:t + 1, :k]) ** 2)

    Eq << Eq[0].lhs.this.find(Conjugate[~Sliced]).apply(Algebra.Expr.eq.Block, t - k)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Block)

    Eq.next = Eq[-1].subs(k, k + 1)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Add.shift)

    Eq << Eq[-1].this.rhs.apply(Tensor.Square.Norm.eq.Add.Dot)

    Eq << Eq[-1].this.rhs.find(Norm[Indexed * Conjugate]).apply(Algebra.Norm.eq.Mul.Norm)

    Eq << Eq[-1].this.rhs.args[1:3].apply(Tensor.Add.Square.eq.Sub.Dot)

    Eq << Eq[-1].this.rhs.find(Re[Mul[~MatMul[Adjoint]]]).T

    Eq << Eq[-1].this.rhs.find(Re[MatMul * Conjugate]).apply(Algebra.Re.Conj)

    Eq << Eq[-1].this.rhs.args[-2:].apply(Algebra.Add.eq.Re)

    Eq << Eq[-1].this.rhs.args[-1].apply(Algebra.Re.eq.Mul)

    Eq << Eq[-1].this.rhs.args[-1].find(Add).apply(Tensor.Add.eq.Dot)

    Eq << Eq[-1].this.find(Re).apply(Algebra.Re.Conj)

    Eq << Eq[-1].rhs.find(Add[MatMul]).this.apply(Tensor.Add.eq.Dot.Block)

    Eq << Eq[-1].this.rhs.find(BlockMatrix[Conjugate]).apply(Algebra.Block.eq.Conj)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.find(Norm[Conjugate]).apply(Algebra.Norm.Conj)





if __name__ == '__main__':
    run()
# created on 2023-06-24
# updated on 2023-09-19
from . import real
