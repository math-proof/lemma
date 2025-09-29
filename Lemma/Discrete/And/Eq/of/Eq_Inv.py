from util import *


@apply
def apply(eq):
    ((Λ_x, Λ_xy), (S[Λ_xy.T], Λ_y)), ((Σ_x, Σ_xy), (S[Σ_xy.T], Σ_y)) = eq.of(Equal[BlockMatrix[BlockMatrix[1], BlockMatrix[1]], MatPow[BlockMatrix[BlockMatrix[1], BlockMatrix[1]], -1]])
    assert Σ_x.is_invertible and Σ_y.is_invertible
    return Equal(Λ_x, (Σ_x - Σ_xy @ (Σ_y ^ -1) @ Σ_xy.T) ^ -1), \
        Equal(Λ_y, (Σ_y - Σ_xy.T @ (Σ_x ^ -1) @ Σ_xy) ^ -1), \
        Equal(Λ_xy, -Λ_x @ Σ_xy @ (Σ_y ^ -1)), \
        Equal(Λ_xy.T, -Λ_y @ Σ_xy.T @ (Σ_x ^ -1))

@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    m, n = Symbol(integer=True, positive=True)
    Σ_x = Symbol(shape=(n, n), real=True, singular=False)
    Λ_x = Symbol(shape=(n, n), real=True)
    Σ_y = Symbol(shape=(m, m), real=True, singular=False)
    Λ_y = Symbol(shape=(m, m), real=True)
    Σ_xy, Λ_xy = Symbol(shape=(n, m), real=True)
    Eq << apply(Equal(BlockMatrix([[Λ_x, Λ_xy], [Λ_xy.T, Λ_y]]), Inverse(BlockMatrix([[Σ_x, Σ_xy], [Σ_xy.T, Σ_y]]))))

    Eq << Eq[0].reversed

    Eq << Tensor.EqDot.of.Eq.apply(Eq[-1], Eq[-1].lhs.find(BlockMatrix)).reversed

    Eq << Eq[-1].this.rhs.apply(Algebra.Expr.eq.Block, n, n)

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Block, deep=True)

    Eq << Tensor.EqSliceS.Eq.of.Eq.apply(Eq[-1], n)

    Eq <<= Algebra.EqTranspose.of.Eq.apply(Eq[-2]), Algebra.EqTranspose.of.Eq.apply(Eq[-1])

    Eq <<= Tensor.EqSliceS.Eq.of.Eq.apply(Eq[-2], n), Tensor.EqSliceS.Eq.of.Eq.apply(Eq[-1], n)

    Eq.eq_identity_x = Eq[-4].T

    Eq.is_zero_xy = Eq[-3].T

    Eq.is_zero_yx = Eq[-2].T

    Eq.eq_identity_y = Eq[-1].T

    Eq <<= Algebra.Eq.of.Eq.transport.apply(Eq.is_zero_xy, 0), Algebra.Eq.of.Eq.transport.apply(Eq.is_zero_yx, 0)

    Eq << Eq[-2] @ (Σ_y ^ -1)

    Eq << Eq[-1] @ (Σ_x ^ -1)

    Eq <<= Eq.eq_identity_x.subs(Eq[3]), Eq.eq_identity_y.subs(Eq[4])

    Eq <<= Eq[-2].this.lhs.apply(Tensor.Add.eq.Dot), Eq[-1].this.lhs.apply(Tensor.Add.eq.Dot)

    Eq <<= Tensor.EqInv.of.Eq_Dot.apply(Eq[-2]), Tensor.EqInv.of.Eq_Dot.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-04-28
# updated on 2023-04-30
