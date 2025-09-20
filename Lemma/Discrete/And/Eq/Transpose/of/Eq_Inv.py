from util import *


@apply
def apply(eq):
    ((Λ_x, Λ_xy), (S[Λ_xy.T], Λ_y)), ((Σ_x, Σ_xy), (S[Σ_xy.T], Σ_y)) = eq.of(Equal[BlockMatrix[BlockMatrix[1], BlockMatrix[1]], MatPow[BlockMatrix[BlockMatrix[1], BlockMatrix[1]], -1]])
    assert Σ_x.is_invertible and Σ_y.is_invertible
    return Equal(Λ_x, (Σ_x - Σ_xy @ (Σ_y ^ -1) @ Σ_xy.T) ^ -1), \
        Equal(Λ_y, (Σ_y - Σ_xy.T @ (Σ_x ^ -1) @ Σ_xy) ^ -1), \
        Equal(Λ_xy, -(Σ_x ^ -1) @ Σ_xy @ Λ_y), \
        Equal(Λ_xy.T, -(Σ_y ^ -1) @ Σ_xy.T @ Λ_x)

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

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[0], Eq[0].rhs.find(BlockMatrix))

    Eq << Eq[-1].this.rhs.apply(Algebra.Expr.eq.Block, n, n)

    Eq << Eq[-1].this.lhs.apply(Tensor.Dot.eq.Block, deep=True)

    Eq << Algebra.And.Eq.of.Eq.split.apply(Eq[-1], n)

    Eq <<= Algebra.EqTranspose.of.Eq.apply(Eq[-2]), Algebra.EqTranspose.of.Eq.apply(Eq[-1])

    Eq <<= Algebra.And.Eq.of.Eq.split.apply(Eq[-2], n), Algebra.And.Eq.of.Eq.split.apply(Eq[-1], n)

    Eq.eq_identity_x = Eq[-4].T

    Eq.is_zero_xy = Eq[-3].T

    Eq.is_zero_yx = Eq[-2].T

    Eq.eq_identity_y = Eq[-1].T

    Eq <<= Algebra.Eq.of.Eq.transport.apply(Eq.is_zero_xy, 0), Algebra.Eq.of.Eq.transport.apply(Eq.is_zero_yx, 0)

    Eq << (Σ_x ^ -1) @ -Eq[-2].reversed

    Eq << (Σ_y ^ -1) @ -Eq[-1].reversed

    Eq <<= Eq.eq_identity_x.subs(Eq[4]), Eq.eq_identity_y.subs(Eq[3])

    Eq <<= Eq[-2].this.lhs.apply(Tensor.Add.eq.Dot), Eq[-1].this.lhs.apply(Tensor.Add.eq.Dot)

    Eq <<= Tensor.EqInv.of.Eq_Dot.apply(Eq[-2], left=True), Tensor.EqInv.of.Eq_Dot.apply(Eq[-1], left=True)





if __name__ == '__main__':
    run()
# created on 2023-04-30
# updated on 2023-05-01
