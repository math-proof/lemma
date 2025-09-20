from util import *


@apply
def apply(self):
    (A, B), (C, D) = self.of(Determinant[BlockMatrix[BlockMatrix[1], BlockMatrix[1]]])
    if not A or not D:
        A = B
        D = C
        factor = (-1) ** (B.shape[0] * C.shape[0])
    else:
        assert not B or not C
        factor = 1

    if A.is_Transpose:
        A = A.T

    if D.is_Transpose:
        D = D.T

    return Equal(self, factor * Det(A).doit() * Det(D).doit())


@prove(proved=False)
def prove(Eq):
    from Lemma import Discrete, Tensor

    n, m = Symbol(integer=True, positive=True)
    # A = Symbol(shape=(m, m), complex=True)
    # B = Symbol(shape=(n, n), complex=True)
    # C = Symbol(shape=(m, n), complex=True)
    # Eq << apply(Determinant(BlockMatrix([[A, C],[Zeros(n, m), B]])))
    A = Symbol(shape=(m, m), complex=True)
    B = Symbol(shape=(n, n), complex=True)
    C = Symbol(shape=(m, n), complex=True)
    Eq << apply(Determinant(BlockMatrix([[C, A],[B, Zeros(n, m)]])))

    Eq << (Eq[0].lhs.arg @ BlockMatrix([[Zeros(n, m), Identity(n)],[Identity(m), Zeros(m, n)]])).this.apply(Tensor.Dot.eq.Block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Block)

    Eq << Discrete.EqDet.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Tensor.Det.Dot.eq.Mul.right)

    # Eq << Eq[-1].this.rhs.apply(Discrete.Det_blockMatrix.to.mul)
    Eq << Eq[-1] * (-1) ** (m*n)





if __name__ == '__main__':
    run()

# created on 2020-08-19
# updated on 2021-12-13
