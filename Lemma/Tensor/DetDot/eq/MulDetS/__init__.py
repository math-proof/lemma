from util import *


@apply
def apply(self):
    A, B = self.of(Determinant[Expr @ Expr])

    return Equal(self, Det(A) * Det(B))


@prove
def prove(Eq):
    from Lemma import Tensor, Nat

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(shape=(n, n), complex=True)
    Eq << apply(Determinant(A @ B))

    Eq << (BlockMatrix([[A, Zeros(n, n)], [Identity(n), B]]) @ BlockMatrix([[Identity(n), -B], [Zeros(n, n), Identity(n)]])).this.apply(Tensor.DotAppendSHstackS.eq.AppendHstackSAddSDotS, deep=True)

    Eq << Tensor.Det.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Tensor.DetDot_AppendHstackS.eq.Det)

    Eq << Eq[-1].this.lhs.apply(Tensor.DetAppendHstackS.eq.MulPowNeg1Mul)

    Eq << Eq[-1].this.rhs.apply(Tensor.DetAppendHstackS.eq.MulPowNeg1Mul)

    Eq << Eq[-1].this.rhs.find(Det).apply(Tensor.DetMul.eq.MulPow)

    Eq << Eq[-1].this.find(Pow).apply(Nat.PowNeg1Mul_Add_1.eq.One)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2020-08-20
# updated on 2021-12-13

from . import trois
