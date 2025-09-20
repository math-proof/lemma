from util import *


@apply
def apply(self):
    (((j, i), (r, S[j])), (S[j], S[0], m), (S[i], S[0], d)), ((S[j], S[i]), (S[j], S[0], S[m]), (S[i], S[0], S[m - d])) = self.of(Det[BlockMatrix[Stack[Pow * Pow], Stack[Pow]]])
    assert m > d
    return Equal(self, r ** Binomial(d, 2) * (1 - r) ** (d * (m - d)) * Product[i:d](factorial(i)) * Product[i:m - d](factorial(i)))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Tensor

    λ = Symbol(real=True)
    d = Symbol(integer=True, positive=True)
    m = Symbol(domain=Range(d + 1, oo))
    i, j = Symbol(integer=True)
    Eq << apply(Det(BlockMatrix([Stack[j:m, i:d](j ** i * λ ** j), Stack[j:m, i:m - d](j ** i)])))

    E = BlockMatrix(Stack[j:d, i:m]((-λ) ** (j - i) * binomial(j, i)).T, Stack[j:m - d, i:m]((-λ) ** (d + j - i) * binomial(d, i - j)).T).T
    Eq << (Eq[0].lhs.arg @ E).this.apply(Tensor.Dot.eq.Block)

    Eq << Eq[-1].this.rhs.find(Mul[Stack]).apply(Tensor.Mul.eq.Stack, simplify=None)

    Eq << Eq[-1].this.rhs.find(Mul[Stack]).apply(Tensor.Mul.eq.Stack, simplify=None)

    Eq << Eq[-1].this.rhs.args[0].args[1].apply(Tensor.Dot.Stack.eq.Zero.vandermonde.col_transformation)

    Eq << Eq[-1].this.find(BlockMatrix[1]).apply(Tensor.Block.eq.Stack.Ite)

    Eq << Eq[-1].this.find(Binomial[Add]).apply(Discrete.Binom.SDiff)

    Eq << Discrete.EqDet.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul.deux)

    Eq << Eq[-1].this.rhs.apply(Discrete.Det.Block.eq.Mul)

    Eq << Eq[-1].this.lhs.args[1].doit(deep=True)

    Eq << Eq[-1].this.find(Det[2]).apply(Tensor.DetDotStackS.eq.Mul_Prod.vandermonde.col_transform)

    Eq << Eq[-1].this.find(Det[MatMul]).apply(Tensor.Det.Dot.Stack.eq.Mul.Prod.vandermonde)





if __name__ == '__main__':
    run()
# created on 2021-11-25
# updated on 2023-05-18
