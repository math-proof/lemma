from util import *


@apply
def apply(self, *indices):
    ((Q, KT), d_z), V = self.of(Softmax[Expr @ Expr / Expr ** S.Half] @ Expr)
    n, S[d_z] = V.shape
    K = KT.T
    if len(Q.shape) == 2:
        S[n], S[d_z] = V.shape
        i, j, k = indices
        return Equal(self, Stack[j:d_z, i:n](Sum[k](V[k, j] * Exp((Q[i] @ K[k]) / sqrt(d_z))) / ReducedSum(Exp((Q[i] @ K.T) / sqrt(d_z)))))

    S[d_z], = Q.shape
    j, k = indices
    return Equal(self, Stack[j:d_z](Sum[k](V[k, j] * Exp((Q @ K[k]) / sqrt(d_z))) / ReducedSum(Exp((Q @ K.T) / sqrt(d_z)))))

@prove
def prove(Eq):
    from Lemma import Tensor, Discrete

    n, d_z = Symbol(integer=True, positive=True)
    i, j, k = Symbol(integer=True)
    Q, K, V = Symbol(shape=(n, d_z), real=True)
    Eq << apply(softmax(Q @ K.T / sqrt(d_z)) @ V, i, j, k)

    Eq << Eq[0].lhs.this.apply(Tensor.Dot.Softmax.eq.Stack.Dot.scaled_dot_product_attention.double_limits, i, j)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Sum, simplify=1)




if __name__ == '__main__':
    run()
# created on 2023-05-22
