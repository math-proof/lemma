from util import *


@apply
def apply(eq):
    ((((Q, KT), d_sqrt), ((_n,), (S[0],))), V), (Z, seq_length) = eq.of(Equal[Softmax[Expr @ Expr / Expr + (BandPart[Ones] - 1) * Infinity] @ Expr, Sliced])
    n = V.shape[-2]
    assert _n >= n - 1
    S[0], S[n] = seq_length
    K = KT.T
    Q, S[seq_length] = Q.of(Sliced)
    K, S[seq_length] = K.of(Sliced)
    V, S[seq_length] = V.of(Sliced)
    return Equal(Z[:n + 1], [Z[:n], Softmax((Q[n] @ BlockMatrix[1](K[:n].T, K[n])) / d_sqrt) @ [V[:n], V[n]]])


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra

    n, d_z = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Z, Q, K, V = Symbol(shape=(oo, d_z), real=True)
    Eq << apply(
        Equal(Z[:n], softmax(Q[:n] @ K[:n].T / sqrt(d_z) + (BandPart[n, 0](Ones(n, n)) - 1) * oo) @ V[:n]))

    Eq << Eq[0].this.rhs.apply(Tensor.DotSoftmax.eq.Stack_Dot.gpt, i)

    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.Block.pop)

    Eq << Eq[-1].subs(Eq[2].reversed)

    Eq << Eq[-1].this.find(Transpose[~Sliced]).apply(Algebra.Expr.eq.Block, -1)

    Eq << Eq[-1].this.find(MatMul[~Sliced]).apply(Algebra.Expr.eq.Block, -1)

    # http://myhz0606.com/article/kv-cache


if __name__ == '__main__':
    run()
# created on 2024-02-28
# updated on 2024-02-29

