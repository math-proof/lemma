from util import *


@apply
def apply(eq):
    ((((Q, KT), d_sqrt), ((_n,), (S[0],))), V), (Z, batch_size, seq_length) = eq.of(Equal[Softmax[Expr @ Expr / Expr + (BandPart[Ones] - 1) * Infinity] @ Expr, Sliced])
    n = V.shape[-2]
    S[0], m = batch_size
    S[0], S[n] = seq_length
    assert _n >= n - 1
    K = KT.T
    Q, S[batch_size], S[seq_length] = Q.of(Sliced)
    K, S[batch_size], S[seq_length] = K.of(Sliced)
    V, S[batch_size], S[seq_length] = V.of(Sliced)

    return Equal(
        Transpose[0, 1](Z[:, :n + 1]),
        [
            Transpose[0, 1](Z[:, :n]),
            Softmax((Q[:, n] @ Transpose[0, 2]([
                Transpose[0,1](K[:, :n]),
                K[:, n]
                ])) / d_sqrt) @ Transpose[0, 1]([
                    Transpose[0, 1](V[:, :n]),
                    V[:, n]
                ])
        ])


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra

    m, n, d_z = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Z, Q, K, V = Symbol(shape=(m, oo, d_z), real=True)
    Eq << apply(
        Equal(Z[:, :n], softmax(Q[:, :n] @ K[:, :n].T / sqrt(d_z) + (BandPart[n, 0](Ones(n, n)) - 1) * oo) @ V[:, :n]))

    Eq << Eq[0].this.rhs.apply(Tensor.Dot.Softmax.eq.Stack.Dot.gpt.batched, i)

    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Block.pop)

    Eq << Algebra.EqTranspose.of.Eq.apply(Eq[2], axis=(0, 1))

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Algebra.EqTranspose.of.Eq.apply(Eq[-1], axis=(0, 1))
    Eq << Eq[-1].this.find(MatMul[Transpose[~Sliced]]).apply(Algebra.Expr.eq.Block, -1, axis=1)

    Eq << Eq[-1].this.find(MatMul[~Sliced]).apply(Algebra.Expr.eq.Block, -1, axis=1)




if __name__ == '__main__':
    run()
# created on 2024-02-29
# updated on 2024-03-02
