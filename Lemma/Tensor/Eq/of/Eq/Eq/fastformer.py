from util import *


@apply
def apply(eq_K, eq_V, i, j):
    K_quote, ((((Q, w_q), d), S[Q]), K) = eq_K.of(Equal[Symbol, Softmax[MatMul / Symbol ** S.Half] @ Symbol * Symbol])
    V_quote, ((((K_quote, w_k), S[d]), S[K_quote]), V) = eq_V.of(Equal[Symbol, Softmax[MatMul / Symbol ** S.Half] @ Symbol * Symbol])
    return Equal(V_quote[i, j], V[i, j] * Sum[i](K_quote[i, j] * Exp((K_quote[i] @ w_k) / sqrt(d))) / ReducedSum(Exp((K_quote @ w_k) / sqrt(d))))


@prove
def prove(Eq):
    from Lemma import Discrete, Tensor

    n, d = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Q, K, V, K_quote, V_quote = Symbol(shape=(n, d), real=True)
    w_q, w_k = Symbol(shape=(d,), real=True)
    Eq << apply(
        Equal(K_quote, softmax(Q @ w_q / sqrt(d)) @ Q * K),
        Equal(V_quote, softmax(K_quote @ w_k / sqrt(d)) @ K_quote * V), i, j)

    Eq << Eq[1][i, j]

    Eq << Eq[-1].this.find(MatMul).apply(Tensor.Dot.eq.Sum)

    # https://arxiv.org/pdf/2108.09084.pdf
    # pytorch implementation:
    # https://github.com/wuch15/Fastformer/blob/main/Fastformer.ipynb



if __name__ == '__main__':
    run()
# created on 2023-07-10
