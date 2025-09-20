from util import *


@apply
def apply(eq_K_quote, eq_V_quote, Q, K, V, k):
    n, d_z = Q.shape

    ((w_K, clip_index), j_limit, i_limit), K_quote = eq_K_quote.of(Equal[Stack[Indexed]])
    ((w_V, S[clip_index]), S[j_limit], S[i_limit]), V_quote = eq_V_quote.of(Equal[Stack[Indexed]])

    i, S[0], S[n] = i_limit
    j, S[0], S[n] = j_limit

    l, (S[j - i], S[-l], S[l]) = clip_index.of(Add[clip])

    return Equal(softmax(Q @ (K + K_quote).T / sqrt(d_z)) @ (V + V_quote),
                 Stack[j:d_z, i:n](Sum[k]((V[k, j] + V_quote[i, k, j]) * Exp((Q[i] @ (K[k] + K_quote[i, k])) / sqrt(d_z))) / ReducedSum(Exp((Q[i] @ (K.T + K_quote[i].T)) / sqrt(d_z)))))



@prove
def prove(Eq):
    from Lemma import Tensor

    n, l = Symbol(integer=True, positive=True)
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    V = Symbol(shape=(n, d_z), real=True)
    w_K = Symbol("w^K", shape=(2 * l + 1, d_z), real=True)
    w_V = Symbol("w^V", shape=(2 * l + 1, d_z), real=True)
    i, j, k = Symbol(integer=True)
    K_quote = Symbol(real=True, shape=(n, n, d_z))
    V_quote = Symbol(real=True, shape=(n, n, d_z))
    (Eq.K_quote, Eq.V_quote), Eq.objective = apply(
        Equal(K_quote, Stack[j:n, i:n](w_K[l + clip(j - i, -l, l)])),
        Equal(V_quote, Stack[j:n, i:n](w_V[l + clip(j - i, -l, l)])),
        Q, K, V, k)

    Eq << Tensor.EqSoftmax.of.Eq_Clip.Eq_Clip.bert.position_representation.relative.apply(Eq.K_quote, Eq.V_quote, Q, K, V)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.Softmax.eq.Stack.Sum.scaled_dot_product_attention, j, k, simplify=1)

    # reference:
    # Self-Attention with Relative Position Representations.pdf
    # https://arxiv.org/abs/1803.02155



if __name__ == '__main__':
    run()
# created on 2023-05-22
