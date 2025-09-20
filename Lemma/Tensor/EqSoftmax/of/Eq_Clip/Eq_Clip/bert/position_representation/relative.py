from util import *


@apply
def apply(eq_K_quote, eq_V_quote, Q, K, V):
    n, d_z = Q.shape

    ((w_K, clip_index), j_limit, i_limit), K_quote = eq_K_quote.of(Equal[Stack[Indexed]])
    ((w_V, S[clip_index]), S[j_limit], S[i_limit]), V_quote = eq_V_quote.of(Equal[Stack[Indexed]])

    i, S[0], S[n] = i_limit
    j, S[0], S[n] = j_limit

    k, (S[j - i], S[-k], S[k]) = clip_index.of(Add[clip])

    return Equal(softmax(Q @ (K + K_quote).T / sqrt(d_z)) @ (V + V_quote),
                 Stack[i:n](softmax(Q[i] @ (K + K_quote[i]).T / sqrt(d_z)) @ (V + V_quote[i])))



@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Logic

    n, k = Symbol(integer=True, positive=True)
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    V = Symbol(shape=(n, d_z), real=True)
    w_K = Symbol("w^K", shape=(2 * k + 1, d_z), real=True)
    w_V = Symbol("w^V", shape=(2 * k + 1, d_z), real=True)
    i, j = Symbol(integer=True)
    K_quote = Symbol(real=True, shape=(n, n, d_z))
    V_quote = Symbol(real=True, shape=(n, n, d_z))
    (Eq.K_quote, Eq.V_quote), Eq.objective = apply(
        Equal(K_quote, Stack[j:n, i:n](w_K[k + clip(j - i, -k, k)])),
        Equal(V_quote, Stack[j:n, i:n](w_V[k + clip(j - i, -k, k)])),
        Q, K, V)

    z = Symbol(Eq.objective.lhs)
    Eq << z.this.definition

    Eq << Eq[-1][i]

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (i, 0, n))

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-3], Eq[-1])

    # reference:
    # Self-Attention with Relative Position Representations.pdf
    # https://arxiv.org/abs/1803.02155



if __name__ == '__main__':
    run()
# created on 2021-01-03
# updated on 2022-02-19
