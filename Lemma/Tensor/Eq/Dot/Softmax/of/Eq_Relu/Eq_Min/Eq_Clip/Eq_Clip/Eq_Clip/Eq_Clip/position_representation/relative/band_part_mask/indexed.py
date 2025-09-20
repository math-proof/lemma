from util import *


@apply
def apply(eq_relu, eq_min, eq_K_quote, eq_V_quote, eq_K, eq_V, Q, K, V):
    ((i, l), i_limit), β = eq_relu.of(Equal[Stack[relu[Expr + 1 - Expr]]])
    S[i], S[0], n = i_limit

    ((S[n], (S[i], u)), S[i_limit]), ζ = eq_min.of(Equal[Stack[Min[Add]]])

    ((w_K, clip_index), j_limit, S[i_limit]), K_dquote = eq_K.of(Equal[Stack[Indexed]])
    ((w_V, S[clip_index]), S[j_limit], S[i_limit]), V_dquote = eq_V.of(Equal[Stack[Indexed]])
    j, S[0], S[Min(n, l + u - 1)] = j_limit
    k, (((r, S[Min(j + β[i], n - 1)]), (S[r], S[i])), S[-k], S[k]) = clip_index.of(Add[clip[Indexed - Indexed]])
    S[n], d_z = Q.shape

    indices = slice(β[i], ζ[i])
    indices0 = slice(0, ζ[i] - β[i])

    ((S[w_K], clip_index), j_limit, S[i_limit]), K_quote = eq_K_quote.of(Equal[Stack[Indexed]])
    ((S[w_V], S[clip_index]), S[j_limit], S[i_limit]), V_quote = eq_V_quote.of(Equal[Stack[Indexed]])
    S[k], (S[r[j] - r[i]], S[-k], S[k]) = clip_index.of(Add[clip])
    S[j], S[0], S[n] = j_limit

    return Equal(softmax(Q @ (K + K_quote).T / sqrt(d_z) + (BandPart[l - 1, u - 1](Ones(n, n)) - 1) * oo) @ (V + V_quote), \
                 Stack[i:n](softmax(Q[i] @ (K[indices] + K_dquote[i][indices0]).T / sqrt(d_z)) @ (V[indices] + V_dquote[i][indices0])))



@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n, k, l, u = Symbol(integer=True, positive=True)
    r = Symbol(shape=(n,), integer=True)
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    V = Symbol(shape=(n, d_z), real=True)
    β, ζ = Symbol(shape=(n,), integer=True)
    w_K = Symbol("w^K", shape=(2 * k + 1, d_z), real=True)
    w_V = Symbol("w^V", shape=(2 * k + 1, d_z), real=True)
    i, j = Symbol(integer=True)
    K_quote = Symbol(real=True, shape=(n, n, d_z))
    V_quote = Symbol(real=True, shape=(n, n, d_z))
    K_dquote = Symbol('K^\"', real=True, shape=(n, Min(n, l + u - 1), d_z))
    V_dquote = Symbol('V^\"', real=True, shape=(n, Min(n, l + u - 1), d_z))
    (Eq.beta, Eq.zeta, Eq.K_quote, Eq.V_quote, Eq.K_dquote, Eq.V_dquote), Eq.objective = apply(
        Equal(β, Stack[i:n](relu(i - l + 1))),
        Equal(ζ, Stack[i:n](Min(i + u, n))),
        Equal(K_quote, Stack[j:n, i:n](w_K[k + clip(r[j] - r[i], -k, k)])),
        Equal(V_quote, Stack[j:n, i:n](w_V[k + clip(r[j] - r[i], -k, k)])),
        Equal(K_dquote, Stack[j:Min(n, l + u - 1), i:n](w_K[k + clip(r[Min(n - 1, β[i] + j)] - r[i], -k, k)])),
        Equal(V_dquote, Stack[j:Min(n, l + u - 1), i:n](w_V[k + clip(r[Min(n - 1, β[i] + j)] - r[i], -k, k)])),
        Q, K, V)

    Eq <<= Eq.K_quote[i], Eq.V_quote[i]

    Eq <<= Eq[-2][Min(j + β[i], n - 1)], Eq[-1][Min(j + β[i], n - 1)]

    Eq <<= Eq.K_dquote.subs(Eq[-2].reversed), Eq.V_dquote.subs(Eq[-1].reversed)

    Eq <<= Eq[-2].this.rhs.apply(Tensor.Stack.eq.Transpose, axis=(0, 1)), Eq[-1].this.rhs.apply(Tensor.Stack.eq.Transpose, axis=(0, 1))

    Eq << Tensor.EqSoftmax.of.Eq_Relu.Eq_Min.Eq.Eq.bert.position_representation.relative.band_part_mask.apply(Eq.beta, Eq.zeta, Eq[-2], Eq[-1], Q, K, V)

    Eq << Eq.K_dquote[i, j - β[i]]





if __name__ == '__main__':
    run()
# created on 2021-12-15
# updated on 2022-03-30
