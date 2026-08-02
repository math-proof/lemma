from util import *


@apply
def apply(eq_max, eq_min, eq_K_quote, eq_V_quote, eq_K, eq_V, Q, K, V):
    (((i, l), (S[i - l + 1], d)), i_limit), β = eq_max.of(Equal[Stack[Max[Expr + 1 - Expr, Mod]]])
    S[i], S[0], n = i_limit

    ((S[n], (S[i], u)), S[i_limit]), ζ = eq_min.of(Equal[Stack[Min[Add]]])

    ((w_K, clip_index), j_limit, S[i_limit]), K_dquote = eq_K.of(Equal[Stack[Indexed]])
    ((w_V, S[clip_index]), S[j_limit], S[i_limit]), V_dquote = eq_V.of(Equal[Stack[Indexed]])
    j, S[0], S[Min(n, l + u - 1)] = j_limit
    k, (((r, S[Min(j + β[i], n - 1)]), (S[r], S[i])), S[-k], S[k]) = clip_index.of(Add[clip[Indexed - Indexed]])
    S[n], d_z = Q.shape

    indices = slice(β[i], ζ[i], d)
    indices0 = slice(0, ζ[i] - β[i], d)

    ((S[w_K], clip_index), j_limit, S[i_limit]), K_quote = eq_K_quote.of(Equal[Stack[Indexed]])
    ((S[w_V], S[clip_index]), S[j_limit], S[i_limit]), V_quote = eq_V_quote.of(Equal[Stack[Indexed]])
    S[k], (S[r[j] - r[i]], S[-k], S[k]) = clip_index.of(Add[clip])
    S[j], S[0], S[n] = j_limit

    return Equal(softmax(Q @ (K + K_quote).T / sqrt(d_z) + (BandPart[l - 1, u - 1, d](Ones(n, n)) - 1) * oo) @ (V + V_quote), \
                 Stack[i:n](softmax(Q[i] @ (K[indices] + K_dquote[i][indices0]).T / sqrt(d_z)) @ (V[indices] + V_dquote[i][indices0])))



@prove
def prove(Eq):
    from Lemma import Tensor

    n, k, l, u, d = Symbol(integer=True, positive=True)
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
        Equal(β, Stack[i:n](Max(i - l + 1, (i - l + 1) % d))),
        Equal(ζ, Stack[i:n](Min(i + u, n))),
        Equal(K_quote, Stack[j:n, i:n](w_K[k + clip(r[j] - r[i], -k, k)])),
        Equal(V_quote, Stack[j:n, i:n](w_V[k + clip(r[j] - r[i], -k, k)])),
        Equal(K_dquote, Stack[j:Min(n, l + u - 1), i:n](w_K[k + clip(r[Min(n - 1, β[i] + j)] - r[i], -k, k)])),
        Equal(V_dquote, Stack[j:Min(n, l + u - 1), i:n](w_V[k + clip(r[Min(n - 1, β[i] + j)] - r[i], -k, k)])),
        Q, K, V)

    Eq <<= Eq.K_quote[i], Eq.V_quote[i]

    Eq <<= Eq[-2][Min(j + β[i], n - 1)], Eq[-1][Min(j + β[i], n - 1)]

    Eq <<= Eq.K_dquote.subs(Eq[-2].reversed), Eq.V_dquote.subs(Eq[-1].reversed)

    Eq << Tensor.EqSoftmax.of.Eq_Max.Eq_Min.Eq.Eq.bert.position_representation.relative.band_part_mask.dilated.apply(Eq.beta, Eq.zeta, Eq[-2], Eq[-1], Q, K, V)




if __name__ == '__main__':
    run()
# created on 2021-12-27
# updated on 2022-03-30



from . import compact
