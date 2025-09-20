from util import *


@apply
def apply(eq_relu, eq_min, eq_K_quote, eq_V_quote, eq_K, eq_V, Q, K, V):
    ((i, l), i_limit), β = eq_relu.of(Equal[Stack[relu[Expr + 1 - Expr]]])
    S[i], S[0], n = i_limit

    ((S[n], (S[i], u)), S[i_limit]), ζ = eq_min.of(Equal[Stack[Min[Add]]])

    ((w_K, clip_index), j_limit, S[i_limit]), K_dquote = eq_K.of(Equal[Stack[Indexed]])
    ((w_V, S[clip_index]), S[j_limit], S[i_limit]), V_dquote = eq_V.of(Equal[Stack[Indexed]])
    j, S[0], S[Min(n, l + u - 1)] = j_limit
    k, (S[j - i + β[i]], S[-k], S[k]) = clip_index.of(Add[clip])

    S[n], d_z = Q.shape

    indices = slice(β[i], ζ[i])
    indices0 = slice(0, ζ[i] - β[i])

    ((S[w_K], clip_index), j_limit, S[i_limit]), K_quote = eq_K_quote.of(Equal[Stack[Indexed]])
    ((S[w_V], S[clip_index]), S[j_limit], S[i_limit]), V_quote = eq_V_quote.of(Equal[Stack[Indexed]])
    S[k], (S[j - i], S[-k], S[k]) = clip_index.of(Add[clip])
    S[j], S[0], S[n] = j_limit

    return Equal(softmax(Q @ (K + K_quote).T / sqrt(d_z) + (BandPart[l - 1, u - 1](Ones(n, n)) - 1) * oo) @ (V + V_quote),
                 Stack[i:n](softmax(Q[i] @ (K[indices] + K_dquote[i][indices0]).T / sqrt(d_z)) @ (V[indices] + V_dquote[i][indices0])))



@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Logic

    n, k, l, u = Symbol(integer=True, positive=True)
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
        Equal(K_quote, Stack[j:n, i:n](w_K[k + clip(j - i, -k, k)])),
        Equal(V_quote, Stack[j:n, i:n](w_V[k + clip(j - i, -k, k)])),
        Equal(K_dquote, Stack[j:Min(n, l + u - 1), i:n](w_K[k + clip(j - i + β[i], -k, k)])),
        Equal(V_dquote, Stack[j:Min(n, l + u - 1), i:n](w_V[k + clip(j - i + β[i], -k, k)])),
        Q, K, V)

    K_dquote = Symbol('K^\"', Transpose[0, 1](Stack[j:Min(n, l + u - 1)](K_quote[:, Min(n - 1, j + β[i])])))
    V_dquote = Symbol('V^\"', Transpose[0, 1](Stack[j:Min(n, l + u - 1)](V_quote[:, Min(n - 1, j + β[i])])))
    Eq <<= K_dquote.this.definition, V_dquote.this.definition

    Eq << Tensor.EqSoftmax.of.Eq_Relu.Eq_Min.Eq.Eq.bert.position_representation.relative.band_part_mask.apply(Eq.beta, Eq.zeta, Eq[-2], Eq[-1], Q, K, V)

    Eq <<= Eq[0][i], Eq[1][i]

    Eq.le_min = Tensor.Le.of.Eq_Relu.Eq_Min.apply(Eq.beta, Eq.zeta)

    Eq <<= Algebra.EqSlice.of.Le.Eq.apply(Eq.le_min, Eq[-2]), Algebra.EqSlice.of.Le.Eq.apply(Eq.le_min, Eq[-1])

    Eq <<= Eq[-2].this.find(Symbol + Indexed).apply(Algebra.Expr.eq.IteGe, upper=ζ[i] - 1), Eq[-1].this.find(Symbol + Indexed).apply(Algebra.Expr.eq.IteGe, upper=ζ[i] - 1)

    Eq <<= Eq[-2].this.rhs().find(GreaterEqual).simplify(), Eq[-1].this.rhs().find(GreaterEqual).simplify()

    Eq <<= Eq[-2].this.find(Symbol - 1).apply(Algebra.Expr.eq.IteGe, lower=ζ[i] - 1), Eq[-1].this.find(Symbol - 1).apply(Algebra.Expr.eq.IteGe, lower=ζ[i] - 1)

    Eq.le_zeta = Algebra.Le.of.Eq.relax.apply(Eq.zeta[i], upper=n)

    Eq <<= Logic.BFn.of.BFnIte.Cond.apply(Eq.le_zeta, Eq[-2]), Logic.BFn.of.BFnIte.Cond.apply(Eq.le_zeta, Eq[-1])

    Eq <<= Eq[-2].this.rhs().find(Min).simplify(), Eq[-1].this.rhs().find(Min).simplify()

    Eq <<= Algebra.EqSlice.of.Le.Eq.apply(Eq.le_zeta, Eq.K_quote[i], start=β[i]), Algebra.EqSlice.of.Le.Eq.apply(Eq.le_zeta, Eq.V_quote[i], start=β[i])

    Eq <<= Logic.Eq.of.Eq.Eq.apply(Eq[-4], Eq[-2]), Logic.Eq.of.Eq.Eq.apply(Eq[-3], Eq[-1])

    Eq <<= Algebra.EqSlice.of.Le.Eq.apply(Eq.le_min, Eq.K_dquote[i]), Algebra.EqSlice.of.Le.Eq.apply(Eq.le_min, Eq.V_dquote[i])

    Eq <<= Logic.Eq.of.Eq.Eq.apply(Eq[-4], Eq[-2]), Logic.Eq.of.Eq.Eq.apply(Eq[-3], Eq[-1])

    Eq << Eq[2].subs(Eq[-2], Eq[-1])





if __name__ == '__main__':
    run()

# created on 2020-12-30
# updated on 2023-05-20
