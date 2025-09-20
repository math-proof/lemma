from util import *


@apply
def apply(eq_a, eq_b, eq_a_t, eq_b_t, eq_r, eq_k, eq_v, eq_o, i=None):
    a = eq_a.of(Equal[Indexed[Symbol, 0], 0])
    b = eq_b.of(Equal[Indexed[Symbol, 0], 0])
    (S[b], t), ((S[b[t - 1]], w), (K, S[t])) = eq_b_t.of(Equal[Indexed, Expr * Exp[-Symbol] + Exp[Indexed]])
    (S[a[t - 1] * Exp(-w)], ((V, S[t]), (S[K], S[t]))), S[a[t]] = eq_a_t.of(Equal[Expr + Indexed * Exp[Indexed]])
    (R, S[t]), (W_r, ((μ_r, (x, S[t])), (S[x[t - 1]], S[μ_r]))) = eq_r.of(Equal[Indexed, Symbol @ (Symbol * Indexed + Expr * (1 - Symbol))])
    (K, S[t]), (W_k, ((μ_k, S[x[t]]), (S[x[t - 1]], S[μ_k]))) = eq_k.of(Equal[Indexed, Symbol @ (Symbol * Expr + Expr * (1 - Symbol))])
    (V, S[t]), (W_v, ((μ_v, S[x[t]]), (S[x[t - 1]], S[μ_v]))) = eq_v.of(Equal[Indexed, Symbol @ (Symbol * Expr + Expr * (1 - Symbol))])
    (O, S[t]), (W_o, (((S[V[t]], (u, S[K[t]])), S[a[t]]), S[R[t]], ((S[u], S[K[t]]), S[b[t]]))) = eq_o.of(Equal[Indexed, Symbol @ ((Expr * Exp[Symbol + Expr] + Expr) * sigmoid / (Exp[Symbol + Expr] + Expr))])
    return Equal(O[t], W_o @ ((V[t] * Exp(u + K[t]) + Sum[i:t](V[i] * Exp(K[i] + w * (i - t + 1)))) * sigmoid(R[t]) / (Exp(u + K[t]) + Sum[i:t](Exp(K[i] + w * (i - t + 1))))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    # T is the sequence length
    # d is the embedding size
    T, d = Symbol(integer=True, positive=True)
    # x is the sequence
    x = Symbol(real=True, shape=(T, d))
    # model weights:
    W_r = Symbol("W^r", real=True, shape=(d, d))
    W_k = Symbol("W^k", real=True, shape=(d, d))
    W_v = Symbol("W^v", real=True, shape=(d, d))
    W_o = Symbol("W^o", real=True, shape=(d, d))
    μ_r, μ_k, μ_v, u, w = Symbol(real=True, shape=(d,))
    # w is the positional weight decay vector. A trainable model parameter
    R, K, V, O = Symbol(real=True, shape=(T, d))
    a, b = Symbol(real=True, shape=(T, d))
    i, t = Symbol(integer=True)
    Eq << apply(
        Equal(a[0], Zeros(d)),
        Equal(b[0], Zeros(d)),
        Equal(a[t], exp(-w) * a[t - 1] + exp(K[t]) * V[t]),
        Equal(b[t], exp(-w) * b[t - 1] + exp(K[t])),
        Equal(R[t], W_r @ (μ_r * x[t] + (1 - μ_r) * x[t - 1])),
        Equal(K[t], W_k @ (μ_k * x[t] + (1 - μ_k) * x[t - 1])),
        Equal(V[t], W_v @ (μ_v * x[t] + (1 - μ_v) * x[t - 1])),
        Equal(O[t], W_o @ (sigmoid(R[t]) *(a[t] + exp(u + K[t]) * V[t]) / (b[t] + exp(u + K[t])))), i)

    Eq <<= Algebra.Eq.of.Eq.rsolve.apply(Eq[2]), Algebra.Eq.of.Eq.rsolve.apply(Eq[3])

    Eq <<= Eq[-2].subs(Eq[0]), Eq[-1].subs(Eq[1])

    Eq <<= Eq[-2].this.find(Exp[~Mul]).apply(Algebra.Mul.Neg), Eq[-1].this.find(Exp[~Mul]).apply(Algebra.Mul.Neg)

    Eq <<= Eq[-2].this.find(Exp * Exp).args[1:].apply(Algebra.Mul.eq.Exp), Eq[-1].this.find(Exp * Exp).apply(Algebra.Mul.eq.Exp)

    Eq << Eq[7].subs(Eq[-2], Eq[-1])

    # https://arxiv.org/pdf/2305.13048.pdf#page=5
    # compared to standard transformer of scaled dot product attention
    # http://localhost/axiom/?module=Tensor.Dot_softmax.to.Lamda.sum.scaled_dot_product_attention




if __name__ == '__main__':
    run()
# created on 2023-06-17
# updated on 2023-06-24
