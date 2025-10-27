from util import *


@apply
def apply(eq_h_embed, eq_h_global_in, eq_h_global_out, eq_h_local_in, eq_h_local_out, eq_prob):
    (h_embed, t), ((E_pos, S[t]), (E_global_embed, xt)) = eq_h_embed.of(Equal[Indexed, Indexed + Indexed])
    x_var, S[t] = xt.of(Indexed)
    T, = x_var.shape

    V, D_G = E_global_embed.shape
    (h_global_in, k), ((E_global_pad, S[Equal(k, 0)]), (h_embed_patched, S[True])) = eq_h_global_in.of(Equal[Indexed, Piecewise])

    P = E_global_pad.shape[-1] / D_G
    (h_embed, index_row, index_col), (i, S[0], S[P * D_G]) = h_embed_patched.of(Stack[Indexed])
    S[i // P + P * k - P] = index_row
    S[i % P] = index_col
    K, S[P * D_G] = h_global_in.shape
    assert K == Ceil(T / P)

    h_global_out, transformer_global_h_global_in = eq_h_global_out.of(Equal)
    S[h_global_in] = transformer_global_h_global_in.of(Function)
    (h_local_in, S[k], p), (((S[h_global_out[k]], (S[p * D_G], S[p * D_G + D_G])), w_GL), ((E_local_pad, S[Equal(p, 0)]), (E_local_embed, S[True]))) = eq_h_local_in.of(Equal[Indexed, Sliced @ Symbol + Piecewise])
    E_local_embed, S[x_var[k * P + p - 1]] = E_local_embed.of(Indexed)
    (h_local_out, S[k]), (S[h_local_in], S[k]) = eq_h_local_out.of(Equal[Indexed, Function[Indexed]])
    ((((x, S[P * k + p]), S[x[P * k + p].var]), S[x[:P * k + p].as_boolean()]), [S[x[P * k + p].var]]), (S[E_local_embed], S[h_local_out[k, p]]) = eq_prob.of(Equal[Stack[Pr[Conditioned[Equal[Indexed]]]], Softmax[MatMul]])
    assert x.var == x_var
    return Equal(h_global_in, BlockMatrix(E_global_pad, Stack[i: P * D_G, k:K - 1](h_embed[P * k: P * k + P][i // P, i % P]))),\
        Equal(h_local_in[k], Stack[p:P](h_global_out[k, p * D_G: p * D_G + D_G]) @ w_GL + BlockMatrix(E_local_pad, Stack[p:P - 1](E_local_embed[x_var[k * P + p]]))),\
        Equal(Pr(x[t] | x[:t]), softmax(E_local_embed @ h_local_out[t // P, t % P])[x.var[t]])


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Nat, Nat, Nat, Int

    # T is the byte sequence length
    # P is the patch size which is normally set to 4
    # V is the size of bytes vocabulary, ie 256;
    # D_G is the global model dimension
    # D_L is the local model dimension
    T, P, V, D_G, D_L = Symbol(integer=True, positive=True)
    # the patch size K is defined as:
    K = Ceil(T / P)
    # t is index iterating from 0 ~ T, notes: t = k * P + p
    # k is index iterating from 0 ~ K
    # p is index iterating from 0 ~ P
    # i is index iterating from 0 ~ P * D_G
    t, i, k, p = Symbol(integer=True)
    # the byte sequence: (integer numbers ranging from 0 ~ 255)
    x = Symbol(domain=Range(V), shape=(T,), random=True)
    # the byte embedding lookup table in global model, which maps a byte to a tensor of shape (D_G,)
    E_global_embed = Symbol("E^global-embed", real=True, shape=(V, D_G))
    # the byte embedding lookup table in local model, which maps a byte to a tensor of shape (D_L,)
    E_local_embed = Symbol("E^local-embed", real=True, shape=(V, D_L))
    # a trainable global patch-sized padding embedding
    E_global_pad = Symbol("E^global-pad", real=True, shape=(P * D_G,))
    # a trainable local padding embedding
    E_local_pad = Symbol("E^local-pad", real=True, shape=(D_L,))
    # the absolute position embedding lookup table which maps a position to a tensor of shape (D_G,)
    E_pos = Symbol("E^pos", real=True, shape=(oo, D_G))
    # the byte embeddings
    h_embed = Symbol("h^embed", real=True, shape=(T, D_G))
    # inputs and outputs of global transformer model
    h_global_in = Symbol("h^global-in", real=True, shape=(K, P * D_G))
    h_global_out = Symbol("h^global-out", real=True, shape=(K, P * D_G))
    # inputs and outputs of local transformer model
    h_local_in = Symbol("h^local-in", real=True, shape=(K, P, D_L))
    h_local_out = Symbol("h^local-out", real=True, shape=(K, P, D_L))
    w_GL = Symbol("w^GL", real=True, shape=(D_G, D_L))
    transformer_global = Function('transformer^{global}', real=True)
    transformer_local = Function('transformer^{local}', real=True)
    *Eq[-6:], (Eq.h_global_in, Eq.h_local_in, Eq.prob) = apply(
        Equal(h_embed[t], E_global_embed[x.var[t]] + E_pos[t]),
        Equal(h_global_in[k], Piecewise((E_global_pad, Equal(k, 0)), (Stack[i:P * D_G](h_embed[k * P - P: k * P][i // P, i % P]), True))),
        Equal(h_global_out, transformer_global(h_global_in)),
        Equal(h_local_in[k, p], h_global_out[k, p * D_G: p * D_G + D_G] @ w_GL + Piecewise((E_local_pad, Equal(p, 0)), (E_local_embed[x.var[k * P + p - 1]], True))),
        Equal(h_local_out[k], transformer_local(h_local_in[k])),
        Equal(Stack[x.var[k * P + p]](Pr(x[k * P + p] | x[:k * P + p])), softmax(E_local_embed @ h_local_out[k, p])),
        )

    l = Symbol(domain=Range(K))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq.h_global_in, l)

    Eq << Eq[-1].this.rhs.apply(Int.Ite.eq.AddMulS)

    Eq << Eq[1].subs(k, l)

    Eq << Eq[-1].this.find(Add).args[:2].apply(Nat.AddMulS.eq.Mul_Add)

    l = Symbol(domain=Range(P))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq.h_local_in, l)

    Eq << Eq[-1].this.find(Piecewise).apply(Int.Ite.eq.AddMulS)

    Eq << Eq[3].subs(p, l)

    Eq << Eq[-1].this.find(Piecewise).apply(Int.Ite.eq.AddMulS)

    Eq << Eq[5][x.var[P * k + p]]

    Eq << Algebra.Expr.eq.Add.Mod.apply(t, P)

    Eq << Eq[-2].subs(k, t // P).subs(p, t % P)

    Eq << Eq[-1].subs(Eq[-2].reversed)
    # https://arxiv.org/pdf/2305.07185.pdf#page=3



if __name__ == '__main__':
    run()
# created on 2023-06-04
