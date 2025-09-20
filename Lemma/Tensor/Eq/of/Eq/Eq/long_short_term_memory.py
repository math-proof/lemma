from util import *


@apply
def apply(eq_h, eq_c):
    (x, *limits), h = eq_h.of(Equal[LSTM])
    [W], [Wh], [b] = limits
    S[(x, *limits)], c = eq_c.of(Equal[LSTMCell])
    
    t = Symbol(integer=True, positive=True)

    d_h = h.shape[-1]

    W_i = W[:,:d_h]
    W_f = W[:, d_h:2 * d_h]
    W_c = W[:, 2 * d_h:3 * d_h]
    W_o = W[:, -d_h:]

    W_hi = Wh[:,:d_h]
    W_hf = Wh[:, d_h:2 * d_h]
    W_hc = Wh[:, 2 * d_h:3 * d_h]
    W_ho = Wh[:, -d_h:]

    b_i = b[:d_h]
    b_f = b[d_h:2 * d_h]
    b_c = b[2 * d_h:3 * d_h]
    b_o = b[-d_h:]
#     i, f, c, o = Symbol(shape=(oo, d_h), real=True)
    i_t = Symbol(sigmoid(x[t] @ W_i + h[t - 1] @ W_hi + b_i))
    f_t = Symbol(sigmoid(x[t] @ W_f + h[t - 1] @ W_hf + b_f))
    c_t = Symbol(f_t * c[t - 1] + i_t * tanh(x[t] @ W_c + h[t - 1] @ W_hc + b_c))
    o_t = Symbol(sigmoid(x[t] @ W_o + h[t - 1] @ W_ho + b_o))

    return Equal(h[t], o_t * tanh(c_t))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    d_x = Symbol(integer=True, positive=True)
    d_h = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n, d_x))
    W = Symbol(real=True, shape=(d_x, 4 * d_h))
    Wh = Symbol("W^h", real=True, shape=(d_h, 4 * d_h))
    b = Symbol(real=True, shape=(4 * d_h,))
    h, c = Symbol(shape=(n, d_h), real=True)
    Eq << apply(
        Equal(h, LSTM[W, Wh, b](x)),
        Equal(c, LSTMCell[W, Wh, b](x)),
        )

    t = Eq[-1].lhs.index
    Eq << Eq[0].this.rhs.defun()

    Eq <<= Eq[-1][t - 1], Eq[-1][t]

    Eq << Eq[-1].this.rhs.defun()

    Eq << Eq[-1].subs(Eq[-3].reversed)

    Eq << Eq[1].this.rhs.defun()[t - 1]

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].subs(*(Eq[i].reversed for i in range(2, 6)))

    # https://www.mitpressjournals.org/doi/pdf/10.1162/089976600300015015    



if __name__ == '__main__':
    run()
# created on 2021-09-04
# updated on 2022-02-20
