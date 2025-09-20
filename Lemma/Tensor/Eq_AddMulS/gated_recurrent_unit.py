from util import *


@apply
def apply(x, Wx, Wh, b):
    h = Symbol(GRU[Wx, Wh, b](x))
    t = Symbol(integer=True, positive=True)

    d = h[t - 1].shape[-1]
    W_xz = Symbol(Wx[:,:d])
    W_xr = Symbol(Wx[:, d:2 * d])
    W_xh = Symbol(Wx[:, -d:])

    W_hz = Symbol(Wh[:,:d])
    W_hr = Symbol(Wh[:, d:2 * d])
    W_hh = Symbol(Wh[:, -d:])

    b_z = Symbol(b[:d])
    b_r = Symbol(b[d:2 * d])
    b_h = Symbol(b[-d:])

    z_t = Symbol(sigmoid(x[t] @ W_xz + h[t - 1] @ W_hz + b_z))
    r_t = Symbol(sigmoid(x[t] @ W_xr + h[t - 1] @ W_hr + b_r))
    gh = Symbol(r"\tilde{h}_t", tanh(x[t] @ W_xh + (r_t * h[t - 1]) @ W_hh + b_h))

    return Equal(h[t], (1 - z_t) * gh + z_t * h[t - 1])


@prove
def prove(Eq):
    m, n = Symbol(integer=True, positive=True)

    d_x = Symbol(integer=True, positive=True)
    d_h = Symbol(integer=True, positive=True)

    x = Symbol(real=True, shape=(n, d_x))
    Wx = Symbol("W^x", real=True, shape=(d_x, 3 * d_h))
    Wh = Symbol("W^h", real=True, shape=(d_h, 3 * d_h))
    b = Symbol(real=True, shape=(3 * d_h,))

    Eq << apply(x, Wx, Wh, b)

    t = Eq[-1].lhs.index

    Eq << Eq[0].this.rhs.defun()

    Eq <<= Eq[-1][t - 1], Eq[-1][t]

    Eq << Eq[-1].this.rhs.defun()

    Eq << Eq[-1].subs(Eq[-3].reversed)

    Eq << Eq[-1].subs(*(Eq[i].reversed for i in range(1, 13)))
    # https://arxiv.org/abs/1412.3555v1

if __name__ == '__main__':
    run()
# created on 2021-09-12
