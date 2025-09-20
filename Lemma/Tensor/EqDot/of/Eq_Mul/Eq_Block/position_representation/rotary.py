from util import *


from Lemma.Tensor.EqDot.of.Eq_Mul.position_representation import rotary_matrix, extract
@apply
def apply(eq_theta, eq_R, t):
    Rk, d, alpha, θ, b, k, *_ = extract(eq_theta, eq_R)
    return Equal(Rk.subs(k, t).T @ Rk, Rk.subs(k, k - t))

@prove
def prove(Eq):
    from Lemma import Tensor

    # n denotes sequence length (seq_length)
    # b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    # k, t denote token index
    # i denotes row index
    i, k, t = Symbol(integer=True)
    # λ denotes scaling factor
    λ = Symbol(real=True)
    Eq << apply(*rotary_matrix(R, θ, d, b, k, i, λ), t)

    Eq << Tensor.EqDot.of.Eq_Mul.position_representation.apply(Eq[0], t)

    Eq << Eq[1].reversed

    Eq <<= Eq[-1].subs(k, t).T, Eq[-1].subs(k, k - t)

    Eq << Eq[-4].subs(*Eq[-3:])





if __name__ == '__main__':
    run()
# created on 2023-06-08
# updated on 2023-09-16
