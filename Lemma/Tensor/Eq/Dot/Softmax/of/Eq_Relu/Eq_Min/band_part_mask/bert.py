from util import *


@apply
def apply(eq_relu, eq_min, Q, K, V):
    ((_i, l), limit_i), β = eq_relu.of(Equal[Stack[relu[Expr - Expr]]])
    i, S[0], n = limit_i
    l -= _i - 1 - i

    ((S[n], iu), S[limit_i]), ζ = eq_min.of(Equal[Stack[Min]])
    u = iu - i

    S[n], d_z = Q.shape

    indices = slice(β[i], ζ[i])
    return Equal(softmax(Q @ K.T / sqrt(d_z) + (BandPart[l - 1, u - 1](Ones(n, n)) - 1) * oo) @ V, Stack[i:n](softmax(Q[i] @ (K[indices]).T / sqrt(d_z)) @ (V[indices])))


@prove
def prove(Eq):
    from Lemma import Tensor

    n, l, u, d_z = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Q = Symbol(real=True, shape=(n, d_z))
    K = Symbol(real=True, shape=(n, d_z))
    V = Symbol(real=True, shape=(n, d_z))
    β, ζ = Symbol(integer=True, shape=(n,))
    (Eq.beta, Eq.zeta), Eq.objective = apply(Equal(β, Stack[i:n](relu(i - l + 1))), Equal(ζ, Stack[i:n](Min(i + u, n))), Q, K, V)

    A = Symbol(Eq.objective.find(Mul[MatMul]))
    Eq << Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax.of.Eq_Stack_Relu.Eq_Stack_Min.apply(Eq.beta, Eq.zeta, A, V)

    Eq << Eq[-1].subs(A.this.definition)





if __name__ == '__main__':
    run()
# created on 2022-01-01
# updated on 2022-03-30
