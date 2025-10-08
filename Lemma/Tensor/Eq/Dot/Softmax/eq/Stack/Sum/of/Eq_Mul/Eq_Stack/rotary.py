from util import *


@apply
def apply(eq_theta, eq_R, Q, K, V):
    from Lemma.Tensor.Dot.eq.Stack.of.Eq_Stack.position_representation.rotary import extract
    (Ri, d), b, (i, j, k) = extract(eq_R)
    (S[k], (S[b], ((S[i], (S[i], S[0], S[d / 2])), S[d]))), (θ, S[k]) = eq_theta.of(Equal[Symbol * Symbol ** (-2 * Stack / Symbol), Indexed])
    n = Q.shape[0]
    return Equal(
        Softmax((Stack[i:n](Ri @ Q[i]) @ Stack[i:n](Ri @ K[i]).T) / sqrt(d)) @ V,
        Stack[j:d, i:n](Sum[k:n](V[k, j] * Exp(S[K[k, ::2] * Q[i, ::2] + K[k, 1::2] * Q[i, 1::2], K[k, ::2] * Q[i, 1::2] - Q[i, ::2] * K[k, 1::2]] @ [cos(θ[k - i]), sin(θ[k - i])] / sqrt(d))) / ReducedSum(Exp((Q[i] @ Ri.T @ Stack[i:n](Ri @ K[i]).T) / sqrt(d)))))

@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Discrete, Bool
    from Lemma.Tensor.Dot.eq.Stack.of.Eq_Stack.position_representation.rotary import rotary_matrix
    # n denotes sequence length (seq_length)
    # b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # i denotes token index
    # j denotes row index
    # k denotes column index
    i, j, k = Symbol(integer=True)
    Q, K, V = Symbol(shape=(n, d), real=True)
    # R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    T = Symbol(shape=(n, n), real=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    Eq << apply(
        Equal(θ[k], k / b ** (Stack[i:d / 2](i) * 2 / d)),
        Equal(R(i), rotary_matrix(d, b, i, j, k)),
        Q, K, V)

    Eq << Eq[-1].lhs.this.apply(Tensor.Dot.Softmax.eq.Stack.Sum.scaled_dot_product_attention, i, j, k)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.domain_defined, simplify=None)

    Eq << Tensor.EqDot.of.Eq_Stack.position_representation.rotary.apply(Eq[1]).subs(j, k)

    Eq.final = Eq[-2].subs(Eq[-1])

    Eq << Tensor.Dot.eq.Stack.of.Eq_Stack.position_representation.rotary.apply(Eq[1], K[k])

    Eq << Eq[-1].subs(i, k - i)

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], Q[i])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.halve)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.halve)

    Eq << Eq[-1].this.rhs.apply(Algebra.AddSumS.eq.Sum_Add_Sum)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.expr.args[1:3].apply(Algebra.AddMulS.eq.Mul_Add)

    Eq.matmul_QRK = Eq[-1].this.rhs.expr.args[1:].apply(Algebra.AddMulS.eq.Mul_Add)

    Eq << Eq[2].find(BlockMatrix @ BlockMatrix).this.apply(Tensor.Dot.eq.Block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].subs(Eq[0].subs(k, k - i)[j])

    Eq << Eq[-1].this.rhs.apply(Algebra.AddSumS.eq.Sum_Add_Sum)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[-1], Eq.matmul_QRK)

    Eq << Eq.final.subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()
# created on 2023-05-30
# updated on 2023-09-16
