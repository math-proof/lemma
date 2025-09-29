from util import *



@apply
def apply(eq_theta, eq_R, Q, K, V, j):
    from Lemma.Tensor.EqDot.of.Eq_Mul.position_representation import extract
    Rk, d, alpha, θ, b, k, i, *_ = extract(eq_theta, eq_R)
    n = Q.shape[0]
    Ri = Rk.subs(k, i)
    return Equal(
        Softmax((Stack[i:n](Ri @ Q[i]) @ Stack[i:n](Ri @ K[i]).T) / sqrt(d)) @ V,
        Stack[j:d, i:n](Sum[k:n](V[k, j] * Exp((S[K[k, :d / 2] * Q[i, :d / 2] + K[k, d / 2:] * Q[i, d / 2:], (K[k, :d / 2] * Q[i, d / 2:] - Q[i, :d / 2] * K[k, d / 2:])] @ [cos(θ[k - i]), sin(θ[k - i])]) / sqrt(d))) / ReducedSum(Exp((Q[i] @ Ri.T @ Stack[i:n](Ri @ K[i]).T) / sqrt(d)))))

@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Discrete, Logic
    from Lemma.Tensor.EqDot.of.Eq_Mul.position_representation import rotary_matrix
    # n denotes sequence length (seq_length)
    # b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # R denotes rotary matrix
    R = Function(shape=(d, d), real=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    # k, t denote token index
    # i denotes row index
    i, j, k, t = Symbol(integer=True)
    Q, K, V = Symbol(shape=(n, d), real=True)
    # λ denotes scaling factor
    λ = Symbol(real=True)
    Eq << apply(*rotary_matrix(R, θ, d, b, k, i, λ), Q, K, V, j)

    Eq << Eq[-1].lhs.this.apply(Tensor.Dot.Softmax.eq.Stack.Sum.scaled_dot_product_attention, i, j, k)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.domain_defined, simplify=None)

    Eq << Tensor.EqDot.of.Eq_Mul.Eq_Block.position_representation.rotary.apply(*Eq[:2], i)

    Eq.final = Eq[-2].subs(Eq[-1])

    Eq << Tensor.Dot.eq.Add.of.Eq_Mul.Eq_Block.position_representation.rotary.apply(*Eq[:2], K[i])

    Eq << Eq[-1].subs(k, k - t).subs(i, k).subs(t, i)

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], Q[i])

    Eq << Eq[-1].subs(Eq[0].subs(k, k - i))

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.find(Sum[2]).apply(Algebra.Sum.limits.subst.offset, d / 2)

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

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-1], Eq.matmul_QRK)

    Eq << Eq.final.subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()
# created on 2023-06-09
# updated on 2023-09-16
