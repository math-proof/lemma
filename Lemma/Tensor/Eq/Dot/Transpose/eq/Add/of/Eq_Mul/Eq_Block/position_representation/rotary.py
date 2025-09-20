from util import *


@apply
def apply(eq_theta, eq_R, x):
    from Lemma.Tensor.EqDot.of.Eq_Mul.position_representation import extract
    Rk, d, alpha, θ, b, k, *_ = extract(eq_theta, eq_R)
    return Equal(
        Rk.T @ x,
        x * Cos(alpha) + BlockMatrix(x[d / 2:], -x[:d / 2]) * Sin(alpha))

@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Trigonometry, Tensor
    from Lemma.Tensor.EqDot.of.Eq_Mul.position_representation import rotary_matrix
    # n denotes sequence length (seq_length)
    # b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # x_k denotes token embedding at index k (ie, x denotes sentence embedding)
    x = Symbol(shape=(n, d), real=True)
    # R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    # k denote token index
    # i denotes row index
    i, k = Symbol(integer=True)
    # λ denotes scaling factor
    λ = Symbol(real=True)
    Eq << apply(*rotary_matrix(R, θ, d, b, k, i, λ), x[k])

    Eq << Eq[1].T @ x[k]

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Expr.eq.Block, d / 2)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Block, deep=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq <<= Eq[-1].rhs.find(MatMul).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS), \
        Eq[-1].rhs.find(-~MatMul).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS), \
        Eq[-1].rhs.args[1].find(MatMul).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS), \
        Eq[-1].rhs.find(MatMul + ~MatMul).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq << Eq[-1].this.rhs.apply(Algebra.Block.eq.Add.Block)

    Eq << Eq[-1].this.find(BlockMatrix).apply(Algebra.Block.eq.Mul.Block)

    Eq << Eq[-1].this.find(BlockMatrix).apply(Algebra.Block.eq.Mul.Block)

    Eq <<= Eq[-1].find(Stack).this.apply(Trigonometry.Stack.eq.Cos), Eq[-1].find(Stack[Sin]).this.apply(Trigonometry.Stack.eq.Sin)

    Eq << Eq[-1].rhs.find(Stack).this.apply(Tensor.Stack.eq.Pow)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq << Eq[-1].this.find(BlockMatrix).apply(Trigonometry.Block.eq.Cos)

    Eq << Eq[-1].this.find(BlockMatrix * ~BlockMatrix).apply(Trigonometry.Block.eq.Sin)

    Eq << Eq[-1].subs(Eq[0].reversed)





if __name__ == '__main__':
    run()
# created on 2023-06-09
# updated on 2023-09-16
