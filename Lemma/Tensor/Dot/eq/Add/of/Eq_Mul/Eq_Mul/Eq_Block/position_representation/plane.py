from util import *



@apply
def apply(eq_theta_r, eq_theta_c, eq_R, xt, r, c):
    from Lemma.Tensor.EqDot.of.Eq_Mul.Eq_Mul.Eq_Block.position_representation.plane import extract
    d_r, d_c, θ_r, θ_c, Rij, i, j, k = extract(eq_theta_r, eq_theta_c, eq_R)
    alpha = [θ_r[r[k]], θ_c[c[k]], θ_r[r[k]], θ_c[c[k]]]
    d = d_r + d_c
    d /= 2
    return Equal(
        Rij.subs(i, r[k]).subs(j, c[k]) @ xt,
        xt * cos(alpha) + [-xt[d:], xt[:d]] * sin(alpha))

@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Trigonometry, Tensor
    from Lemma.Tensor.EqDot.of.Eq_Mul.Eq_Mul.Eq_Block.position_representation.plane import rotary_matrix
    # n denotes sequence length (seq_length)
    # b_r, b_c denotes 10000
    n = Symbol(integer=True, positive=True)
    format_supscript = r"^{\color{magenta} %s}"
    format_r = '%s' + format_supscript % 'r'
    format_c = '%s' + format_supscript % 'c'
    b_r = Symbol(format_r.replace('^', '_') % 'b', integer=True, positive=True)
    b_c = Symbol(format_c.replace('^', '_') % 'b', integer=True, positive=True)
    # d, d_r, d_c denotes embedding size which must be divisible by 2, under the condition that d = d_r + d_c
    d_r = Symbol(format_r % 'd', integer=True, positive=True, even=True)
    d_c = Symbol(format_c % 'd', integer=True, positive=True, even=True)
    d = d_r + d_c
    # x_k denotes token embedding at index k (ie, x denotes sentence embedding)
    x = Symbol(shape=(n, d), real=True)
    # R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    θ_r = Symbol(format_r % "θ", shape=(n, d_r / 2), real=True)
    θ_c = Symbol(format_c % "θ", shape=(n, d_c / 2), real=True)
    # t denotes time step
    # i denotes row index, j denotes column index
    i, j, t, k = Symbol(integer=True)
    # r, c denote the row index and column index respectively, each token has a (r[t], c[t]) two-demensional index
    r, c = Symbol(integer=True, shape=(n,))
    # λ denotes scaling factor, default to 1
    λ_r = Symbol(format_r % "λ", real=True)
    λ_c = Symbol(format_c % "λ", real=True)
    Eq << apply(*rotary_matrix(d_r, d_c, b_r, b_c, λ_r, λ_c, θ_r, θ_c, R, i, j, k), x[t], r, c)

    Eq << Eq[2].subs(i, r[k]).subs(j, c[k]) @ x[t]

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Expr.eq.Block, (d_r + d_c) / 2)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Block, deep=True)

    Eq << Eq[-1].this.rhs.apply(Algebra.Block.eq.Add.Block, (-1, slice(1, None)))

    Eq <<= Eq[-1].rhs.find(MatMul).this.apply(Tensor.Dot.Eye.eq.Mul), \
        Eq[-1].find(MatMul[2]).this.apply(Tensor.Dot.Eye.eq.Mul), \
        Eq[-1].find(-~MatMul).this.apply(Tensor.Dot.Eye.eq.Mul), \
        Eq[-1].rhs.args[1].find(MatMul).this.apply(Tensor.Dot.Eye.eq.Mul)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq << Eq[-1].this.find(BlockMatrix).apply(Algebra.Block.eq.Mul.Block)

    Eq << Eq[-1].this.find(BlockMatrix).apply(Algebra.Block.eq.Mul.Block)

    Eq << Eq[-1].this.find(BlockMatrix).apply(Trigonometry.Block.eq.Cos)

    Eq << Eq[-1].this.find(BlockMatrix[2]).apply(Trigonometry.Block.eq.Sin)

    # reference:
    # https://arxiv.org/pdf/2402.12376.pdf#page=11
    # https://arxiv.org/pdf/2312.17172.pdf#page=4



if __name__ == '__main__':
    run()
# created on 2023-09-16
# updated on 2023-09-18
