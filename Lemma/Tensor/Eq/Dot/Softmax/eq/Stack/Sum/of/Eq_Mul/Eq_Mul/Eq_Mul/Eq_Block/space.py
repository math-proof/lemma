from util import *



@apply
def apply(eq_theta_r, eq_theta_c, eq_theta_z, eq_R, Q, K, V, r, c, z, t):
    from Lemma.Tensor.EqDot.of.Eq_Mul.Eq_Mul.Eq_Mul.Eq_Block.position_representation.space import extract
    d_r, d_c, d_z, θ_r, θ_c, θ_z, Rijk, i, j, k, h = extract(eq_theta_r, eq_theta_c, eq_theta_z, eq_R)
    n = Q.shape[0]
    Rt = Rijk.subs(i, r[t]).subs(j, c[t]).subs(k, z[t])
    d = d_r + d_c + d_z
    θ = [θ_r[r[t] - r[i]], θ_c[c[t] - c[i]], θ_z[z[t] - z[i]]]
    return Equal(
        Softmax((Stack[t:n](Rt @ Q[t]) @ Stack[t:n](Rt @ K[t]).T) / sqrt(d)) @ V,
        Stack[j:d, i:n](Sum[t](V[t, j] * Exp(S[K[t, :d / 2] * Q[i, :d / 2] + K[t, d / 2:] * Q[i, d / 2:], K[t, :d / 2] * Q[i, d / 2:] - K[t, d / 2:] * Q[i, :d / 2]] @ [cos(θ), sin(θ)] / sqrt(d))) / ReducedSum(Exp((Q[i] @ Rt.subs(t, i).T @ Stack[i:n](Rt.subs(t, i) @ K[i]).T) / sqrt(d)))))

@prove(slow=True)
def prove(Eq):
    from Lemma import Tensor, Discrete, Algebra, Trigonometry
    from Lemma.Tensor.EqDot.of.Eq_Mul.Eq_Mul.Eq_Mul.Eq_Block.position_representation.space import rotary_matrix
    # n denotes sequence length (seq_length)
    # b_r, b_c denotes 10000
    n = Symbol(integer=True, positive=True)
    format_supscript = r"^{\color{magenta} %s}"
    format_r = '%s' + format_supscript % 'r'
    format_c = '%s' + format_supscript % 'c'
    format_z = '%s' + format_supscript % 'z'
    b_r = Symbol(format_r.replace('^', '_') % 'b', integer=True, positive=True)
    b_c = Symbol(format_c.replace('^', '_') % 'b', integer=True, positive=True)
    b_z = Symbol(format_z.replace('^', '_') % 'b', integer=True, positive=True)
    # d, d_r, d_c, d_z denotes embedding size which must be divisible by 2, under the condition that d = d_r + d_c + d_z
    d_r = Symbol(format_r % 'd', integer=True, positive=True, even=True)
    d_c = Symbol(format_c % 'd', integer=True, positive=True, even=True)
    d_z = Symbol(format_z % 'd', integer=True, positive=True, even=True)
    d = d_r + d_c + d_z
    # R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    θ_r = Symbol(format_r % "θ", shape=(n, d_r / 2), real=True)
    θ_c = Symbol(format_c % "θ", shape=(n, d_c / 2), real=True)
    θ_z = Symbol(format_z % "θ", shape=(n, d_z / 2), real=True)
    # t denotes time step
    # i denotes row index, j denotes column index
    i, j, k, t, h = Symbol(integer=True)
    # r, c, z denote the row index and column index respectively, each token has a (r[t], c[t], z[t]) two-demensional index
    r, c, z = Symbol(integer=True, shape=(n,))
    # λ denotes scaling factor, default to 1
    λ_r = Symbol(format_r % "λ", real=True)
    λ_c = Symbol(format_c % "λ", real=True)
    λ_z = Symbol(format_z % "λ", real=True)
    Q, K, V = Symbol(shape=(n, d), real=True)
    Eq << apply(*rotary_matrix(d_r, d_c, d_z, b_r, b_c, b_z, λ_r, λ_c, λ_z, θ_r, θ_c, θ_z, R, i, j, k, h), Q, K, V, r, c, z, t)

    Eq << Eq[-1].lhs.this.apply(Tensor.Dot.Softmax.eq.Stack.Sum.scaled_dot_product_attention, i, j, t)

    i_quote, j_quote, k_quote = Symbol(integer=True)
    Eq << Tensor.EqDot.of.Eq_Mul.Eq_Mul.Eq_Mul.Eq_Block.position_representation.space.apply(*Eq[:4], i_quote, j_quote, k_quote)

    Eq << Eq[-1].subs(i, r[t]).subs(j, c[t]).subs(k, z[t]).subs(i_quote, r[i]).subs(j_quote, c[i]).subs(k_quote, z[i])

    Eq.final = Eq[-3].subs(Eq[-1])

    Eq << Tensor.Dot.eq.Add.of.Eq_Mul.Eq_Mul.Eq_Mul.Eq_Block.position_representation.space.apply(*Eq[:4], K[t], r, c, z)

    Eq << Eq[-1].subs(r[h], r[t] - r[i]).subs(c[h], c[t] - c[i]).subs(z[h], z[t] - z[i])

    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], Q[i])

    Eq.theta_r, Eq.theta_c, Eq.theta_z = Eq[0].subs(i, r[t] - r[i]), Eq[1].subs(j, c[t] - c[i]), Eq[2].subs(k, z[t] - z[i])

    Eq << Eq[-1].subs(Eq.theta_r, Eq.theta_c, Eq.theta_z)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq <<= Eq[-1].find(Sum).this.apply(Algebra.Sum.limits.subst.offset, d_r / 2), \
        Eq[-1].find(Sum[2]).this.apply(Algebra.Sum.limits.subst.offset, d_r + (d_c + d_z) / 2),\
        Eq[-1].find(Sum[4]).this.apply(Algebra.Sum.limits.subst.offset, (d_r + d_c + d_z) / 2),\
        Eq[-1].find(Sum[5]).this.apply(Algebra.Sum.limits.subst.offset, (d_r + d_c) / 2),\
        Eq[-1].find(Sum[6]).this.apply(Algebra.Sum.limits.subst.offset, d_r + d_c + d_z / 2)

    Eq << Eq[-6].subs(*Eq[-5:])

    Eq << Eq[-1].subs(Eq.theta_r[j].reversed, Eq.theta_c[j].reversed, Eq.theta_z[j].reversed)

    Eq <<= Add(*Eq[-1].rhs.args[::3]).this.apply(Algebra.AddSumS.eq.Sum_Add_Sum),\
        Add(*Eq[-1].rhs.args[1::3]).this.apply(Algebra.AddSumS.eq.Sum_Add_Sum),\
        Add(*Eq[-1].rhs.args[2::3]).this.apply(Algebra.AddSumS.eq.Sum_Add_Sum)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq <<= Eq[-1].find(Mul[Add]).this.apply(Algebra.Mul_Add.eq.AddMulS),\
        Eq[-1].find(Mul[2][Add]).this.apply(Algebra.Mul_Add.eq.AddMulS),\
        Eq[-1].find(Sum[2], Mul[Add]).this.apply(Algebra.Mul_Add.eq.AddMulS), \
        Eq[-1].find(Sum[2], Mul[Add][2]).this.apply(Algebra.Mul_Add.eq.AddMulS),\
        Eq[-1].find(Sum[3], Mul[Add]).this.apply(Algebra.Mul_Add.eq.AddMulS), \
        Eq[-1].find(Sum[3], Mul[Add][2]).this.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-7].subs(*Eq[-6:])

    Eq <<= Add(*Eq[-1].find(Sum).expr.args[1:3]).this.apply(Algebra.AddMulS.eq.Mul_Add), \
        Add(*Eq[-1].find(Sum).expr.args[::3]).this.apply(Algebra.AddMulS.eq.Mul_Add), \
        Add(*Eq[-1].find(Sum[2]).expr.args[1:3]).this.apply(Algebra.AddMulS.eq.Mul_Add),\
        Add(*Eq[-1].find(Sum[2]).expr.args[::3]).this.apply(Algebra.AddMulS.eq.Mul_Add),\
        Add(*Eq[-1].find(Sum[3]).expr.args[1:3]).this.apply(Algebra.AddMulS.eq.Mul_Add),\
        Add(*Eq[-1].find(Sum[3]).expr.args[::3]).this.apply(Algebra.AddMulS.eq.Mul_Add)

    Eq << Eq[-7].subs(*Eq[-6:])

    Eq <<= Eq[-1].find(Sum).this.apply(Tensor.Sum.eq.Add.Dot),\
        Eq[-1].find(Sum[2]).this.apply(Tensor.Sum.eq.Add.Dot),\
        Eq[-1].find(Sum[3]).this.apply(Tensor.Sum.eq.Add.Dot)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq <<= Eq[-1].find(Stack).this.apply(Tensor.Stack.eq.Add),\
        Eq[-1].find(MatMul[2][~Stack]).this.apply(Tensor.Stack.eq.Add),\
        Eq[-1].find(MatMul[3][~Stack]).this.apply(Tensor.Stack.eq.Add),\
        Eq[-1].find(MatMul[4][~Stack]).this.apply(Tensor.Stack.eq.Add),\
        Eq[-1].find(MatMul[5][~Stack]).this.apply(Tensor.Stack.eq.Add),\
        Eq[-1].find(MatMul[6][~Stack]).this.apply(Tensor.Stack.eq.Add)

    Eq << Eq[-7].subs(*Eq[-6:])

    Eq <<= Add(*Eq[-1].rhs.args[:3]).this.apply(Tensor.Add.eq.Dot.Block, swap=(False, True)), Add(*Eq[-1].rhs.args[3:]).this.apply(Tensor.Add.eq.Dot.Block, swap=(False, True))

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq << Eq[-1].this.find(BlockMatrix).apply(Algebra.Block.eq.Add.Block, (-1, slice(-1, None), slice(-1, None)))

    Eq << Eq[-1].this.find(Add[~BlockMatrix]).apply(Algebra.Block.eq.Mul.Block)

    Eq << Eq[-1].this.find(Add[~BlockMatrix]).apply(Algebra.Block.eq.Mul.Block)

    Eq << Eq[-1].this.find((~BlockMatrix) @ BlockMatrix).apply(Algebra.Block.eq.Add.Block, (-1, -1, -1))

    Eq << Eq[-1].this.find(Add[~BlockMatrix]).apply(Algebra.Block.eq.Mul.Block)

    Eq << Eq[-1].this.find(Add[~BlockMatrix]).apply(Algebra.Block.eq.Mul.Block)

    Eq << Eq[-1].this.find(Mul[~BlockMatrix]).apply(Algebra.Block.eq.Neg.Block)

    Eq <<= Eq[-1].find(BlockMatrix[Cos]).this.apply(Trigonometry.Block.eq.Cos), Eq[-1].find(BlockMatrix[Sin]).this.apply(Trigonometry.Block.eq.Sin)

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq << Eq[-1].this.rhs.apply(Tensor.Add.eq.Dot.Block, swap=True)

    Eq << Eq.final.subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-09-20
