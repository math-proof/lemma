from util import *


def rotary_matrix(d_r, d_c, d_z, b_r, b_c, b_z, λ_r, λ_c, λ_z, θ_r, θ_c, θ_z, R, i, j, k, h):
    θ = [θ_r[i], θ_c[j], θ_z[k]]
    d = d_r + d_c + d_z
    d /= 2
    return Equal(θ_r[i], λ_r * i / b_r ** (2 * Stack[h:d_r / 2](h) / d_r)), \
        Equal(θ_c[j], λ_c * j / b_c ** (2 * Stack[h:d_c / 2](h) / d_c)),\
        Equal(θ_z[k], λ_z * k / b_z ** (2 * Stack[h:d_z / 2](h) / d_z)),\
        Equal(R(i, j, k), BlockMatrix([
            [Identity(d) * cos(θ), -Identity(d) * sin(θ)],
            [Identity(d) * sin(θ),  Identity(d) * cos(θ)]]))

def extract(eq_theta_r, eq_theta_c, eq_theta_z, eq_R):
    from Lemma.Tensor.EqDot.of.Eq_Mul.position_representation import extract_theta
    d_r, b_r, λ_r, θ_r, i, h = extract_theta(eq_theta_r)
    d_c, b_c, λ_c, θ_c, j, S[h] = extract_theta(eq_theta_c)
    d_z, b_z, λ_z, θ_z, k, S[h] = extract_theta(eq_theta_z)

    ((θijk, S[θijk]), (S[θijk], S[θijk])), Rijk = eq_R.of(Equal[BlockMatrix[BlockMatrix[1][Identity * cos[BlockMatrix], -Identity * sin[BlockMatrix]], BlockMatrix[1][Identity * sin[BlockMatrix], Identity * cos[BlockMatrix]]]])
    θ_r[i], θ_c[j], θ_z[k] = θijk
    return d_r, d_c, d_z, θ_r, θ_c, θ_z, Rijk, i, j, k, h



@apply
def apply(eq_theta_r, eq_theta_c, eq_theta_z, eq_R, i_, j_, k_):
    d_r, d_c, d_z, θ_r, θ_c, θ_z, Rijk, i, j, k, h = extract(eq_theta_r, eq_theta_c, eq_theta_z, eq_R)
    return Equal(Rijk.subs(i, i_).subs(j, j_).subs(k, k_).T @ Rijk, Rijk.subs(i, i - i_).subs(j, j - j_).subs(k, k - k_))

@prove
def prove(Eq):
    from Lemma import Tensor, Discrete, Algebra, Trigonometry, Logic

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
    # x_k denotes token embedding at index k (ie, x denotes sentence embedding)
    x = Symbol(shape=(n, d), real=True)
    # R denotes rotary matrix function
    R = Function(shape=(d, d), real=True)
    θ_r = Symbol(format_r % "θ", shape=(n, d_r / 2), real=True)
    θ_c = Symbol(format_c % "θ", shape=(n, d_c / 2), real=True)
    θ_z = Symbol(format_z % "θ", shape=(n, d_z / 2), real=True)
    # t denotes time step
    # i denotes row index, j denotes column index, k denotes column index
    i, j, t, k, h = Symbol(integer=True)
    # r, c, z denote the row index, column index, vertical index respectively, each token has a (r[t], c[t], z[t]) three-demensional index
    r, c, z = Symbol(integer=True, shape=(n,))
    # λ denotes scaling factor, default to 1
    λ_r = Symbol(format_r % "λ", real=True)
    λ_c = Symbol(format_c % "λ", real=True)
    λ_z = Symbol(format_z % "λ", real=True)
    i_quote, j_quote, k_quote = Symbol(integer=True)
    Eq << apply(*rotary_matrix(d_r, d_c, d_z, b_r, b_c, b_z, λ_r, λ_c, λ_z, θ_r, θ_c, θ_z, R, i, j, k, h), i_quote, j_quote, k_quote)

    Eq << Tensor.EqDot.of.Eq_Mul.position_representation.apply(Eq[0], i_quote)

    Eq << Tensor.EqDot.of.Eq_Mul.position_representation.apply(Eq[1], j_quote)

    Eq << Tensor.EqDot.of.EqDot.EqDot.apply(*Eq[-2:])

    Eq << Eq[-1].find(Zeros).this.apply(Algebra.Expr.eq.Block, d_r / 2, d_c / 2)

    Eq << Eq[-1].T

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq << Tensor.EqDot.of.Eq_Mul.position_representation.apply(Eq[2], k_quote)

    Eq << Tensor.EqDot.of.EqDot.EqDot.apply(*Eq[-2:])

    Eq << Eq[-1].rhs.args[1].find(Zeros).this.apply(Algebra.Expr.eq.Block, d_z / 2, d_r)

    Eq << Eq[-1].T

    Eq.rect_r = Eq[-2].rhs.find(Zeros).this.apply(Algebra.Expr.eq.Block, d_r / 2, axis=1)

    Eq.rect_r_T = Eq.rect_r.T

    Eq.rect_c = Eq[-2].rhs.find(Zeros[2]).this.apply(Algebra.Expr.eq.Block, d_c / 2, axis=1)

    Eq.rect_c_T = Eq.rect_c.T

    Eq << Eq[-3].subs(*Eq[-2:], Eq.rect_r, Eq.rect_r_T, Eq.rect_c, Eq.rect_c_T)

    Ir = Identity(d_r / 2)
    Ic = Identity(d_c / 2)
    Iz = Identity(d_z / 2)
    Zrr = Zeros(d_r / 2, d_r / 2)
    Zrc = Zeros(d_r / 2, d_c / 2)
    Zrz = Zeros(d_r / 2, d_z / 2)
    Zcr = Zrc.T
    Zcc = Zeros(d_c / 2, d_c / 2)
    Zcz = Zeros(d_c / 2, d_z / 2)
    Zzr = Zrz.T
    Zzc = Zcz.T
    Zzz = Zeros(d_z / 2, d_z / 2)
    # suppose I Matrix is as follows:
    # I = [
    #[ Ir, Zrr, Zrc, Zrc, Zrz, Zrz],
    #[Zrr,  Ir, Zrc, Zrc, Zrz, Zrz],
    #[Zcr, Zcr,  Ic, Zcc, Zcz, Zcz],
    #[Zcr, Zcr, Zcc,  Ic, Zcz, Zcz],
    #[Zzr, Zzr, Zzc, Zzc,  Iz, Zzz],
    #[Zzr, Zzr, Zzc, Zzc, Zzz,  Iz]]
    # swap the 1st and 3rd rows, 2nd and 4th rows of I Matrix, we get the row transformation
    D_r = [
        [ Ir, Zrr, Zrc, Zrc, Zrz, Zrz],
        [Zcr, Zcr, Zcc,  Ic, Zcz, Zcz],
        [Zzr, Zzr, Zzc, Zzc,  Iz, Zzz],
        [Zrr,  Ir, Zrc, Zrc, Zrz, Zrz],
        [Zcr, Zcr, -Ic, Zcc, Zcz, Zcz],
        [Zzr, Zzr, Zzc, Zzc, Zzz,  Iz]]
    Eq << Discrete.Eq.of.Eq.rmatmul.apply(Eq[-1], D_r)

    Eq << Eq[-1].this.lhs.args[:2].apply(Tensor.Dot.eq.Block, deep=True)

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Block, deep=True)

    # swap the 1st and 3rd columns, 2nd and 4th columns of I Matrix, we get the column transformation
    D_c = [
        [ Ir, Zrc, Zrz, Zrr, Zrc, Zrz],
        [Zrr, Zrc, Zrz,  Ir, Zrc, Zrz],
        [Zcr, Zcc, Zcz, Zcr, -Ic, Zcz],
        [Zcr,  Ic, Zcz, Zcr, Zcc, Zcz],
        [Zzr, Zzc,  Iz, Zzr, Zzc, Zzz],
        [Zzr, Zzc, Zzz, Zzr, Zzc,  Iz]]
    Eq << Tensor.EqDot.of.Eq.apply(Eq[-1], D_c)

    Eq << Eq[-1].this.lhs.args[-2:].apply(Tensor.Dot.eq.Block, deep=True)

    Eq.eq_matmul = Eq[-1].this.rhs.apply(Tensor.Dot.eq.Block, deep=True)

    Eq <<= (Eq.eq_matmul.lhs.args[0] @ D_c).this.apply(Tensor.Dot.eq.Block, deep=True),  (D_r @ Eq.eq_matmul.lhs.args[1]).this.apply(Tensor.Dot.eq.Block, deep=True)

    Eq << Eq[-2] @ Eq[-1]

    Eq << Eq[-1].this.lhs.args[1:3].apply(Tensor.Dot.eq.Block, deep=True)

    Eq << Eq[-1].this.find(BlockMatrix[2]).apply(Algebra.Block.eq.Eye)

    Eq.eq_matmul = Logic.Eq.of.Eq.Eq.apply(Eq.eq_matmul, Eq[-1])

    Eq << Eq[3].find(Identity).this.apply(Algebra.Expr.eq.Block, (d_r + d_c) / 2, (d_r + d_c) / 2).this.rhs.find(Identity).apply(Algebra.Expr.eq.Block, d_r / 2, d_r / 2)

    Eq << Eq[-1].rhs.args[1].find(Zeros).this.apply(Algebra.Expr.eq.Block, d_r / 2, axis=1)

    Eq << Eq[-1].T

    Eq.identity = Eq[-3].subs(*Eq[-2:])

    Eq << Eq[3].subs(i, i_quote).subs(j, j_quote).subs(k, k_quote).T @ Eq[3]

    Eq <<= Eq[-1].find(cos).this.apply(Trigonometry.Cos.eq.Block), Eq[-1].find(sin).this.apply(Trigonometry.Sin.eq.Block), \
        Eq[-1].find(BlockMatrix[2]).find(cos).this.apply(Trigonometry.Cos.eq.Block), Eq[-1].find(BlockMatrix[2]).find(sin).this.apply(Trigonometry.Sin.eq.Block)

    Eq << Eq[-5].subs(*Eq[-4:], Eq.identity)

    Eq <<= Eq[-1].find(Mul).this.apply(Algebra.Mul.eq.Block),\
        Eq[-1].find(Mul[2]).this.apply(Algebra.Mul.eq.Block),\
        Eq[-1].find(BlockMatrix[2]).find(Mul).this.apply(Algebra.Mul.eq.Block),\
        Eq[-1].find(BlockMatrix[2]).args[1].find(Mul).this.apply(Algebra.Mul.eq.Block)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq <<= Eq[-1].find(-BlockMatrix).this.apply(Algebra.Mul.eq.Block), \
        Eq[-1].find(BlockMatrix[2]).find(-BlockMatrix).this.apply(Algebra.Mul.eq.Block)

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq.eq_matmul = Logic.Eq.of.Eq.Eq.apply(Eq[-1], Eq.eq_matmul)

    Eq << Eq[3].subs(i, i - i_quote).subs(j, j - j_quote).subs(k, k - k_quote)

    Eq <<= Eq[-1].find(cos).this.apply(Trigonometry.Cos.eq.Block), Eq[-1].find(sin).this.apply(Trigonometry.Sin.eq.Block)

    Eq << Eq[-3].subs(*Eq[-2:], Eq.identity)

    Eq <<= Eq[-1].rhs.find(Mul).this.apply(Algebra.Mul.eq.Block),\
        Eq[-1].rhs.args[1].find(Mul).this.apply(Algebra.Mul.eq.Block)

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq << Eq[-1].this.find(-BlockMatrix).apply(Algebra.Mul.eq.Block)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq.eq_matmul, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-09-16
# updated on 2023-09-18
