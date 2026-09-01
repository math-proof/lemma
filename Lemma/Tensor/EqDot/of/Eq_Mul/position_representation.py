from util import *


def eq_theta(θ, d, b, i, j, λ=1):
    return Equal(θ[i], λ * i / b ** (Stack[j:d / 2](j) / (d / 2)))

def rotary_def(θ, d, k):
    return BlockMatrix([
        [Identity(d / 2) * cos(θ[k]), -Identity(d / 2) * sin(θ[k])],
        [Identity(d / 2) * sin(θ[k]), Identity(d / 2) * cos(θ[k])]])

def rotary_matrix(R, θ, d, b, i, j, λ=1):
    return eq_theta(θ, d, b, i, j, λ), Equal(R(i), rotary_def(θ, d, i))

def extract_theta(eq_theta):
    (tλ, (b, ((k, limit_k), d))), (θ, t) = eq_theta.of(Equal[Expr / Symbol ** (2 * Stack / Symbol), Indexed])
    assert d.is_even
    S[k], S[0], S[d / 2] = limit_k
    λ = tλ / t
    return d, b, λ, θ, t, k

def extract(eq_theta, eq_R):
    d, b, λ, θ, i, j = extract_theta(eq_theta)
    ((cos, sin), (S[-sin], S[cos])), Rk = eq_R.of(Equal[BlockMatrix[BlockMatrix[1], BlockMatrix[1]]])
    S[θ[i]] = cos.of(Cos[Expr] * Identity)
    S[θ[i]] = sin.of(-Identity * Sin[Expr])
    alpha = BlockMatrix(θ[i], θ[i])

    return Rk, d, alpha, θ, b, i, j, λ

@apply
def apply(eq_theta, t):
    d, b, λ, θ, i, j = extract_theta(eq_theta)
    Rk = rotary_def(θ, d, i)
    return Equal(Rk.subs(i, t).T @ Rk, Rk.subs(i, i - t))

@prove
def prove(Eq):
    from Lemma import Tensor, Nat, Real

    # n denotes sequence length (seq_length)
    # b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    θ = Symbol(shape=(n, d / 2), real=True)
    # i, t denote token index
    # j denotes row index
    i, j, t = Symbol(integer=True)
    # λ denotes scaling factor
    λ = Symbol(real=True)
    Eq << apply(eq_theta(θ, d, b, i, j, λ), t)

    Eq << Eq[1].subs(Eq[0]).subs(Eq[0].subs(i, t))

    Eq << Eq[-1].this.lhs.apply(Tensor.DotAppendSHstackS.eq.AppendHstackSAddSDotS, deep=True)

    Eq <<= Eq[-1].lhs.find(MatMul).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS),\
        Eq[-1].lhs.find(MatMul[2]).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS),\
        Eq[-1].lhs.find((~MatMul) - MatMul).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS),\
        Eq[-1].lhs.find(MatMul - ~MatMul).this.apply(Tensor.Dot.eq.Stack_Sum_MulGetS)

    Eq <<= Eq[-4].rhs.find(Mul).this.apply(Nat.Mul_Delta, 1, reverse=True),\
        Eq[-3].rhs.find(Mul).this.apply(Nat.Mul_Delta, 1, reverse=True),\
        Eq[-2].rhs.find(Mul).this.apply(Nat.Mul_Delta, 1, reverse=True),\
        Eq[-1].rhs.find(Mul).this.apply(Nat.Mul_Delta, 1, reverse=True)

    Eq << Eq[-9].subs(*Eq[-8:])

    Eq <<= Eq[-1].find(Stack).this().find(Element).simplify(),\
        Eq[-1].find(Stack + ~Stack).this().find(Element).simplify(),\
        Eq[-1].find((~Stack) - Stack).this().find(Element).simplify(),\
        Eq[-1].find(Stack - ~Stack).this().find(Element).simplify()

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq <<= Eq[-1].find(Stack + Stack).this.apply(Tensor.Add_Stack.eq.Stack_Add, deep=True),\
        Eq[-1].find(Stack - Stack).this.apply(Tensor.Add_Stack.eq.Stack_Add, deep=True),\
        Eq[-1].lhs.args[1].find(Stack - Stack).this.apply(Tensor.Add_Stack.eq.Stack_Add, deep=True)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq <<= Eq[-1].find(Mul + Mul).this.apply(Nat.AddMulS.eq.Mul_Add),\
        Eq[-1].find(Mul[KroneckerDelta] - Mul).this.apply(Nat.AddMulS.eq.Mul_Add)
    Eq << Eq[-3].subs(*Eq[-2:])
    Eq <<= Eq[-1].lhs.find(Sin * Sin + Cos * Cos).this.apply(Real.AddSinSin_CosCos.eq.CosSub), \
        Eq[-1].lhs.find(Sin * Cos - Sin * Cos).this.apply(Real.SubMulSSin_Cos.eq.SinSub)

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq <<= Eq[-1].lhs.find(Add).this.apply(Nat.AddMulS.eq.Mul_Add),\
        Eq[-1].find(Sin[~Add]).this.apply(Nat.AddMulS.eq.Mul_Add)

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq << Eq[-1].find(Stack[-Expr]).this.simplify()

    Eq << Eq[-2].subs(Eq[-1])

    Eq <<= Eq[-1].find(Stack).this.apply(Tensor.Stack_Mul.eq.MulStackS),\
        Eq[-1].find(-~Stack).this.apply(Tensor.Stack_Mul.eq.MulStackS)

    Eq << Eq[-1].find(Stack[KroneckerDelta]).this.apply(Tensor.Stack.eq.Eye)

    Eq << Eq[-4].subs(*Eq[-3:])

    Eq <<= Eq[-1].find(Stack).this.apply(Real.Stack.eq.Cos), Eq[-1].find(Stack[Sin]).this.apply(Real.Stack.eq.Sin)

    Eq << Eq[-1].rhs.find(Stack).this.apply(Tensor.Stack_PowGetS.eq.Pow)

    _j = Eq[-1].lhs.variable
    Eq << Eq[0].subs(i, i - t).this.find(Stack).limits_subs(j, _j).reversed

    Eq << Eq[-5].subs(*Eq[-4:])





if __name__ == '__main__':
    run()
# created on 2023-09-16
# updated on 2023-09-20
