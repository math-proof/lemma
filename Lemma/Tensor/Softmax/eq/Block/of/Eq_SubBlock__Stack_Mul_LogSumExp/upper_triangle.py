from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], u))), (S[i], S[0], (n,  S[u]))), (A[i + n - u, i + n - u:], (S[i], S[0], S[u]))), (A[i, i:Min(n, i + u)], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Stack[
                Sliced[Indexed, Tuple[Add]],
                Tuple[Expr - Expr]
            ],
            Stack[
                BlockMatrix[NegativeInfinity * Ones]
            ]
        ] - Stack[Ones * Log[ReducedSum[Exp]]]])

    assert n >= 2 and u >= 2 and u <= n

    return Equal(softmax(A + (BandPart[0, u - 1](Ones(n, n)) - 1) * oo), BlockMatrix(
        Stack[i:n - u](BlockMatrix(Zeros(i), Exp(z[i]), Zeros(n - i - u))),
        Stack[i:u](BlockMatrix(Zeros(n - u + i), Exp(z[i + n - u, :u - i])))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Logic

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, u), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix(
        Stack[i:n - u](A[i, i:i + u]),
        Stack[i:u](BlockMatrix(A[i + n - u, n - u + i:], -oo * Ones(i)))) - Stack[i:n](Ones(u) * Log(ReducedSum(Exp(A[i, i:Min(n, i + u)]))))))

    Eq << Logic.EqUFnS.of.Eq.apply(Eq[0], exp)

    Eq << Eq[-1].this.rhs.apply(Algebra.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(Exp[Stack[BlockMatrix]]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[Stack]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.rhs.find(Exp[Mul[Stack]]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.rhs.find(Pow[ReducedSum]).apply(Algebra.Pow.eq.Mul.One)

    Eq << Eq[-1].this.rhs.find(Stack).apply(Tensor.Stack.eq.Pow)

    Eq << Tensor.Softmax.eq.Block.of.Eq_Div_Stack_Mul_ReducedSumExp.upper_triangle.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-20
