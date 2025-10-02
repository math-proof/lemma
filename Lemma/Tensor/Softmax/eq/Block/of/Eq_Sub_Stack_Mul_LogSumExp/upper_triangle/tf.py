from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], (n, u)))), (S[i], S[0], (S[1], S[n],  S[-Min(n, u)]))), (S[A[i + n - Min(n, u) + 1][i + n - Min(n, u) + 1:n]], (S[i], S[0], S[Min(n, u) - 1]))), (S[A[i][i:Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Stack[
                Sliced[Indexed, Tuple[Add[Min]]],
                Tuple[Add]
            ],
            Stack[
                BlockMatrix[NegativeInfinity * Ones]
            ]
        ] - Stack[Ones * logsumexp]
    ])

    assert n >= 2 and u >= 2
    breadth = Min(u, n) - 1
    return Equal(softmax(A + (BandPart[0, u - 1](Ones(n, n)) - 1) * oo), BlockMatrix(
        Stack[i:n - breadth](BlockMatrix(Zeros(i), Exp(z[i]), Zeros(n - 1 - i - breadth))),
        Stack[i:breadth](BlockMatrix(Zeros(n - breadth + i), Exp(z[i + n - breadth, :breadth - i])))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Logic

    n, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, Min(u, n)), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix(
        Stack[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
        Stack[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * Ones(i + 1)))) - Stack[i:n](Ones(Min(u, n)) * logsumexp(A[i, i:Min(n, i + u)]))))

    Eq << Logic.EqUFnS.of.Eq.apply(Eq[0], exp)

    Eq << Eq[-1].this.rhs.apply(Algebra.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(Exp[Stack[BlockMatrix]]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[Stack]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(logsumexp).defun()

    Eq << Eq[-1].this.rhs.find(Exp[Mul[Stack]]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.rhs.find(Pow[ReducedSum]).apply(Algebra.Pow.eq.Mul.One)

    Eq << Eq[-1].this.rhs.find(Stack).apply(Tensor.Stack.eq.Pow)

    Eq << Tensor.Softmax.eq.Block.of.Eq_Div_Stack_ReducedSumExp.upper_triangle.tf.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-12
