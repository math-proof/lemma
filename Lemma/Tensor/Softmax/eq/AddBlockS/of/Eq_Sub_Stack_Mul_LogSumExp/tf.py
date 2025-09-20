from util import *


@apply
def apply(eq):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n) - 1, i:i + Min(l, n) - 1]], (S[i], S[0], S[n - Min(l, n) + 1]))), (((S[A[i]], (S[i], (S[i], (S[n], u)))), (S[i], S[0], S[n + 1 - Min(n, u)])), (S[A[i + n - Min(n, u) + 1, i + n - Min(n, u) + 1:n]], (S[i], S[0], S[Min(n, u) - 1])))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[BlockMatrix[1][
        BlockMatrix[
            Stack[
                BlockMatrix[
                    NegativeInfinity * Ones,
                    Sliced[Indexed]
                ],
                Tuple[Min - 1]
                ],
            Stack
            ],
        BlockMatrix[
            Stack[Sliced[Tuple[Add[Min]]]],
            Stack[
                BlockMatrix[
                    NegativeInfinity * Ones
                    ]
                ]
            ]
        ] - Stack[Ones * logsumexp]])

    assert n >= 2 and u >= 2
    breadth = Add(Min(l, n), Min(u, n), -1)
    return Equal(softmax(A + (BandPart[l - 1, u - 1](Ones(n, n)) - 1) * oo), BlockMatrix(
        Stack[i:Min(l, n) - 1](BlockMatrix(Exp(z[i, Min(l, n) - 1 - i:Min(l, n) - 1]), Zeros(n - i))),
        Stack[i:n - Min(l, n) + 1](BlockMatrix(Zeros(i), Exp(z[i + Min(l, n) - 1,:Min(l, n) - 1]), Zeros(n - i - Min(l, n) + 1)))) + BlockMatrix(
        Stack[i:n - Min(u, n) + 1](BlockMatrix(Zeros(i), Exp(z[i, Min(l, n) - 1:]), Zeros(n - i - Min(u, n)))),
        Stack[i:Min(u, n) - 1](BlockMatrix(Zeros(n - Min(u, n) + i + 1), Exp(z[i + n - Min(u, n) + 1, Min(l, n) - 1:breadth - i - 1])))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix[1](
        BlockMatrix(
            Stack[i:Min(l, n) - 1](BlockMatrix(-oo * Ones(Min(l, n) - i - 1), A[i,:i])),
            Stack[i:n - Min(l, n) + 1](A[i + Min(l, n) - 1, i:i + Min(l, n) - 1])),
        BlockMatrix(
            Stack[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Stack[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * Ones(i + 1))))) - Stack[i:n](Ones(breadth) * logsumexp(A[i, relu(i + 1 - l):Min(n, i + u)]))))

    Eq << Algebra.EqExp.of.Eq.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Algebra.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(Exp[Stack[BlockMatrix]]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(Exp[Stack]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[Stack]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[Stack]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(logsumexp).defun()

    Eq << Eq[-1].this.rhs.find(Exp[Mul[Stack]]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.rhs.find(Pow[ReducedSum]).apply(Algebra.Pow.eq.Mul.One)

    Eq << Eq[-1].this.rhs.find(Stack).apply(Tensor.Stack.eq.Pow)

    Eq << Tensor.Softmax.eq.AddBlockS.of.Eq_Div_Stack_Mul_Exp.tf.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-06-08
