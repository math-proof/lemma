from util import *


@apply
def apply(eq):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n), i + 1:i + Min(l, n)]], (S[i], S[0], S[n - Min(l, n)]))), (((S[A[i]], (S[i], (S[i], (S[n], u)))), (S[i], S[0], (S[n], S[-Min(n, u)]))), (S[A[i + n - Min(n, u), i + n - Min(n, u):n]], (S[i], S[0], S[Min(n, u)])))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[BlockMatrix[1][
        BlockMatrix[
            Stack[
                BlockMatrix[
                    NegativeInfinity * Ones,
                    Sliced[Indexed]
                ],
                Tuple[Min]
                ],
            Stack
            ],
        BlockMatrix[
            Stack[Sliced[Tuple[Add[Min]]], Tuple[Add]],
            Stack[
                BlockMatrix[
                    NegativeInfinity * Ones
                    ]
                ]
            ]
        ] - Stack[Ones * Log[ReducedSum[Exp]]]])

    assert n >= 2 and u >= 2 and l >= 2
    breadth = Add(Min(l, n), Min(u, n), -1)
    return Equal(softmax(A + (BandPart[l - 1, u - 1](Ones(n, n)) - 1) * oo), BlockMatrix(
        Stack[i:Min(l, n)](BlockMatrix(Exp(z[i, Min(l, n) - i - 1:Min(l, n) - 1]), Zeros(n - i))),
        Stack[i:n - Min(l, n)](BlockMatrix(Zeros(i + 1), Exp(z[i + Min(l, n), :Min(l, n) - 1]), Zeros(n - i - Min(l, n))))) + BlockMatrix(
        Stack[i:n - Min(u, n)](BlockMatrix(Zeros(i), Exp(z[i, Min(l, n) - 1:]), Zeros(n - i - Min(u, n)))),
        Stack[i:Min(u, n)](BlockMatrix(Zeros(n - Min(u, n) + i), Exp(z[i + n - Min(u, n), Min(l, n) - 1:breadth - i])))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Bool, Real

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix[1](
        BlockMatrix(
            Stack[i:Min(l, n)](BlockMatrix(-oo * Ones(Min(l, n) - i - 1), A[i, :i])),
            Stack[i:n - Min(l, n)](A[i + Min(l, n), i + 1:i + Min(l, n)])),
        BlockMatrix(
            Stack[i:n - Min(u, n)](A[i, i:i + Min(u, n)]),
            Stack[i:Min(u, n)](BlockMatrix(A[i + n - Min(u, n), n - Min(u, n) + i:], -oo * Ones(i))))) - Stack[i:n](Ones(breadth) * Log(ReducedSum(Exp(A[i, relu(i + 1 - l):Min(n, i + u)]))))))

    Eq << Bool.EqUFnS.of.Eq.apply(Eq[0], exp)

    Eq << Eq[-1].this.rhs.apply(Real.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(Exp[Stack[BlockMatrix]]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[Stack]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(Exp[Stack]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[Stack]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.rhs.find(Exp[Mul[Stack]]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.rhs.find(Pow[ReducedSum]).apply(Algebra.Pow.eq.Mul.One)

    Eq << Eq[-1].this.rhs.find(Stack).apply(Tensor.Stack.eq.Pow)

    Eq << Tensor.Softmax.eq.AddBlockS.of.Eq_DivBlock__Stack_Mul_ReducedSumExpIndexed_SlicedRelu.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-06-08



from . import tf
