from util import *


@apply
def apply(eq):
    (((((A, i), (S[0], S[i + 1])), (S[i], S[0], l)), (A[i + l, i + 1:i + l + 1], (S[i], S[0], (n, S[l])))), (S[A[i, relu(i - l + 1):i + 1]], (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[
                Stack[
                    BlockMatrix[
                        NegativeInfinity * Ones,
                        Sliced[Indexed]
                        ],
                    ],
                Stack[Tuple[Expr - Expr]]
                ] - Stack[Ones * Log[ReducedSum[Exp]]]
            ])

    assert n >= 2 and l >= 2 and l <= n
    return Equal(softmax(A + (BandPart[l - 1, 0](Ones(n, n)) - 1) * oo), BlockMatrix(
        Stack[i:l](BlockMatrix(Exp(z[i, l - i - 1:]), Zeros(n - 1 - i))),
        Stack[i:n - l](BlockMatrix(Zeros(i + 1), Exp(z[i + l]), Zeros(n - 1 - i - l)))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Bool, Real, Real

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, l), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix(
            Stack[i:l](BlockMatrix(-oo * Ones(l - i - 1), A[i, :i + 1])),
            Stack[i:n - l](A[i + l, i + 1:i + l + 1])) - Stack[i:n](Ones(l) * Log(ReducedSum(Exp(A[i, relu(i + 1 - l):i + 1]))))))

    Eq << Bool.EqUFnS.of.Eq.apply(Eq[0], exp)

    Eq << Eq[-1].this.rhs.apply(Real.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.rhs.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(Exp[Stack[BlockMatrix]]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[Stack]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.rhs.find(Exp[Mul[Stack]]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.rhs.find(Pow[ReducedSum]).apply(Algebra.Pow.eq.Mul.One)

    Eq << Eq[-1].this.rhs.find(Stack).apply(Tensor.Stack.eq.Pow)

    Eq << Tensor.Softmax.eq.Block.of.Eq_Div_Stack_Mul_ReducedSumExpIndexed_SlicedRelu.lower_triangle.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-20



from . import tf
