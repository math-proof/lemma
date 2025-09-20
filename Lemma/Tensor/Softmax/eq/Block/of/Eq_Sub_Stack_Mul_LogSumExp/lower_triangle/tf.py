from util import *


@apply
def apply(eq):
    (((((A, i), (S[0], S[i + 1])), (S[i], S[0], l)), (A[i + l - 1, i:i + l], (S[i], S[0], (n, S[l])))), (A[i, relu(i - l + 1):i + 1], (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[
                Stack[
                    BlockMatrix[
                        NegativeInfinity * Ones,
                        Sliced[Indexed]
                    ],
                    Tuple[Expr - 1]],
                Stack[Tuple[Expr + 1 - Expr]]
            ] - Stack[Ones * logsumexp]])

    assert n >= 2 and l >= 2 and l <= n
    return Equal(softmax(A + (BandPart[l - 1, 0](Ones(n, n)) - 1) * oo), BlockMatrix(
        Stack[i:l - 1](BlockMatrix(Exp(z[i, l - 1 - i:]), Zeros(n - 1 - i))),
        Stack[i:n - l + 1](BlockMatrix(Zeros(i), Exp(z[i + l - 1]), Zeros(n - i - l)))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, l), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix(
            Stack[i:l - 1](BlockMatrix(-oo * Ones(l - i - 1), A[i, :i + 1])),
            Stack[i:n - l + 1](A[i + l - 1, i:i + l])) - Stack[i:n](Ones(l) * logsumexp(A[i, relu(i + 1 - l):i + 1]))))

    Eq << Algebra.EqExp.of.Eq.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Algebra.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(Exp[Stack[BlockMatrix]]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[Stack]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(logsumexp).defun()

    Eq << Eq[-1].this.rhs.find(Exp[Mul[Stack]]).apply(Tensor.Exp.eq.Stack)

    Eq << Eq[-1].this.rhs.find(Pow[ReducedSum]).apply(Algebra.Pow.eq.Mul.One)

    Eq << Eq[-1].this.rhs.find(Stack).apply(Tensor.Stack.eq.Pow)

    Eq << Tensor.Softmax.eq.Block.of.Eq_Div_Stack_Mul_ReducedSumExpIndexed_SlicedRelu.lower_triangle.tf.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-12-16
# updated on 2023-05-20
