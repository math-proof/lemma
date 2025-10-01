from util import *


@apply
def apply(eq):
    (H, ((((A, i), (S[0], S[i + 1])), (S[i], S[0], l)), (S[A[i + l, i + 1:i + l + 1]], (S[i], S[0], (n, S[l])))), ((S[H[i]], S[A[i, relu(i - l + 1):i + 1]]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[1][Zeros, Expr] + BlockMatrix[
                Stack[
                    BlockMatrix[
                        NegativeInfinity * Ones,
                        Sliced[Indexed]
                    ],
                ],
                Stack[Tuple[Expr - Expr]]
            ] - Stack[Ones * logsumexp[Add[BlockMatrix[Zeros, Expr]]]]])
    assert n >= 2 and l >= 2 and l <= n
    return Equal(softmax(A + H * Identity(n) + (BandPart[l - 1, 0](Ones(n, n)) - 1) * oo),
                 BlockMatrix(
                     Stack[i:l](BlockMatrix(Exp(z[i, l - i - 1:]), Zeros(n - 1 - i))),
                     Stack[i:n - l](BlockMatrix(Zeros(i + 1), Exp(z[i + l]), Zeros(n - 1 - i - l)))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    H = Symbol(shape=(n,), real=True)
    z = Symbol(shape=(n, l), real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](Zeros(n, l - 1), H) + BlockMatrix(
            Stack[i:l](BlockMatrix(-oo * Ones(l - i - 1), A[i, :i + 1])),
            Stack[i:n - l](A[i + l, i + 1:i + l + 1])) - Stack[i:n](Ones(l) * logsumexp((A[i, relu(i + 1 - l):i + 1] + BlockMatrix(Zeros(Min(i, l - 1)), H[i]))))))

    Eq << Eq[0].this.find(BlockMatrix[1]).apply(Algebra.Block.split, Min(l, n))

    Eq << Add(*Eq[-1].find(Add[BlockMatrix]).args[:2]).this.apply(Algebra.Add.Block.eq.Block)

    Eq.z_def = Eq[-2].subs(Eq[-1])

    A = Symbol(Add(*Eq[1].lhs.arg.args[:2]))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i][:i + 1]

    Eq << Eq[-1].this.find(Mul).apply(Tensor.Expr.eq.Stack, simplify=None)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Mul.Stack)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Block)

    Eq.matmul_subs = Eq[-1].this.apply(Algebra.EqAdd.Is.Eq_Sub, rhs=0).reversed

    Eq << Eq.z_def.rhs.find(Add).this.args[0].apply(Tensor.Expr.eq.Stack, i)

    Eq << Eq[-1].this.rhs.apply(Tensor.Add_Stack.eq.Stack_Add)

    Eq << Eq[-1].this.rhs.subs(Eq.matmul_subs)

    Eq << Eq[-1].this.rhs.find(Add).apply(Tensor.Expr.eq.Stack)

    Eq << Eq[-1].this.rhs.find(-~Piecewise).find(Less).simplify()

    Eq << Eq[-1].this.rhs.find(-~Piecewise).find(Less).apply(Algebra.Lt.transport, lhs=slice(0, 3, 2))

    Eq << Eq[-1].this.rhs.find(-Piecewise).apply(Algebra.Mul.eq.Ite)

    Eq << Eq[-1].this.rhs.find(Add).apply(Algebra.AddIteS.eq.IteAnd, swap=True)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq.upper_part = Eq[-1].this.rhs.apply(Tensor.Stack.Ite.eq.Stack.Block)

    Eq << Eq.A_def[i + Min(l, n)][i + 1:i + Min(l, n) + 1]

    Eq << Eq[-1].this.find(Mul).apply(Tensor.Expr.eq.Stack, simplify=None)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Mul.Stack)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Block)

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (i, 0, n - Min(l, n)), simplify=None)

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.Add)

    Eq.lower_part = Eq[-1].this.find(Stack[BlockMatrix]).apply(Tensor.Stack.Block.eq.Block.Stack)

    Eq << Eq.A_def[i][relu(i + 1 - l):i + 1]

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.offset, -Eq[-1].find(relu))

    Eq << Eq[-1].this.find(Mul[Stack]).apply(Tensor.Expr.eq.Stack, simplify=None)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Mul.Stack)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(Algebra.Mul.eq.Block)

    Eq << Eq[-1].this.find(Zeros).shape[0].find(relu).apply(Tensor.Relu.eq.Add.Min)

    Eq << Eq[-1].this.find(Zeros).shape[0].apply(Algebra.Add.eq.Min)
    Eq << Eq.z_def.subs(Eq[-1].reversed, Eq.upper_part, Eq.lower_part.reversed)

    Eq << Tensor.Softmax.eq.Block.of.Eq_Sub_Stack_Mul_LogSumExp.lower_triangle.apply(Eq[-1])

    Eq << Eq[-1].this.find(Symbol).definition





if __name__ == '__main__':
    run()
# created on 2022-03-13
# updated on 2023-09-17
