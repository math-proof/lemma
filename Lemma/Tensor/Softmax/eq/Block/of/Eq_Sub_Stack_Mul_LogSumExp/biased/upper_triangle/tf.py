from util import *


@apply
def apply(eq):
    (H, ((((A, i), (S[i], (S[i], (n, u)))), (S[i], S[0], S[n - Min(n, u) + 1])), (S[A[i + n - Min(u, n) + 1, i + n - Min(n, u) + 1:]], (S[i], S[0], S[Min(u, n) - 1]))), ((S[H[i]], S[A[i, i:Min(n, i + u)]]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[1][Expr, Zeros] + BlockMatrix[
                Stack[Sliced[Indexed, Tuple[Add[Min]]]],
                Stack[
                    BlockMatrix[
                        NegativeInfinity * Ones
                    ],
                ]
            ] - Stack[Ones * logsumexp[Add[BlockMatrix[Expr, Zeros]]]]])
    assert n >= 2 and u >= 2
    breadth = Min(u, n) - 1
    return Equal(softmax(A + H * Identity(n) + (BandPart[0, u - 1](Ones(n, n)) - 1) * oo),
                 BlockMatrix(
                     Stack[i:n - breadth](BlockMatrix(Zeros(i), Exp(z[i]), Zeros(n - 1 - i - breadth))),
                     Stack[i:breadth](BlockMatrix(Zeros(n - breadth + i), Exp(z[i + n - breadth, :breadth - i])))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Logic

    n, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    H = Symbol(shape=(n,), real=True)
    z = Symbol(shape=(n, Min(u, n)), real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](H, Zeros(n, Min(u, n) - 1)) + BlockMatrix(
            Stack[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Stack[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * Ones(i + 1)))) - Stack[i:n](Ones(Min(u, n)) * logsumexp((A[i, i:Min(n, i + u)] + BlockMatrix(H[i], Zeros(Min(n - i, u) - 1)))))))

    Eq << Eq[0].this.find(BlockMatrix[1]).apply(Algebra.Block.split, n + 1 - Min(u, n))

    Eq << Add(*Eq[-1].find(Add[BlockMatrix]).args[:2]).this.apply(Algebra.Add.Block.eq.Block)

    Eq.z_def = Eq[-2].subs(Eq[-1])

    A = Symbol(Add(*Eq[1].lhs.arg.args[:2]))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i + n + 1 - Min(u, n)][i + n + 1 - Min(u, n):]

    Eq << Eq[-1].this.find(Mul[Stack]).apply(Tensor.Expr.eq.Stack, simplify=None)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Mul.Stack)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(Algebra.Mul.eq.Block)

    Eq.matmul_subs = Eq[-1].this.apply(Algebra.Eq.transport, rhs=0).reversed

    Eq << Eq.z_def.rhs.find(Add[2]).this.args[0].apply(Tensor.Expr.eq.Stack, i)

    Eq << Eq[-1].this.rhs.apply(Tensor.Add_Stack.eq.Stack_Add)

    Eq << Eq[-1].this.rhs.subs(Eq.matmul_subs)

    Eq << Eq[-1].this.rhs.find(Add).apply(Tensor.Expr.eq.Stack)

    Eq << Eq[-1].this.rhs.find(-Piecewise).apply(Algebra.Mul.eq.Ite)

    Eq << Eq[-1].this.rhs.find(Add).apply(Algebra.AddIteS.eq.IteAnd)

    Eq << Eq[-1].this.find(Piecewise).apply(Logic.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.find(Piecewise).apply(Logic.Ite_Ite.eq.Ite__Ite)

    Eq.lower_part = Eq[-1].this.rhs.apply(Tensor.Stack.Ite.eq.Stack.Block)

    Eq << Eq.A_def[i]#[i:i + Min(u, n)]

    Eq << Logic.AllIn.of.All.apply(Eq[-1], (i, 0, n + 1 - Min(u, n)))

    Eq << Algebra.All.Eq.Slice.of.All_Eq.apply(Eq[-1], slice(i, i + Min(u, n)))

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.offset, -i)

    Eq << Eq[-1].this.find(Mul).apply(Tensor.Expr.eq.Stack, simplify=None)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Mul.Stack)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Block)

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.Add)

    Eq.upper_part = Eq[-1].this.find(Stack[BlockMatrix]).apply(Tensor.Stack.Block.eq.Block.Stack)

    Eq << Eq.A_def[i][i:Min(n, i + u)]

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.offset, -i)

    Eq << Eq[-1].this.find(Mul[Stack]).apply(Tensor.Expr.eq.Stack, simplify=None)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Mul.Stack)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(Algebra.Mul.eq.Block)

    Eq << Eq[-1].this.find(Zeros).shape[0].find(Min).apply(Algebra.Min.eq.Add, i)

    Eq << Eq.z_def.subs(Eq[-1].reversed, Eq.upper_part.reversed, Eq.lower_part)

    Eq << Tensor.Softmax.eq.Block.of.Eq_Sub_Stack_Mul_LogSumExp.upper_triangle.tf.apply(Eq[-1])

    Eq << Eq[-1].this.find(Symbol).definition





if __name__ == '__main__':
    run()
# created on 2022-03-14
# updated on 2023-09-17

