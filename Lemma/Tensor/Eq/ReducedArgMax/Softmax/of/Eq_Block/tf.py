from util import *


@apply
def apply(eq):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n) - 1, i:i + Min(l, n) - 1]], (S[i], S[0], S[n - Min(l, n) + 1]))), (((S[A[i]], (S[i], (S[i], (S[n], u)))), (S[i], S[0], (S[1], S[n], S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u) + 1]), (S[i + n - Min(n, u) + 1], S[n])), (S[i], S[0], (S[n], S[u]))))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
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
            Stack[Sliced[Tuple[Add[Min]]], Tuple[Add]],
            Stack[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * Ones
                    ],
                Tuple[Min - 1]
                ]
            ]
        ] - Stack[Ones * Log[ReducedSum[Exp]]]])

    assert n >= 2 and l >= 2 and u >= 2
    return Equal(ReducedArgMax(softmax(A + (BandPart[l - 1, u - 1](Ones(n, n)) - 1) * oo)) - Stack[i:n](i), ReducedArgMax(z) - Min(l, n) + 1)


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Set, Bool

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix[1](
        BlockMatrix(
            Stack[i:Min(l, n) - 1](BlockMatrix(-oo * Ones(Min(l, n) - i - 1), A[i, :i])),
            Stack[i:n - Min(l, n) + 1](A[i + Min(l, n) - 1, i:i + Min(l, n) - 1])
        ),
        BlockMatrix(
            Stack[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Stack[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * Ones(i + 1)))
        )) - Stack[i:n](Ones(breadth) * Log(ReducedSum(Exp(A[i, relu(i + 1 - l):Min(n, i + u)]))))))

    Eq << Tensor.Softmax.eq.AddBlockS.of.Eq_Sub_Stack_Mul_LogSumExp.tf.apply(Eq[0])

    z_quote = Symbol(Eq[-1].lhs)
    Eq.z_quote_def = z_quote.this.definition

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq.z_quote_def, Eq[-1])

    Eq << Eq[-1][i]

    Eq.four_blocks = Eq[-1].this.rhs.apply(Algebra.AddIteS.eq.IteAnd)

    j = Symbol(integer=True)
    Eq << Eq.four_blocks.find(Add[BlockMatrix]).this.apply(Tensor.Expr.eq.Stack, j)

    Eq << Eq[-1].this.find(Piecewise[2]).apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 0)

    Eq.block0 = Eq[-1].this.rhs.apply(Tensor.Stack.Ite.eq.Block)

    Eq << Eq.four_blocks.find(ExprCondPair[2]).find(BlockMatrix).this.apply(Tensor.Expr.eq.Stack, j)

    Eq.block1 = Eq[-1].this.rhs.apply(Tensor.Stack.eq.Exp)

    Eq << Eq.four_blocks.find(ExprCondPair[3]).find(Add[BlockMatrix]).this.apply(Tensor.Expr.eq.Stack, j)

    Eq << Eq[-1].this.find(Piecewise).apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 0)

    Eq << Eq[-1].this.find(Piecewise).apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 0)

    Eq << Eq[-1].this.find(And).apply(Bool.And_Or.Is.OrAndS)

    Eq.block2 = Eq[-1].this.find(Stack).apply(Tensor.Stack.Ite.eq.Block)

    Eq << Eq.four_blocks.find(ExprCondPair[4]).find(Add[BlockMatrix]).this.apply(Tensor.Expr.eq.Stack, j)

    Eq << Eq[-1].this.find(Piecewise[ExprCondPair[3]]).apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Eq[-1].this.find(Add[Piecewise]).apply(Algebra.AddIteS.eq.IteAnd)

    Eq.block3 = Eq[-1].this.find(Stack).apply(Tensor.Stack.Ite.eq.Block)

    Eq << Eq.four_blocks.subs(Eq.block0, Eq.block1, Eq.block2, Eq.block3)

    Eq << Algebra.EqReducedArgMax.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedArgMax.eq.Ite.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, -2)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not, 1)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.Ite__IteAnd_Not)

    Eq << Eq[-1].this.find(And).apply(Algebra.Lt.Lt.Is.Lt.Min)

    Eq << Eq[-1].this.find(And).apply(Set.Cond.Cond.Is.In.Ico)

    Eq.four_blocks = Eq[-1].this.find(And).apply(Algebra.Ge.Ge.Is.Ge.Max)

    Eq << Tensor.And.Imp.Block.of.Eq_Block.tf.apply(Eq[0])

    Eq <<= Eq[-3].this.rhs.apply(Algebra.EqReducedArgMax.of.Eq), Eq[-2].this.rhs.apply(Algebra.EqReducedArgMax.of.Eq), Eq[-1].this.rhs.apply(Algebra.EqReducedArgMax.of.Eq)

    Eq <<= Eq[-3].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add), \
        Eq[-2].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq.block3 = Eq[-3].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq.block0 = Eq[-2].this.rhs.apply(Algebra.EqAdd.Is.Eq_Sub, rhs=slice(0, 3))

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq.block1 = Eq[-1].this.rhs.apply(Algebra.EqAdd.Is.Eq_Sub, rhs=slice(0, 3))

    Eq << Bool.EqIteS.of.Imp_Eq.apply(Eq.block0, Eq.four_blocks.rhs, index=0, reverse=True)

    Eq << Bool.EqIteS.of.Imp_Eq.apply(Eq.block1, Eq[-1].rhs, index=1, reverse=True)

    Eq << Bool.EqIteS.of.Imp_Eq.apply(Eq.block3, Eq[-1].rhs, index=1, reverse=True)

    Eq << Algebra.Eq.of.And.apply(Eq.four_blocks & Eq[-1] & Eq[-2] & Eq[-3]).reversed

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.lhs.apply(Tensor.Stack.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Add)

    Eq << Eq[-1].this.find(Stack[ReducedArgMax]).apply(Tensor.Stack.eq.ReducedArgMax)

    Eq << Eq[-1].subs(Eq.z_quote_def)

    Eq << Eq[-1].this.apply(Algebra.EqAdd.Is.Eq_Sub, rhs=3)





if __name__ == '__main__':
    run()
# created on 2022-01-04
# updated on 2023-05-20
