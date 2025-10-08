from util import *


@apply
def apply(eq):
    (((((A, i), (S[0], S[i + 1])), (S[i], S[0], l)), (A[i + l, i + 1:i + l + 1], (S[i], S[0], (n, S[l])))), (A[i, relu(i - l + 1):i + 1], (S[i], S[0], S[n]))), z = \
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
    return Equal(ReducedArgMax(softmax(A + (BandPart[l - 1, 0](Ones(n, n)) - 1) * oo)) - Stack[i:n](i), ReducedArgMax(z) - l + 1)


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Bool

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, l), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix(
            Stack[i:l](BlockMatrix(-oo * Ones(l - i - 1), A[i, :i + 1])),
            Stack[i:n - l](A[i + l, i + 1:i + l + 1])) - Stack[i:n](Ones(l) * Log(ReducedSum(Exp(A[i, relu(i + 1 - l):i + 1]))))))

    Eq << Tensor.Softmax.eq.Block.of.Eq_Sub_Stack_Mul_LogSumExp.lower_triangle.apply(Eq[0])

    z_quote = Symbol(Eq[-1].lhs)
    Eq << Eq[-1].subs(z_quote.this.definition.reversed)

    Eq << Algebra.EqReducedArgMax.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedArgMax.eq.Block.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax).apply(Tensor.ReducedArgMax.eq.Stack.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[Stack]).apply(Tensor.ReducedArgMax.eq.Stack.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq.eq_reducedArgMax = Eq[-1].this.rhs.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq.eq_lamda = Equal(
        Stack[i:Min(l, n)](z[i]),
        Stack[i:Min(l, n)](BlockMatrix(-oo * Ones(Min(l, n) - i - 1), z[i, Min(l, n) - i - 1:])),
        plausible=True)

    i_ = Symbol("i", domain=Range(Min(l, n)))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq.eq_lamda, i_)

    j_ = Symbol("j", domain=Range(Min(l, n)))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j_)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.apply(Algebra.EqAdd.Is.Eq_Sub, lhs=0)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite_Ite.eq.Ite__Ite)

    j = Symbol(integer=True)
    Eq << Eq[0][i, j + Min(l, n) - i - 1]

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, 0, i + 1))

    Eq.zi_min_def = Eq[-1].this.find(Stack)(j).find(Symbol < 0).simplify()

    Eq << Eq.eq_lamda.subs(Eq.zi_min_def)

    Eq << Algebra.EqReducedArgMax.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Tensor.ReducedArgMax.eq.Stack.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq << Eq[-1].subs(Eq.zi_min_def.reversed)

    Eq << Eq[-1].this.lhs.apply(Tensor.ReducedArgMax.eq.Stack.ReducedArgMax)

    Eq << Eq[-1].this.apply(Algebra.EqAdd.Is.Eq_Sub, rhs=slice(0, 2)).reversed

    Eq << Eq[-1].this.lhs.apply(Tensor.Stack.eq.Add)

    Eq << Eq[-1].this.apply(Algebra.EqAdd.Is.Eq_Sub, lhs=-1)

    Eq << Eq.eq_reducedArgMax.subs(Eq[-1])

    Eq << Eq[-1].this.find(Stack + Stack).apply(Tensor.Add_Stack.eq.Stack_Add)

    Eq << Eq[-1].this.find(BlockMatrix).apply(Tensor.Block.eq.Stack.Ite)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Add)

    Eq << Eq[-1].this.find(Stack[2]).apply(Tensor.Stack.eq.ReducedArgMax)

    Eq << Eq[-1].this.apply(Algebra.EqAdd.Is.Eq_Sub, rhs=3)

    Eq << Eq[-1].this.find(ReducedArgMax).arg.definition





if __name__ == '__main__':
    run()
# created on 2022-01-03

# updated on 2023-05-20

from . import tf
