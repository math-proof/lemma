from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], (n, u)))), (S[i], S[0], (S[1], S[n],  S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u) + 1]), (S[i + n - Min(n, u) + 1], S[n])), (S[i], S[0], (n, u)))), (S[A[i][i:Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Stack[Sliced[Indexed, Tuple[Add[Min]]], Tuple[Add]],
            Stack[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * Ones],
                Tuple[Min - 1]]] - Stack[Ones * logsumexp]])

    assert n >= 2 and u >= 2
    return Equal(ReducedArgMax(softmax(A + (BandPart[0, u - 1](Ones(n, n)) - 1) * oo)) - Stack[i:n](i), ReducedArgMax(z))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra

    n, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, Min(u, n)), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix(
            Stack[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Stack[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * Ones(i + 1)))) - Stack[i:n](Ones(Min(u, n)) * logsumexp(A[i, i:Min(n, i + u)]))))

    Eq << Tensor.Softmax.eq.Block.of.Eq_Sub_Stack_Mul_LogSumExp.upper_triangle.tf.apply(Eq[0])

    z_quote = Symbol(Eq[-1].lhs)
    Eq << Eq[-1].subs(z_quote.this.definition.reversed)

    Eq << Algebra.EqReducedArgMax.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedArgMax.eq.Block.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax).apply(Tensor.ReducedArgMax.eq.Stack.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[Stack]).apply(Tensor.ReducedArgMax.eq.Stack.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(BlockMatrix).apply(Tensor.Block.eq.Stack.Ite)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Ite.eq.SubIte)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.eq.Add)

    Eq.eq_reducedArgMax = Eq[-1].this.find(Stack[Piecewise]).apply(Tensor.Stack.Ite.eq.Block)

    Eq.eq_lamda = Equal(
        Stack[i:Min(u, n) - 1](z[i + n + 1 - Min(n, u)]),
        Stack[i:Min(u, n) - 1](BlockMatrix(z[i + n + 1 - Min(n, u), :Min(u, n) - i - 1], -oo * Ones(i + 1))),
        plausible=True)

    i_ = Symbol("i", domain=Range(Min(u, n) - 1))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq.eq_lamda, i_)

    j_ = Symbol("j", domain=Range(Min(u, n)))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j_)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, 0)

    j = Symbol(integer=True)
    Eq << Eq[0][i + n + 1 - Min(n, u), j - i]

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, i, Min(u, n) - 1))

    Eq.zi_min_def = Eq[-1].this(i).find(Stack)(j).find(Add < Min - 1).simplify()

    Eq << Eq.eq_lamda.subs(Eq.zi_min_def)

    Eq << Algebra.EqReducedArgMax.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Tensor.ReducedArgMax.eq.Stack.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq << Eq[-1].subs(Eq.zi_min_def.reversed)

    Eq << Eq[-1].this.lhs.apply(Tensor.ReducedArgMax.eq.Stack.ReducedArgMax, simplify=None).reversed

    Eq << Eq.eq_reducedArgMax.subs(Eq[-1])

    Eq << Eq[-1].this.find(BlockMatrix).apply(Tensor.Block.eq.Stack.Ite)

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, rhs=0)

    Eq << Eq[-1].this.rhs.apply(Tensor.Stack.eq.ReducedArgMax)

    Eq << Eq[-1].this.lhs.find(ReducedArgMax).arg.definition





if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-18
