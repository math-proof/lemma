from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], u))), (S[i], S[0], (n,  S[u]))), (((S[A], S[i + n - u]), (S[i + n - u], S[n])), (S[i], S[0], S[u]))), (A[i, i:Min(n, i + u)], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Stack[
                Sliced[Indexed, Tuple[Add]],
                Tuple[Expr - Expr]
            ],
            Stack[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * Ones],
            ]
        ] - Stack[Ones * logsumexp]])

    assert n >= 2 and u >= 2 and u <= n
    return Equal(ReducedArgMax(softmax(A + (BandPart[0, u - 1](Ones(n, n)) - 1) * oo)) - Stack[i:n](i), ReducedArgMax(z))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, u), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix(
            Stack[i:n - u](A[i, i:i + u]),
            Stack[i:u](BlockMatrix(A[i + n - u, n - u + i:], -oo * Ones(i)))) - Stack[i:n](Ones(u) * logsumexp(A[i, i:Min(n, i + u)]))))

    Eq << Tensor.Softmax.eq.Block.of.Eq_SubBlock__Stack_Mul_LogSumExp.upper_triangle.apply(Eq[0])

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
        Stack[i:Min(u, n)](z[i + n - Min(n, u)]),
        Stack[i:Min(u, n)](BlockMatrix(z[i + n - Min(n, u), :Min(u, n) - i], -oo * Ones(i))),
        plausible=True)

    i_ = Symbol("i", domain=Range(Min(u, n)))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq.eq_lamda, i_)

    j_ = Symbol("j", domain=Range(Min(u, n)))
    Eq << Tensor.Eq.given.All_EqGetS.apply(Eq[-1], j_)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, lhs=0)

    j = Symbol(integer=True)
    Eq << Eq[0][i + n - Min(n, u), j - i]

    Eq << Tensor.EqStackS.of.Eq.apply(Eq[-1], (j, i, Min(u, n)))

    Eq.zi_min_def = Eq[-1].this(i).find(Stack)(j).find(Add < Symbol).simplify()

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
# updated on 2023-05-20

from . import tf
