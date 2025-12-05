from util import *


@apply
def apply(eq):
    (H, ((((A, i), (S[i], (S[i], u))), (S[i], S[0], (n, S[u]))), (A[i + n - u, i + n - u:], (S[i], S[0], S[u]))), ((H[i], A[i, i:Min(n, i + u)]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[1][Expr, Zeros] + BlockMatrix[
                Stack[Sliced[Indexed, Tuple[Add]], Tuple[Expr - Expr]],
                Stack[BlockMatrix[NegativeInfinity * Ones]]
            ] - Stack[Ones * Log[ReducedSum[Exp[Add[BlockMatrix[Expr, Zeros]]]]]]])
    assert n >= 2 and u >= 2 and u <= n

    return Equal(softmax(A + H * Identity(n) + (BandPart[0, u - 1](Ones(n, n)) - 1) * oo),
                 BlockMatrix(
                     Stack[i:n - u](BlockMatrix(Zeros(i), Exp(z[i]), Zeros(n - i - u))),
                     Stack[i:u](BlockMatrix(Zeros(n - u + i), Exp(z[i + n - u, :u - i])))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Bool, Int, Nat

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    H = Symbol(shape=(n,), real=True)
    z = Symbol(shape=(n, u), real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](H, Zeros(n, u - 1)) + BlockMatrix(
            Stack[i:n - u](A[i, i:i + u]),
            Stack[i:u](BlockMatrix(A[i + n - u, n - u + i:], -oo * Ones(i)))) - Stack[i:n](Ones(u) * Log(ReducedSum(Exp(A[i, i:Min(n, i + u)] + BlockMatrix(H[i], Zeros(Min(n - i, u) - 1))))))))

    Eq << Eq[0].this.find(BlockMatrix[1]).apply(Algebra.Block.split, n - Min(u, n))

    Eq << Add(*Eq[-1].find(Add[BlockMatrix]).args[:2]).this.apply(Algebra.Add.Block.eq.Block)

    Eq.z_def = Eq[-2].subs(Eq[-1])

    A = Symbol(Add(*Eq[1].lhs.arg.args[:2]))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i + n - Min(u, n)][i + n - Min(u, n):]

    Eq << Eq[-1].this.find(Mul[Stack]).apply(Tensor.Expr.eq.Stack, simplify=None)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Mul.Stack)

    Eq << Eq[-1].this.find(Stack).apply(Tensor.Stack.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(Algebra.Mul.eq.Block)

    Eq.matmul_subs = Eq[-1].this.apply(Int.EqAdd.Is.Eq_Sub, rhs=0).reversed

    Eq << Eq.z_def.rhs.find(Add[2]).this.args[0].apply(Tensor.Expr.eq.Stack, i)

    Eq << Eq[-1].this.rhs.apply(Tensor.Add_Stack.eq.Stack_Add)

    Eq << Eq[-1].this.rhs.subs(Eq.matmul_subs)

    Eq << Eq[-1].this.rhs.find(Add).apply(Tensor.Expr.eq.Stack)

    Eq << Eq[-1].this.rhs.find(-Piecewise).apply(Nat.Mul_Ite.eq.Ite_MulS)

    Eq << Eq[-1].this.rhs.find(Add).apply(Nat.AddIteS.eq.IteAnd)

    Eq << Eq[-1].this.find(Piecewise).apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite, 1)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Nat.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.find(Piecewise).apply(Bool.Ite_Ite.eq.Ite__Ite)

    Eq.lower_part = Eq[-1].this.rhs.apply(Tensor.Stack.Ite.eq.Stack.Block)

    Eq << Eq.A_def[i]#[i:i + Min(u, n)]

    Eq << Bool.AllIn.of.All.apply(Eq[-1], (i, 0, n - Min(u, n)))

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

    Eq << Tensor.Softmax.eq.Block.of.Eq_SubBlock__Stack_Mul_LogSumExp.upper_triangle.apply(Eq[-1])

    Eq << Eq[-1].this.find(Symbol).definition





if __name__ == '__main__':
    run()
# created on 2022-03-13
# updated on 2023-09-17

