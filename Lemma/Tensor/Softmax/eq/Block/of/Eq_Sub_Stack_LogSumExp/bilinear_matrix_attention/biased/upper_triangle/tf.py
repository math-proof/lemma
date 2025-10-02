from util import *


@apply
def apply(eq):
#   (H, ((((Q, i), W, (K, (  i , (  i , (n, u))))), (  i ,   0 ,   n - Min(n, u) + 1) ), ((  Q[i + n - Min(n, u) + 1] ,   W ,   K[i + n - Min(n, u) + 1:].T ), (  i ,   0 ,   Min(n, u) - 1 ))), (((  Q[i] ,   W ,   K[i:Min(n, i + u)].T ),   H[i] ), (  i ,   0 ,   n ))), z
    (H, ((((Q, i), W, (K, (S[i], (S[i], (n, u))))), (S[i], S[0], S[n - Min(n, u) + 1])), ((S[Q[i + n - Min(u, n) + 1]], S[W], S[K[i + n - Min(n, u) + 1:].T]), (S[i], S[0], S[Min(u, n) - 1]))), (((S[Q[i]], S[W], S[K[i:Min(n, i + u)].T]), S[H[i]]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[1][Expr, Zeros] + BlockMatrix[
                Stack[Indexed @ Expr @ Transpose[Sliced[Tuple[Add[Min]]]]],
                Stack[
                    BlockMatrix[
                        MatMul,
                        NegativeInfinity * Ones
                    ],
                ]
            ] - Stack[Ones * Log[ReducedSum[Exp[MatMul + BlockMatrix[Expr, Zeros]]]]]])
    assert n >= 2 and u >= 2
    breadth = Min(u, n) - 1
    return Equal(softmax(Q @ W @ K.T + H * Identity(n) + (BandPart[0, u - 1](Ones(n, n)) - 1) * oo),
                 BlockMatrix(
                     Stack[i:n - breadth](BlockMatrix(Zeros(i), Exp(z[i]), Zeros(n - 1 - i - breadth))),
                     Stack[i:breadth](BlockMatrix(Zeros(n - breadth + i), Exp(z[i + n - breadth, :breadth - i])))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Logic

    n, u = Symbol(domain=Range(2, oo))
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    W = Symbol(shape=(d_z, d_z), real=True)
    H = Symbol(shape=(n,), real=True)
    z = Symbol(shape=(n, Min(u, n)), real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](H, Zeros(n, Min(u, n) - 1)) + BlockMatrix(
            Stack[i:n - Min(u, n) + 1](Q[i] @ W @ K[i:i + Min(u, n)].T),
            Stack[i:Min(u, n) - 1](BlockMatrix(Q[i + n - Min(u, n) + 1] @ W @ K[n - Min(u, n) + i + 1:].T, -oo * Ones(i + 1)))) - Stack[i:n](Ones(Min(u, n)) * Log(ReducedSum(Exp(Q[i] @ W @ K[i:Min(n, i + u)].T + BlockMatrix(H[i], Zeros(Min(n - i, u) - 1))))))))

    A = Symbol(Eq[1].find(MatMul))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i]#[i:i + Min(u, n)]

    Eq << Logic.AllIn.of.All.apply(Eq[-1], (i, 0, n + 1 - Min(u, n)))

    Eq << Algebra.All.Eq.Slice.of.All_Eq.apply(Eq[-1], slice(i, i + Min(u, n)))

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1])

    Eq << Eq.A_def[i][i:Min(n, i + u)]

    Eq << Eq.A_def[i + n + 1 - Min(u, n)][i + n + 1 - Min(u, n):]

    Eq << Eq[0].subs(Eq[-1].reversed, Eq[-2].reversed, Eq[-3].reversed)

    Eq << Tensor.Softmax.eq.Block.of.Eq_Sub_Stack_Mul_LogSumExp.biased.upper_triangle.tf.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.A_def)





if __name__ == '__main__':
    run()
# created on 2022-01-04
# updated on 2022-03-14
