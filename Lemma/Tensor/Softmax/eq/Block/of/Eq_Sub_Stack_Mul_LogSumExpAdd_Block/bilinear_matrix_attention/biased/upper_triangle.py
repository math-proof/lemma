from util import *


@apply
def apply(eq):
    (H, ((((Q, i), W, (K, (S[i], (S[i], u)))), (S[i], S[0], (n, S[u]))), ((Q[i + n - u], S[W], S[K[i + n - u:].T]), (S[i], S[0], S[u]))), (((Q[i], S[W], S[K[i:Min(n, i + u)].T]), H[i]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[1][Expr, Zeros] + BlockMatrix[
                Stack[
                    Indexed @ Expr @ Transpose[Sliced[Tuple[Add]]],
                    Tuple[Expr - Expr]
                ],
                Stack[
                    BlockMatrix[
                        MatMul,
                        NegativeInfinity * Ones
                    ],
                ]
            ] - Stack[Ones * logsumexp[MatMul + BlockMatrix[Expr, Zeros]]]])
    assert n >= 2 and u >= 2 and u <= n

    return Equal(softmax(Q @ W @ K.T + H * Identity(n) + (BandPart[0, u - 1](Ones(n, n)) - 1) * oo),
                 BlockMatrix(
                     Stack[i:n - u](BlockMatrix(Zeros(i), Exp(z[i]), Zeros(n - i - u))),
                     Stack[i:u](BlockMatrix(Zeros(n - u + i), Exp(z[i + n - u, :u - i])))))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Logic

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    W = Symbol(shape=(d_z, d_z), real=True)
    H = Symbol(shape=(n,), real=True)
    z = Symbol(shape=(n, u), real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](H, Zeros(n, u - 1)) + BlockMatrix(
            Stack[i:n - u](Q[i] @ W @ K[i:i + u].T),
            Stack[i:u](BlockMatrix(Q[i + n - u] @ W @ K[n - u + i:].T, -oo * Ones(i)))) - Stack[i:n](Ones(u) * logsumexp((Q[i] @ W @ K[i:Min(n, i + u)].T + BlockMatrix(H[i], Zeros(Min(n - i, u) - 1)))))))

    A = Symbol(Eq[1].find(MatMul))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i]#[i:i + Min(u, n)]

    Eq << Logic.AllIn.of.All.apply(Eq[-1], (i, 0, n - Min(u, n)))

    Eq << Algebra.All.Eq.Slice.of.All_Eq.apply(Eq[-1], slice(i, i + Min(u, n)))

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1])

    Eq << Eq.A_def[i + n - Min(u, n)][i + n - Min(u, n):]

    Eq << Eq.A_def[i][i:Min(n, i + u)]

    Eq << Eq[0].subs(Eq[-1].reversed, Eq[-2].reversed, Eq[-3].reversed)

    Eq << Tensor.Softmax.eq.Block.of.Eq_Sub_Stack_Mul_LogSumExpAddBlock.biased.upper_triangle.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.A_def)





if __name__ == '__main__':
    run()
# created on 2022-01-04
# updated on 2022-03-30

