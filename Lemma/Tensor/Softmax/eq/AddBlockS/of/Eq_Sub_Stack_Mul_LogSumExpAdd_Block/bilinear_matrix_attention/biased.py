from util import *


@apply
def apply(eq):
#   (H, (((((Q, i), W, (K, (  0 ,   i ))), (  i ,   0 , (l, n))), ((  Q[i + Min(l, n)] ,   W ,   K[i + 1:i + Min(l, n)].T ), (  i ,   0 ,   n - Min(l, n) ))), (((  Q[i] ,   W , (  K , (  i , (  i , (  n,  u))))), (  i ,   0 ,   n - Min(n, u) )), ((  Q[i + n - Min(n, u)] ,   W ,   K[i + n - Min(n, u):].T) , (  i ,   0 ,   Min(n, u)])))), (((  Q[i] ,   W ,   K[relu(i - l + 1):Min(n, i + u)].T ),   H[i] ), (  i ,   0 ,   n ))), z
    (H, (((((Q, i), W, (K, (S[0], S[i]))), (S[i], S[0], (l, n))), ((S[Q[i + Min(l, n)]], S[W], S[K[i + 1:i + Min(l, n)].T]), (S[i], S[0], S[n - Min(l, n)]))), (((S[Q[i]], S[W], (S[K], (S[i], (S[i], (S[n], u))))), (S[i], S[0], S[n - Min(n, u)])), ((S[Q[i + n - Min(n, u)]], S[W], S[K[i + n - Min(n, u):].T]), (S[i], S[0], S[Min(n, u)])))), (((S[Q[i]], S[W], S[K[relu(i - l + 1):Min(n, i + u)].T]), S[H[i]]), (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[1][Zeros, Expr, Zeros] + BlockMatrix[1][
            BlockMatrix[
                Stack[
                    BlockMatrix[
                        NegativeInfinity * Ones,
                        Indexed @ Expr @ Transpose[Sliced]
                    ],
                    Tuple[Min]
                ],
                Stack[MatMul]
            ],
            BlockMatrix[
                Stack[MatMul[Transpose[Sliced[Tuple[Add[Min]]]]]],
                Stack[
                    BlockMatrix[
                        MatMul,
                        NegativeInfinity * Ones
                    ]
                ]
            ]
        ] - Stack[Ones * Log[ReducedSum[Exp[MatMul + BlockMatrix[Zeros, Expr, Zeros]]]]]])
    assert n >= 2 and u >= 2 and l >= 2
    breadth = Add(Min(l, n), Min(u, n), -1)
    return Equal(softmax(Q @ W @ K.T + H * Identity(n) + (BandPart[l - 1, u - 1](Ones(n, n)) - 1) * oo),
                 BlockMatrix(
                    Stack[i:Min(l, n)](BlockMatrix(Exp(z[i, Min(l, n) - i - 1:Min(l, n) - 1]), Zeros(n - i))),
                    Stack[i:n - Min(l, n)](BlockMatrix(Zeros(i + 1), Exp(z[i + Min(l, n), :Min(l, n) - 1]), Zeros(n - i - Min(l, n))))
                 ) + BlockMatrix(
                    Stack[i:n - Min(u, n)](BlockMatrix(Zeros(i), Exp(z[i, Min(l, n) - 1:]), Zeros(n - i - Min(u, n)))),
                    Stack[i:Min(u, n)](BlockMatrix(Zeros(n - Min(u, n) + i), Exp(z[i + n - Min(u, n), Min(l, n) - 1:breadth - i])))
                 ))


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Bool

    n, l, u = Symbol(domain=Range(2, oo))
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    W = Symbol(shape=(d_z, d_z), real=True)
    H = Symbol(shape=(n,), real=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](Zeros(n, Min(l, n) - 1), H, Zeros(n, Min(u, n) - 1)) + BlockMatrix[1](
        BlockMatrix(
            Stack[i:Min(l, n)](BlockMatrix(-oo * Ones(Min(l, n) - i - 1), Q[i] @ W @ K[:i].T)),
            Stack[i:n - Min(l, n)](Q[i + Min(l, n)] @ W @ K[i + 1:i + Min(l, n)].T)
        ),
        BlockMatrix(
            Stack[i:n - Min(u, n)](Q[i] @ W @ K[i:i + Min(u, n)].T),
            Stack[i:Min(u, n)](BlockMatrix(Q[i + n - Min(u, n)] @ W @ K[n - Min(u, n) + i:].T, -oo * Ones(i)))
        )) - Stack[i:n](Ones(breadth) * Log(ReducedSum(Exp(Q[i] @ W @ K[relu(i + 1 - l):Min(n, i + u)].T + BlockMatrix(Zeros(i - relu(i - l + 1)), H[i], Zeros(-i + Min(n, i + u) - 1))))))))

    A = Symbol(Eq[1].find(MatMul))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i]#[i:i + Min(u, n)]

    Eq << Bool.AllIn.of.All.apply(Eq[-1], (i, 0, n - Min(u, n)))

    Eq << Algebra.All.Eq.Slice.of.All_Eq.apply(Eq[-1], slice(i, i + Min(u, n)))

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1])

    Eq << Eq.A_def[i][:i]

    Eq << Eq.A_def[i + Min(l, n)][i + 1:i + Min(l, n)]

    Eq << Eq.A_def[i + n - Min(u, n)][i + n - Min(u, n):]

    Eq << Eq.A_def[i][relu(i + 1 - l):Min(n, i + u)]

    Eq << Eq[0].subs(Eq[-1].reversed, Eq[-2].reversed, Eq[-3].reversed, Eq[-4].reversed, Eq[-5].reversed)

    Eq << Tensor.Softmax.eq.AddBlockS.of.Eq_Sub_Stack_Mul_LogSumExpAdd_Block.biased.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.A_def)





if __name__ == '__main__':
    run()
# created on 2022-01-04
# updated on 2022-03-15




