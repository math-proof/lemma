from util import *


@apply
def apply(eq):
    (H, ((((Q, i), W, (K, (S[0], S[i + 1]))), (S[i], S[0], l)), ((S[Q[i + l]], S[W], S[K[i + 1:i + l + 1].T]), (S[i], S[0], (n, S[l])))), (((S[Q[i]], S[W], S[K[relu(i - l + 1):i + 1].T]), S[H[i]]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[1][Zeros, Expr] + BlockMatrix[
                Stack[
                    BlockMatrix[
                        NegativeInfinity * Ones,
                        Indexed @ Expr @ Transpose[Sliced]
                    ],
                ],
                Stack[MatMul, Tuple[Expr - Expr]]
            ] - Stack[Ones * Log[ReducedSum[Exp[MatMul + BlockMatrix[Zeros, Expr]]]]]])
    assert n >= 2 and l >= 2 and l <= n
    return Equal(softmax(Q @ W @ K.T + H * Identity(n) + (BandPart[l - 1, 0](Ones(n, n)) - 1) * oo),
                 BlockMatrix(
                     Stack[i:l](BlockMatrix(Exp(z[i, l - i - 1:]), Zeros(n - 1 - i))),
                     Stack[i:n - l](BlockMatrix(Zeros(i + 1), Exp(z[i + l]), Zeros(n - 1 - i - l)))))


@prove
def prove(Eq):
    from Lemma import Tensor

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    d_z = Symbol(integer=True, positive=True)
    Q, K = Symbol(shape=(n, d_z), real=True)
    W = Symbol(shape=(d_z, d_z), real=True)
    H = Symbol(shape=(n,), real=True)
    z = Symbol(shape=(n, l), real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](Zeros(n, l - 1), H) + BlockMatrix(
            Stack[i:l](BlockMatrix(-oo * Ones(l - i - 1), Q[i] @ W @ K[:i + 1].T)),
            Stack[i:n - l](Q[i + l] @ W @ K[i + 1:i + l + 1].T)) - Stack[i:n](Ones(l) * Log(ReducedSum(Exp(Q[i] @ W @ K[relu(i + 1 - l):i + 1].T + BlockMatrix(Zeros(Min(i, l - 1)), H[i])))))))

    A = Symbol(Eq[1].find(MatMul))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i][:i + 1]

    Eq << Eq.A_def[i + Min(l, n)][i + 1:i + Min(l, n) + 1]

    Eq << Eq.A_def[i][relu(i + 1 - l):i + 1]

    Eq << Eq[0].subs(Eq[-1].reversed, Eq[-2].reversed, Eq[-3].reversed)

    Eq << Tensor.EqSoftmax.of.Eq_SubAddBlockS__Stack_Mul_LogSumExp.biased_lower_triangle.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.A_def)





if __name__ == '__main__':
    run()
# created on 2022-01-04

# updated on 2022-03-29
