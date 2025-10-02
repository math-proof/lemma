from util import *


@apply
def apply(eq_C, eq_V, eq_V_quote, eq):
    ((w, (k, (r_relative, S[-k], S[k]))), j_limit, i_limit), V = eq_V.of(Equal[Stack[Indexed[Symbol, Add[clip]]]])

    j, S[0], n = j_limit
    i, S[0], S[n] = i_limit

    (r, S[j]), (S[r], S[i]) = r_relative.of(Indexed - Indexed)

    ((S[w], clip_index), (S[j], S[0], l), S[i_limit]), V_quote = eq_V_quote.of(Equal[Stack[Indexed]])
    S[k], (((S[r], S[Min(j + relu(i - l + 1), n - 1)]), (S[r], S[i])), S[-k], S[k]) = clip_index.of(Add[clip[Indexed - Indexed]])
    (C, S[C]), C_quote = eq_C.of(Equal[Mul[Transpose[Ones * ReducedSum[Expr ** 2] ** (1 / 2)] ** -1]])

    ((((S[V_quote[i, :i + 1] * (1 + C_quote[i] @ C_quote[:i + 1].T)], ((A, i), (S[0], S[i + 1]))), (S[i], S[0], S[l - 1])), (S[V_quote[l - 1:] * Stack[i:n - l + 1](1 + C_quote[i + l - 1] @ C_quote[i:i + l].T)], (A[i + l - 1, i:i + l], (S[i], S[0], S[n - l + 1])))), ((S[V_quote[i, :Min(i + 1, l)] * (1 + C_quote[i] @ C_quote[relu(i - l + 1):i + 1].T)], A[i, relu(i + 1 - l):i + 1]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[
                Stack[
                    BlockMatrix[
                        NegativeInfinity * Ones,
                        Add[Sliced[Indexed]]
                        ],
                ],
                Add[Stack]
            ] - Stack[Ones * Log[ReducedSum[Exp[Add]]]]
        ]
    )

    assert n >= 2 and l >= 2 and l <= n

    return Equal(softmax(A + V * (1 + C_quote @ C_quote.T) + (BandPart[l - 1, 0](Ones(n, n)) - 1) * oo),
                 BlockMatrix(
                     Stack[i:l - 1](BlockMatrix(Exp(z[i, l - i - 1:]), Zeros(n - 1 - i))),
                     Stack[i:n - l + 1](BlockMatrix(Zeros(i), Exp(z[i + l - 1]), Zeros(n - i - l)))))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra

    n, k, d = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    V = Symbol(shape=(n, n), real=True)
    z, V_quote = Symbol(shape=(n, l), real=True)
    C, C_quote = Symbol(shape=(n, d), real=True)
    r = Symbol(shape=(n,), integer=True)
    w = Symbol(shape=(k * 2 + 1,), integer=True)
    i, j = Symbol(integer=True)
    Eq << apply(
        Equal(C_quote, C / (sqrt(ReducedSum(C * C) * Ones(d, n))).T),
        Equal(V, Stack[j:n, i:n]((w[k + clip(r[j] - r[i], -k, k)]))),
        Equal(V_quote, Stack[j:l, i:n](w[k + clip(r[Min(n - 1, relu(i - l + 1) + j)] - r[i], -k, k)])),
        Equal(z, BlockMatrix(
            Stack[i:l - 1](BlockMatrix(-oo * Ones(l - i - 1), A[i, :i + 1] + V_quote[i, :i + 1] * (1 + C_quote[i] @ C_quote[:i + 1].T))),
            V_quote[l - 1:] * Stack[i:n - l + 1](1 + C_quote[i + l - 1] @ C_quote[i:i + l].T) + Stack[i:n - l + 1](A[i + l - 1, i:i + l])) - Stack[i:n](Ones(l) * Log(ReducedSum(Exp(A[i, relu(i + 1 - l):i + 1] + V_quote[i, :Min(i + 1, l)] * (1 + C_quote[i] @ C_quote[relu(i - l + 1):i + 1].T)))))))

    Eq << Tensor.All.Eq.of.Eq_Block.Eq_Block.relative_distance.lower_triangle.upper_part.tf.apply(Eq[1], Eq[2])

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1].this.expr.reversed, Eq[3].find(Stack).expr)

    Eq << Tensor.All.Eq.of.Eq_Block.Eq_Block.relative_distance.lower_triangle.lower_part.tf.apply(Eq[1], Eq[2])

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1].this.expr.reversed)

    Eq << Tensor.Eq.of.Eq_Block.Eq_Block.relative_distance.lower_triangle.apply(Eq[1], Eq[2])

    Eq.z_def = Eq[3].subs(Eq[-1].reversed, Eq[-2], Eq[-4])

    C = Symbol(C_quote @ C_quote.T + 1)
    Eq.C_def = C.this.definition

    Eq << Eq.C_def[i, :i + 1]

    Eq << Eq.C_def[i + l - 1, i:i + l]

    Eq << Eq.C_def[i, relu(i + 1 - l):i + 1]

    Eq << Eq.z_def.subs(Eq[-1].reversed, Eq[-2].reversed, Eq[-3].reversed)

    Eq << Eq[-1].this.find(Stack * Stack).apply(Tensor.Mul.Stack.eq.Stack)

    Eq << Eq[-1].this.find(Stack + Stack).apply(Tensor.Add_Stack.eq.Stack_Add)

    Eq << Eq[-1].this.find(-~Min).apply(Tensor.Min.eq.Add.Relu, index=1)

    A_quote = Symbol(A + V * C)
    Eq.A_quote_def = A_quote.this.definition

    Eq << Eq.A_quote_def[i][:i + 1]

    Eq << Eq.A_quote_def[i + l - 1][i:i + l]

    Eq << Eq.A_quote_def[i][relu(i + 1 - l):i + 1]

    Eq << Eq[-4].subs(Eq[-1].reversed, Eq[-2].reversed, Eq[-3].reversed)

    Eq << Tensor.Softmax.eq.Block.of.Eq_Sub_Stack_Mul_LogSumExp.lower_triangle.tf.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.A_quote_def)

    Eq << Eq[-1].subs(Eq.C_def)




if __name__ == '__main__':
    run()
# created on 2022-04-02
# updated on 2023-05-19
