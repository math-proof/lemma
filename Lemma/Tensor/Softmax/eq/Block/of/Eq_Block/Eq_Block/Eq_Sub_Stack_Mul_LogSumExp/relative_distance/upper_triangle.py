from util import *


@apply
def apply(eq_V, eq_V_quote, eq):
    ((w, (k, (r_relative, S[-k], S[k]))), j_limit, i_limit), V = eq_V.of(Equal[Stack[Indexed[Symbol, Add[clip]]]])

    j, S[0], n = j_limit
    i, S[0], S[n] = i_limit

    (r, S[j]), (S[r], S[i]) = r_relative.of(Indexed - Indexed)

    ((S[w], clip_index), (S[j], S[0], u), S[i_limit]), V_quote = eq_V_quote.of(Equal[Stack[Indexed]])
    S[k], (((S[r], S[Min(j + i, n - 1)]), (S[r], S[i])), S[-k], S[k]) = clip_index.of(Add[clip[Indexed - Indexed]])

    (((V_quote[:n - u], (((A, S[i]), (S[i], S[i + u])), (S[i], S[0], S[n - u]))), ((A[i + n - u, i + n - u:], V_quote[i + n - u, :u - i]), (S[i], S[0], S[u]))), ((A[i, i:Min(n, i + u)], V_quote[i, :Min(n, i + u) - i]), (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Expr + Stack[Sliced[Indexed]],
            Stack[
                BlockMatrix[
                    Add,
                    NegativeInfinity * Ones
                ]
            ]
        ] - Stack[Ones * Log[ReducedSum[Exp[Add]]]]])

    assert n >= 2 and u >= 2 and u <= n

    return Equal(softmax(A + V + (BandPart[0, u - 1](Ones(n, n)) - 1) * oo), BlockMatrix(
        Stack[i:n - u](BlockMatrix(Zeros(i), Exp(z[i]), Zeros(n - i - u))),
        Stack[i:u](BlockMatrix(Zeros(n - u + i), Exp(z[i + n - u, :u - i])))))

@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Bool

    n, k = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    V = Symbol(shape=(n, n), real=True)
    z, V_quote = Symbol(shape=(n, u), real=True)
    r = Symbol(shape=(n,), integer=True)
    w = Symbol(shape=(k * 2 + 1,), integer=True)
    i, j = Symbol(integer=True)
    Eq << apply(
        Equal(V, Stack[j:n, i:n]((w[k + clip(r[j] - r[i], -k, k)]))),
        Equal(V_quote, Stack[j:u, i:n](w[k + clip(r[Min(n - 1, i + j)] - r[i], -k, k)])),
        Equal(z, BlockMatrix(
            V_quote[:n - u] + Stack[i:n - u](A[i, i:i + u]),
            Stack[i:u](BlockMatrix(A[i + n - u, n - u + i:] + V_quote[i + n - u, :u - i], -oo * Ones(i)))) - Stack[i:n](Ones(u) * Log(ReducedSum(Exp(A[i, i:Min(n, i + u)] + V_quote[i, :Min(n, i + u) - i]))))))

    Eq << Tensor.All.Eq.of.Eq_Block.Eq_Block.relative_distance.upper_triangle.lower_part.apply(Eq[0], Eq[1])

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1].this.expr.reversed, Eq[2].find(Stack).expr)

    Eq << Tensor.All.Eq.of.Eq_Block.Eq_Block.relative_distance.upper_triangle.upper_part.apply(Eq[0], Eq[1])

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1].this.expr.reversed)

    Eq << Tensor.Eq.of.Eq_Block.Eq_Block.relative_distance.upper_triangle.apply(Eq[0], Eq[1])

    Eq << Eq[2].subs(Eq[-1].reversed, Eq[-2], Eq[-4])

    Eq.z_def = Eq[-1].this.find(Stack + Stack).apply(Tensor.Add_Stack.eq.Stack_Add)

    A_quote = Symbol(A + V)
    Eq.A_quote_def = A_quote.this.definition

    Eq << Eq.A_quote_def[i]#[i:i + u]

    Eq << Bool.AllIn.of.All.apply(Eq[-1], (i, 0, n - u))

    Eq << Algebra.All.Eq.Slice.of.All_Eq.apply(Eq[-1], slice(i, i + u))

    Eq << Tensor.EqStackS.of.All_Eq.apply(Eq[-1])

    Eq << Eq.A_quote_def[i + n - u][i + n - u:]

    Eq << Eq.A_quote_def[i][i:Min(n, i + u)]

    Eq << Eq.z_def.subs(Eq[-1].reversed, Eq[-2].reversed, Eq[-3].reversed)

    Eq << Tensor.Softmax.eq.Block.of.Eq_SubBlock__Stack_Mul_LogSumExp.upper_triangle.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.A_quote_def)




if __name__ == '__main__':
    run()
# created on 2022-03-30

