from util import *


@apply
def apply(eq_V, eq_V_quote):
    ((w, (k, (r_relative, S[-k], S[k]))), j_limit, i_limit), V = eq_V.of(Equal[Stack[Indexed[Symbol, Add[clip]]]])

    j, S[0], n = j_limit
    i, S[0], S[n] = i_limit

    (r, S[j]), (S[r], S[i]) = r_relative.of(Indexed - Indexed)

    ((S[w], clip_index), (S[j], S[0], l), S[i_limit]), V_quote = eq_V_quote.of(Equal[Stack[Indexed]])
    S[k], (((S[r], S[Min(j + relu(i - l + 1), n - 1)]), (S[r], S[i])), S[-k], S[k]) = clip_index.of(Add[clip[Indexed - Indexed]])

    assert n >= 2 and l >= 2 and l <= n

    return Equal(V[i, i + 1 - Min(i + 1, l): i + 1], V_quote[i, :Min(i + 1, l)])


@prove
def prove(Eq):
    from Lemma import Algebra, Tensor, Logic

    n, k = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    V = Symbol(shape=(n, n), real=True)
    V_quote = Symbol(shape=(n, l), real=True)
    r = Symbol(shape=(n,), integer=True)
    w = Symbol(shape=(k * 2 + 1,), integer=True)
    i, j = Symbol(integer=True)
    Eq << apply(
        Equal(V, Stack[j:n, i:n]((w[k + clip(r[j] - r[i], -k, k)]))),
        Equal(V_quote, Stack[j:l, i:n](w[k + clip(r[Min(n - 1, relu(i - l + 1) + j)] - r[i], -k, k)])))

    Eq <<= Eq[0][i]

    Eq <<= Logic.AllIn.of.All.apply(Eq[-1], (i, 0, n), simplify=None)

    Eq << Algebra.All.Eq.Slice.of.All_Eq.apply(Eq[-1], slice(i + 1 - Min(i + 1, l), i + 1))

    Eq << Eq[-1].this.rhs.find(~Indexed - Indexed).args[1].apply(Algebra.Expr.eq.IteGe, upper=n - 1)

    Eq << Eq[-1].this(i).rhs(j).find(GreaterEqual).simplify()

    Eq.V_relu = Eq[-1].this.rhs.find(-~Min).apply(Tensor.Min.eq.Add.Relu, index=1)

    Eq << Eq[1][i]

    Eq << Logic.AllIn.of.All.apply(Eq[-1], (i, 0, n), simplify=None)

    Eq << Algebra.All.Eq.Slice.of.All_Eq.apply(Eq[-1], slice(0, Min(i + 1, l)))

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq.V_relu, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-03-17
# updated on 2023-05-15
