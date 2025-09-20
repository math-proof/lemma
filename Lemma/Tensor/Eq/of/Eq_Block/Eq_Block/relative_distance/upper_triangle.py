from util import *


@apply
def apply(eq_V, eq_V_quote):
    ((w, (k, (r_relative, S[-k], S[k]))), j_limit, i_limit), V = eq_V.of(Equal[Stack[Indexed[Symbol, Add[clip]]]])

    j, S[0], n = j_limit
    i, S[0], S[n] = i_limit

    (r, S[j]), (S[r], S[i]) = r_relative.of(Indexed - Indexed)

    ((S[w], clip_index), (S[j], S[0], u), S[i_limit]), V_quote = eq_V_quote.of(Equal[Stack[Indexed]])
    S[k], (((S[r], S[Min(j + i, n - 1)]), (S[r], S[i])), S[-k], S[k]) = clip_index.of(Add[clip[Indexed - Indexed]])

    assert n >= 2 and u >= 2 and u <= n

    return Equal(V[i, i:Min(n, i + u)], V_quote[i, :Min(n, i + u) - i])


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n, k = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    V = Symbol(shape=(n, n), real=True)
    V_quote = Symbol(shape=(n, u), real=True)
    r = Symbol(shape=(n,), integer=True)
    w = Symbol(shape=(k * 2 + 1,), integer=True)
    i, j = Symbol(integer=True)
    Eq << apply(
        Equal(V, Stack[j:n, i:n]((w[k + clip(r[j] - r[i], -k, k)]))),
        Equal(V_quote, Stack[j:u, i:n](w[k + clip(r[Min(n - 1, i + j)] - r[i], -k, k)])))

    Eq <<= Eq[0][i]

    Eq <<= Logic.AllIn.of.All.apply(Eq[-1], (i, 0, n), simplify=None)

    Eq << Algebra.All.Eq.Slice.of.All_Eq.apply(Eq[-1], slice(i, Min(n, i + u)))

    Eq << Eq[-1].this.rhs.find(~Indexed - Indexed).args[1].apply(Algebra.Expr.eq.IteGe, upper=n - 1)

    Eq.V_relu = Eq[-1].this(i).rhs(j).find(GreaterEqual).simplify()

    Eq << Eq[1][i]

    Eq << Logic.AllIn.of.All.apply(Eq[-1], (i, 0, n), simplify=None)

    Eq << Algebra.All.Eq.Slice.of.All_Eq.apply(Eq[-1], slice(0, Min(n, u + i) - i))

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq.V_relu, Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-03-30
