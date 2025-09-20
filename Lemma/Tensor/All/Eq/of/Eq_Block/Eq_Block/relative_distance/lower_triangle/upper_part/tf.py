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

    return All[i:l - 1](Equal(V[i, :i + 1], V_quote[i, :i + 1]))


@prove
def prove(Eq):
    from Lemma import Tensor, Set

    n, k = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    V = Symbol(shape=(n, n), real=True)
    z, V_quote = Symbol(shape=(n, Min(l, n)), real=True)
    r = Symbol(shape=(n,), integer=True)
    w = Symbol(shape=(k * 2 + 1,), integer=True)
    i, j = Symbol(integer=True)
    Eq << apply(
        Equal(V, Stack[j:n, i:n]((w[k + clip(r[j] - r[i], -k, k)]))),
        Equal(V_quote, Stack[j:l, i:n](w[k + clip(r[Min(n - 1, relu(i - l + 1) + j)] - r[i], -k, k)])))

    Eq << Tensor.All.Eq.of.Eq_Block.Eq_Block.relative_distance.lower_triangle.upper_part.apply(Eq[0], Eq[1])

    Eq << Set.AllIn_SDiff.of.All.apply(Eq[-1], Range(l - 1))




if __name__ == '__main__':
    run()
# created on 2022-03-30
