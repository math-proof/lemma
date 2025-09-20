from util import *


@apply
def apply(eq_cup, subset, eq_V, Q, K):
    cup, m = eq_cup.of(Equal[Card])
    (d, j), j_limit = cup.of(Cup[FiniteSet[Indexed]])
    S[j], S[0], S[m] = j_limit
    n, d_z = Q.shape
    S[cup], (S[0], S[n]) = subset.of(Subset[Expr, Range])


    ((w_V, clip_index), S[j_limit], i_limit), V  = eq_V.of(Equal[Stack[Indexed]])
    i, S[0], S[n] = i_limit
    j, S[0], S[m] = j_limit

    k, (((r, S[d[j]]), (S[r], S[i])), S[-k], S[k]) = clip_index.of(Add[clip[Indexed - Indexed]])

    return Equal(softmax(Q @ K.T + V + (Stack[j:m, i:n](Bool(i < d[j])) - 1) * oo), V)


@prove(proved=False)
def prove(Eq):
    n, k, m = Symbol(integer=True, positive=True)
    r = Symbol(shape=(n,), integer=True)
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(m, d_z), real=True)
    d = Symbol(shape=(oo,), integer=True)
    i, j = Symbol(integer=True)
    w_V = Symbol("w^V", shape=(2 * k + 1, d_z), real=True)
    V = Symbol(real=True, shape=(n, m, d_z))
    s = d[:m].cup_finiteset(j)
    Eq << apply(
        Equal(Card(s), m),
        Subset(s, Range(n)),
        Equal(V, Stack[j:m, i:n](w_V[k + clip(r[d[j]] - r[i], -k, k)])),
        Q, K)




if __name__ == '__main__':
    run()
# created on 2022-04-26

