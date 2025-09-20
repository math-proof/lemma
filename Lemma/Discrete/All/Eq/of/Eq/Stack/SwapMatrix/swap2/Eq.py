from util import *


@apply
def apply(eq_w):
    (w, i, j), (S[i], S[j]) = eq_w.of(Equal[Indexed, SwapMatrix])
    n = w.shape[-1]
    assert n >= 2
    return All(Equal(w[0, i] @ w[0, j] @ w[0, i], w[i, j]), (j, Range(1, n) - {i}))


@prove
def prove(Eq):
    from Lemma import Discrete

    n = Symbol(domain=Range(2, oo))
    w = Symbol(integer=True, shape=(n, n, n, n))
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(w[i, j], SwapMatrix(n, i, j)))

    w = Eq[0].lhs
    Eq << Discrete.All.Eq.of.Eq.Stack.SwapMatrix.swap2.eq_general.apply(Eq[0])

    w_ti, *_ = Eq[-1].expr.lhs.args
    t, i = w_ti.indices
    Eq << Eq[-1].subs(t, 0)





if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-23
# updated on 2023-05-21
