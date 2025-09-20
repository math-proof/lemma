from util import *


@apply
def apply(self, var=None):
    (nk, (n, k), fx), (S[k], S[0], S[n + 1]) = self.of(Sum[(-1) ** Add * Binomial * Expr])
    _n, _k = nk

    assert {_n, _k, -_n, -_k} == {n, k, -n, -k}
    for x in fx.free_symbols:
        if x == k:
            continue

        y = fx._subs(x, x - k)
        if not y._has(k):
            break
    else:
        return

    if x.is_given:
        t = y.generate_var(integer=True, var=var)
        y = y._subs(x, t)
        x = t

    return Equal(self, Difference(y, (x, n)))


@prove
def prove(Eq):
    from Lemma import Discrete

    n = Symbol(integer=True, positive=True)
    k, x = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[k:n + 1]((-1) ** (n - k) * Binomial(n, k) * f(x + k)))

    Eq << Eq[0].this.rhs.apply(Discrete.Diff.eq.Sum.Binom)





if __name__ == '__main__':
    run()
# created on 2021-11-26
