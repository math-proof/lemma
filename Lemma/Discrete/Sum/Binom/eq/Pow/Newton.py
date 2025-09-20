from util import *


@apply
def apply(self):
    ((n, k), *factors), (S[k], S[0], S[n + 1]) = self.of(Sum[Mul[Binomial]])

    if len(factors) == 2:
        x_pow, y_pow = factors
        x, e_x = x_pow.of(Pow)
        y, e_y = y_pow.of(Pow)
        if e_x == k:
            assert e_y == n - k
        elif e_y == k:
            assert e_x == n - k or x == -1 and e_x == n + k
    else:
        x_pow, = factors
        x, _k = x_pow.of(Pow)
        assert _k == k or _k + k == n
        y = 1

    return Equal(self, (x + y) ** n)


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete

    x, y, k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Sum[k:n + 1](Binomial(n, k) * x ** k * y ** (n - k)))
    Eq << Eq[-1].this.rhs.apply(Discrete.Pow.eq.Sum.Binom.Newton)





if __name__ == '__main__':
    run()
# created on 2021-11-25
