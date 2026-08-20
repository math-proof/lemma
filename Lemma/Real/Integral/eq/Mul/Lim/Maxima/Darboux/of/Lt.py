from util import *


@apply
def apply(lt, self, n=None, k=None):
    a, b = lt.of(Less)
    if n is None:
        n = self.generate_var(integer=True, var='n')

    if k is None:
        k = self.generate_var(n, integer=True, var='k')

    fx, (x, S[a], S[b]) = self.of(Integral)
    assert fx.is_continuous_at(x)
    return Equal(self, (b - a) * Limit[n:oo](Sum[k:n](Maxima[x:a + (b - a) * k / n:a + (b - a) * (k + 1) / n](fx)) / n))


@prove(provable=False)
def prove(Eq):
    x, a, b = Symbol(real=True)
    f = Function(real=True, finite=True, continuous=True)
    n, k = Symbol(integer=True)
    Eq << apply(a < b, Integral[x:a:b](f(x)))


if __name__ == '__main__':
    run()
# created on 2020-05-26
