from util import *


@apply
def apply(self, n=None, k=None):
    fx, (x, a, b) = self.of(Integral)
    if n is None:
        n = self.generate_var(integer=True, var='n', positive=True)

    if k is None:
        k = self.generate_var(n, integer=True, var='k')
    assert a < b
    assert fx.is_continuous_at(x, a, b)
    return Equal(self, (b - a) * Limit[n:oo](Sum[k:n](Maxima[x:a + (b - a) * k / n:a + (b - a) * (k + 1) / n](fx)) / n))


@prove
def prove(Eq):
    from Lemma import Calculus

    n = Symbol(integer=True, positive=True)
    x, a = Symbol(real=True)
    b = Symbol(domain=Interval.open(a, oo))
    f = Function(real=True, continuous=True)
    Eq << apply(Integral[x:a:b](f(x)))

    Eq << Less(a, b, plausible=True)

    Eq << Calculus.Integral.eq.Mul.Limit.Maxima.Darboux.of.Lt.apply(Eq[-1], Eq[0].lhs, n)





if __name__ == '__main__':
    run()
# created on 2020-06-07
# updated on 2023-03-25
