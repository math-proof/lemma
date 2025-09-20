from util import *


@apply
def apply(lt, self, n=None, k=None):
    a, b = lt.of(Less)
    fx, (x, S[a], S[b]) = self.of(Integral)
    if n is None:
        n = self.generate_var(integer=True, var='n')

    if k is None:
        k = self.generate_var(n, integer=True, var='k')
    assert fx.is_continuous_at(x)
    return Equal(self, (b - a) * Limit[n:oo](Sum[k:n](fx._subs(x, a + (b - a) * k / n)) / n))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra, Logic

    x, a, b = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(a < b, Integral[x:a:b](f(x)))

    Eq << Calculus.Integral.eq.Mul.Limit.Maxima.Darboux.of.Lt.apply(Eq[0], Eq[1].lhs)

    Eq << Calculus.Integral.eq.Mul.Limit.Minima.Darboux.of.Lt.apply(Eq[0], Eq[1].lhs)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Gt_0.of.Lt.apply(Eq[0])

    Eq << Algebra.EqDiv.of.Gt_0.Eq.apply(Eq[-1], Eq[-2])

    Eq << Calculus.EqDarboux.of.Lt.Eq_Limit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-05-27
