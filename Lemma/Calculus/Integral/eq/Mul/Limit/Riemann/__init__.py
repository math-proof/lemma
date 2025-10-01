from util import *


@apply
def apply(self, n=None, k=None):
    fx, (x, a, b) = self.of(Integral)
    if n is None:
        n = self.generate_var(integer=True, var='n')

    if k is None:
        k = self.generate_var(n, integer=True, var='k')
    assert fx.is_continuous_at(x)
    return Equal(self, (b - a) * Limit[n:oo](Sum[k:n](fx._subs(x, a + (b - a) * k / n)) / n))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Logic

    x, a, b = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(Integral[x:a:b](f(x)))

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[0], cond=a < b)

    Eq << (a < b).this.apply(Calculus.Integral.eq.Mul.Limit.Maxima.Darboux.of.Lt, Eq[0].lhs)

    Eq << (a < b).this.apply(Calculus.Integral.eq.Mul.Limit.Minima.Darboux.of.Lt, Eq[0].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Logic.Eq.of.Eq.Eq)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Gt_0.of.Lt)

    Eq << Eq[-1].this.rhs.apply(Algebra.EqDiv.of.Gt_0.Eq)

    Eq << Logic.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Calculus.EqDarboux.of.Lt.Eq_Limit)

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[2], cond=a > b)

    Eq <<= Eq[-2].this.apply(Logic.Imp.flatten), Eq[-1].this.apply(Logic.Imp.flatten)

    Eq << Eq[-2].this.lhs.apply(Calculus.Integral.eq.Limit.Riemann.of.Gt, Eq[0].lhs)

    Eq << Logic.Imp.given.ImpEq.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-08
from . import of
