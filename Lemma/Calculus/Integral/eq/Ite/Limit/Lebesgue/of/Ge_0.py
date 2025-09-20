from util import *


@apply
def apply(is_nonnegative, self, n=None, k=None):
    fx = is_nonnegative.of(Expr >= 0)
    if n is None:
        n = self.generate_var(integer=True, var='n')

    if k is None:
        k = self.generate_var(n, integer=True, var='k')

    S[fx], (x, a, b) = self.of(Integral)
    assert fx.is_integrable(x, a, b)

    return Equal(self, Piecewise((-Sup[x:Interval(b, a)](fx) * Limit[n:oo](Sum[k:n](Measure({Element(x, Interval(b, a)) : fx >= Sup[x:Interval(b, a)](fx) / n * k})) / n), a > b), (Sup[x:Interval(a, b)](fx) * Limit[n:oo](Sum[k:n](Measure({Element(x, Interval(a, b)) : fx >= Sup[x:Interval(a, b)](fx) / n * k})) / n), True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Calculus, Logic

    x, a, b = Symbol(real=True)
    f = Function(real=True, finite=True, integrable=True)
    Eq << apply(f(x) >= 0, Integral[x:a:b](f(x)))

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[1], cond=a > b)

    Eq <<= Eq[-2].this.find(Integral).apply(Calculus.Integral.eq.Ite), Eq[-1].this.find(Integral).apply(Calculus.Integral.eq.Ite)

    Eq <<= Logic.Imp.given.Imp.subst.Bool.apply(Eq[-2]), Logic.Imp.given.Imp.subst.Bool.apply(Eq[-1], invert=True)

    Eq << -Eq[-2].this.rhs

    Eq << Logic.And.Imp.of.Cond.split.apply(Eq[0], cond=a > b)

    Eq <<= Eq[-2].this.rhs.apply(Calculus.Integral.eq.Mul.Limit.Lebesgue.of.Ge_0, Eq[-3].find(Integral)), Eq[-1].this.rhs.apply(Calculus.Integral.eq.Mul.Limit.Lebesgue.of.Ge_0, Eq[-4].find(Integral))


if __name__ == '__main__':
    run()
# created on 2020-05-25
