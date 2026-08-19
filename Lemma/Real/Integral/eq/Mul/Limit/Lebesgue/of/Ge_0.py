from util import *


@apply
def apply(is_nonnegative, self, n=None, k=None):
    fx = is_nonnegative.of(Expr >= 0)
    if n is None:
        n = self.generate_var(integer=True, var='n')

    if k is None:
        k = self.generate_var(n, integer=True, var='k')

    fx, (x, E) = self.of(Integral)
    assert fx.is_integrable(x, E)
    sup = Sup[x:E](fx)
    return Equal(self, sup * Limit[n:oo](Sum[k:n](Measure({Element(x, E) : fx >= sup / n * k})) / n))


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    E = Symbol(etype=dtype.real, measurable=True)
    f = Function(real=True, finite=True, integrable=True)
    Eq << apply(f(x) >= 0, Integral[x:E](f(x)))

    Eq << Equal(*Eq[1]._subs(E, Interval(0, 1))._subs(f(x), x - x ** 2).args, plausible=True)

    Eq << Eq[-1].this.lhs.doit()


if __name__ == '__main__':
    run()
# created on 2020-05-21
