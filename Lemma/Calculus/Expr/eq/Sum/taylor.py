from util import *


@apply
def apply(fx, a, x=None, n=None):
    if n is None:
        n = fx.generate_var(a.free_symbols, integer=True)

    if x is None:
        x = next(iter(fx.free_symbols))
    else:
        assert x in fx.free_symbols

    return Equal(fx, Sum[n:oo]((x - a) ** n / factorial(n) * Subs[x:a](Derivative[x ** n](fx))))


@prove(proved=False)
def prove(Eq):
    x, a = Symbol(real=True)
    f = Function(real=True, differentiable=True)
    n = Symbol(integer=True)
    Eq << apply(f(x), a, n=n)

    # https://en.wikipedia.org/wiki/Taylor_series
    # https://en.wikipedia.org/wiki/Taylor%27s_theorem


if __name__ == '__main__':
    run()

# created on 2021-08-15
