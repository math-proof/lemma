from util import *


def is_continuous(f, a, b, x=None, xi=None, plausible=None):
    if x is None:
        x = Symbol('x', real=True)

    fx = f(x)
    if xi is None:
        xi = fx.generate_var(var='xi', excludes=a.free_symbols & b.free_symbols, real=True)

    kwargs = {}
    if plausible:
        kwargs['plausible'] = plausible

    return All[xi:Interval(a, b)](Equal(Limit[x:xi](fx), f(xi)), **kwargs)


@apply
def apply(given):
    ((f, (z, xi)), S[f._subs(z, xi)]), (S[xi], domain) = given.of(All[Equal[Limit]])
    assert not xi.infinitesimality
    assert domain.is_Interval
    assert domain.is_closed
    
    y = Symbol(real=True)
    
    return All[y:Interval(Minima[z:domain](f), Maxima[z:domain](f))](Any[z:domain](Equal(f, y)))


@prove(proved=False)
def prove(Eq):
    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval.open(a, oo))
    f = Function(shape=(), real=True)
    Eq << apply(is_continuous(f, a, b))


if __name__ == '__main__':
    run()

# created on 2020-04-19
