from util import *


@apply
def apply(given, domain=None, wrt=None):
    function, *limits = given.of(Any)
    if isinstance(domain, tuple):
        wrt, *domain = domain
        if len(domain) == 1:
            domain = domain[0]

    if wrt is None:
        i = 0
    else:
        try:
            i = given.variables.index(wrt)
        except ValueError:
            limits.append((wrt,))
            i = -1

    limit = limits[i]

    if len(limit) == 1:
        x = limit[0]
        S = x.universalSet
    else:
        x, S = limit.coerce_setlimit()

    assert S in domain
    limit = (x, domain)

    limits[i] = limit
    return Any(function, *limits)

@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, b = Symbol(real=True, given=True)
    x, z = Symbol(real=True)
    f = Function(shape=(), integer=True)
    Eq << apply(Any[x:Interval(a, b, right_open=True)](f(x) > 0), domain=Interval(a, b))

    Eq << ~Eq[-1]

    Eq << Logic.Any_And.of.Any.All.All_Imp.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

# created on 2019-02-17
from . import subst
