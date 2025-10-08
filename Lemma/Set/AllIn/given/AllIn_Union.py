from util import *


@apply
def apply(given, limit):
    if isinstance(limit, tuple):
        wrt, *domain = limit
    else:
        domain = limit
        wrt = None

    expr, *limits = given.of(All)
    if isinstance(domain, list):
        if len(domain) == 1:
            domain = domain[0]
        elif len(domain) == 2:
            domain = wrt.range(*domain)

    if wrt is None:
        i = 0
    else:
        i = given.variables.index(wrt)

    limit = limits[i]

    assert domain is not None

    x, S = limit.coerce_setlimit()
    assert S in domain
    limit = (x, domain)

    limits[i] = limit
    return All(expr, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    A, B = Symbol(etype=dtype.real)
    e = Symbol(real=True)
    f = Function(shape=(), integer=True)

    Eq << apply(All[e:A](f(e) > 0), (e, A | B))

    Eq << ~Eq[0]

    Eq << Bool.Any_And.of.Any.All.All_Imp.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-09-29
