from util import *


@apply
def apply(given, domain=None, wrt=None):
    expr, *limits = given.of(All)

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

    assert domain in S
    limit = (x, domain)

    limits[i] = limit
    return All(expr, *limits)


@prove
def prove(Eq):
    from Lemma import Bool

    S = Symbol(etype=dtype.real, given=True)
    e = Symbol(real=True)
    t = Symbol(real=True, given=True)
    f = Function(shape=(), integer=True)
    Eq << apply(All[e:S](f(e) > 0), domain=S - {t})

    Eq << ~Eq[-1]

    Eq << Bool.Any_And.of.Any.All.All_Imp.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-03-31
