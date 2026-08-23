from util import *


@apply
def apply(given, wrt=None):
    expr, *limits = given.of(All)

    if wrt is None:
        i = 0
    else:
        i = given.variables.index(wrt)

    limit = limits[i]

    if len(limit) == 1:
        x = limit[0]
        S = x.universalSet
    else:
        x, S = limit.coerce_setlimit()

    domain = expr.domain_defined(x)
    limit = (x, domain & S)
    limits[i] = limit
    return All(expr, *limits)


@prove
def prove(Eq):
    from Lemma import Set

    m, n = Symbol(integer=True, positive=True)
    f = Symbol(real=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(All[i:Range(m)](f[i] > 0))

    Eq << Set.AllIn_SDiff.of.All.apply(Eq[0], domain=Range(Min(n, m)))


if __name__ == '__main__':
    run()
# created on 2022-01-08
