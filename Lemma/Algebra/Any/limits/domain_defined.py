from util import *


@apply
def apply(given, wrt=None):
    expr, *limits = given.of(Any)

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
    return Any(expr, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    m, n = Symbol(integer=True, positive=True)
    f = Symbol(real=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(Any[i:Range(m)](f[i] > 0))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Any.of.Any.limits.domain_defined)
    Eq << Eq[-1].this.rhs.apply(Algebra.Any.given.Any.limits.domain_defined)


if __name__ == '__main__':
    run()
# created on 2022-01-08
