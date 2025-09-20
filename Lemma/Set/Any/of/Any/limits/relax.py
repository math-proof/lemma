from util import *


@apply
def apply(given, domain=None, wrt=None):
    function, *limits = given.of(Any)

    if wrt is None:
        i = 0
    else:
        i = given.variables.index(wrt)

    limit = limits[i]

    if domain is None:
        x = limit[0]
        limit = (x,)
    else:
        x, S = limit.coerce_setlimit()
        assert S in domain
        limit = (x, domain)

    limits[i] = limit
    return Any(function, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    S = Symbol(etype=dtype.real)
    e, t = Symbol(real=True)
    f = Function(shape=(), integer=True)
    Eq << apply(Any[e:S - {t}](f(e) > 0), domain=S)

    Eq << Algebra.Any.given.Or.Any.split.apply(Eq[-1], cond={t})

    Eq << Logic.Or.given.Cond.apply(Eq[-1], index=1)





if __name__ == '__main__':
    run()

# created on 2020-09-01
# updated on 2023-10-22
