from util import *


@apply
def apply(eq_k, eq_n, wrt=None):
    eq_k.of(Equal)
    eq_n.of(Equal)

    pattern = eq_k._subs(wrt, Wild('k', **wrt.type.dict))
    res = eq_n.match(pattern)
    n, *_ = res.values()
    domain = wrt.domain
    assert n not in domain
    domain |= n.set

    k = wrt.unbounded

    return All[k:domain](eq_k._subs(wrt, k))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    n = Symbol(integer=True, positive=True)
    f, g = Symbol(integer=True, shape=(oo,))
    k = Symbol(domain=Range(n))
    Eq << apply(Equal(f[k], g[k]), Equal(f[n], g[n]), wrt=k)

    Eq << Algebra.All.given.And.All.apply(Eq[-1], cond={n})

    Eq << Logic.All.of.Cond.apply(Eq[0], k)


if __name__ == '__main__':
    run()
# created on 2019-03-23
