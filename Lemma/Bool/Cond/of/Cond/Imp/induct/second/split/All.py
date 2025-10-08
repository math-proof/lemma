from util import *


@apply
def apply(f0, suffice, n=None):
    fk, fn = suffice.of(Imply)

    fk, (k, start, _n) = fk.of(All[Tuple])

    assert k.is_integer
    assert fk._subs(k, _n) == fn
    assert fk._subs(k, start) == f0
    diff = _n - n
    if diff:
        assert not diff._has(n)
        fn = fn._subs(n, n - diff)

    n_domain = fn.domain_defined(n)
    assert n_domain.min() >= start

    return fn


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
    n = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True)
    f, g = Symbol(shape=(oo,), real=True)

    Eq << apply(f[0] > g[0], Imply(All[k:n](f[k] > g[k]), f[n] > g[n]), n=n)

    Eq << Eq[1].this.apply(Bool.Imp.Is.All, wrt=n)

    Eq << Imply(All[k:n](f[k] > g[k]), All[k:n](f[k] > g[k]), plausible=True)

    Eq <<= Eq[-1] & Eq[1]

    Eq << Eq[-1].this.rhs.apply(Algebra.All.of.Cond.All.push)

    Eq << Bool.Cond.of.Cond.All_Imp.apply(Eq[0], Eq[-1], n=n, start=1)

    Eq << Bool.Or_NotIn.of.All.apply(Eq[-1], k, n - 1)

    Eq << Eq[-1].subs(n, n + 1)


if __name__ == '__main__':
    run()
# created on 2019-03-20
