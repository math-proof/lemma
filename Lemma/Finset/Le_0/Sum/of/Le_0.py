from util import *


@apply
def apply(given, *limits):
    fx = given.of(Expr <= 0)
    for limit in limits:
        x = limit[0]
        assert fx._has(x)
        assert not x.is_given
        x, domain = Tuple(*limit).coerce_setlimit()
        domain_defined = fx.domain_defined(x)
        assert domain in domain_defined

    return Sum(fx, *limits) <= 0


@prove
def prove(Eq):
    from Lemma import Algebra
    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    h = Symbol(real=True, shape=(n,))
    Eq << apply(h[k] <= 0, (k, 0, n))

    Eq << All[k:n](Eq[0], plausible=True)

    Eq << Eq[-1].simplify()

    Eq << Algebra.LeSum.of.All_Le.apply(Eq[-1])

    Eq << Eq[1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# created on 2019-12-06
