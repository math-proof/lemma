from util import *


@apply
def apply(given, *limits):
    assert given.is_Element

    for limit in limits:
        var, domain = Tuple.coerce_setlimit(limit)
        assert given._has(var)
        assert domain in given.domain_defined(var)

    return Any(given, *limits)


@prove
def prove(Eq):
    from Lemma import Algebra
    n = Symbol(positive=True, integer=True, given=True)
    x = Symbol(integer=True, given=True)
    k = Symbol(integer=True)

    A = Symbol(shape=(oo,), etype=dtype.integer, given=True)

    Eq << apply(Element(x, A[k]), (k, 0, n))

    Eq << ~Eq[-1]

    Eq << Algebra.All.And.of.Cond.All.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-03-02
