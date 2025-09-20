from util import *


@apply
def apply(given):
    x, S = given.of(Element)
    function, *limits = S.of(Cup)

    for v in S.variables:
        if x._has(v):
            _v = v.generate_var(given.free_symbols, **v.type.dict)
            S = S.limits_subs(v, _v)

    contains = Element(x, S.expr).simplify()
    return Any(contains, *S.limits)


@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(positive=True, integer=True, given=True)
    x = Symbol(integer=True, given=True)
    k = Symbol(integer=True)

    A = Symbol(shape=(oo,), etype=dtype.integer, given=True)

    Eq << apply(Element(x, Cup[k:n](A[k])))

    Eq << ~Eq[1]

    Eq << Set.NotIn_Cup.of.All_NotIn.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2018-09-09
