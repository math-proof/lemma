from util import *


@apply
def apply(imply):
    x, S = imply.of(Element)
    expr, *limits = S.of(Cup)

    for v in S.variables:
        if x._has(v):
            _v = v.generate_var(imply.free_symbols, **v.type.dict)
            S = S.limits_subs(v, _v)

    contains = Element(x, S.expr).simplify()
    return Any(contains, *S.limits)


@prove
def prove(Eq):
    from Lemma import Set

    n = Symbol(positive=True, integer=True)
    x, k = Symbol(integer=True)
    A = Symbol(shape=(oo,), etype=dtype.integer)
    Eq << apply(Element(x, Cup[k:n](A[k])))

    i = Symbol(domain=Range(n))
    Eq << Eq[-1].limits_subs(k, i)

    Eq << Subset(A[i], Eq[0].rhs, plausible=True)

    Eq << Eq[-1].this.rhs.apply(Set.Cup.eq.UnionCupS, cond=i.set)

    Eq << Eq[-2].this.expr.apply(Set.In.of.In.Subset, Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-09-28
