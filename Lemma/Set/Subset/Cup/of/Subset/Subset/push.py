from util import *


@apply
def apply(*imply):
    from Lemma.Algebra.EqSum.of.Eq.Eq.push import absorb_back
    return absorb_back(Cup, Subset, *imply)


@prove
def prove(Eq):
    from Lemma import Set
    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g, f = Function(etype=dtype.integer)

    Eq << apply(Subset(g(b), f(b)), Subset(Cup[k:a:b](g(k)), Cup[k:a:b](f(k))))

    Eq << Set.Subset.Union.of.Subset.Subset.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()

# created on 2020-08-02
