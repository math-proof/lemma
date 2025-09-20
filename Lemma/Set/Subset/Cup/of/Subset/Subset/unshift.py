from util import *


@apply
def apply(*imply):
    from Lemma.Algebra.EqSum.of.Eq.Eq.unshift import absorb_front
    return absorb_front(Cup, Subset, *imply)


@prove
def prove(Eq):
    from Lemma import Set
    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g, f = Function(etype=dtype.integer)

    Eq << apply(Subset(g(a - 1), f(a - 1)), Subset(Cup[k:a:b](g(k)), Cup[k:a:b](f(k))))

    Eq << Set.Subset.Union.of.Subset.Subset.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()

# created on 2021-06-29
