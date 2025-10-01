from util import *


@apply
def apply(*imply):
    from Lemma.Algebra.EqSum.of.Eq.Eq.push import absorb_back
    return absorb_back(Sum, Less, *imply)


@prove
def prove(Eq):
    from Lemma import Algebra
    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g, f = Function(integer=True)

    Eq << apply((g(b) < f(b)), Sum[k:a:b](g(k)) < Sum[k:a:b](f(k)))

    Eq << Algebra.LtAdd.of.Lt.Lt.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(Algebra.Sum.eq.AddSumS, cond={b})

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.AddSumS, cond={b})


if __name__ == '__main__':
    run()

# created on 2019-09-30
