from util import *


@apply
def apply(*imply):
    from Lemma.Algebra.EqSum.of.Eq.Eq.push import absorb_back
    return absorb_back(Product, Less, *imply, criteria=lambda cond: cond.lhs > 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g = Function(integer=True, positive=True)
    f = Function(integer=True)
    Eq << apply((g(b) < f(b)), Product[k:a:b](g(k)) < Product[k:a:b](f(k)))

    Eq << Algebra.LtMul.of.Lt.Lt.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(Algebra.Prod.eq.MulProdS, cond={b})

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.eq.MulProdS, cond={b})


if __name__ == '__main__':
    run()

# created on 2019-09-29
